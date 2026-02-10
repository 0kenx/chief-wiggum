---------------------------- MODULE Orchestrator -----------------------------
(*
 * TLA+ formal model of Chief Wiggum's multi-worker orchestrator.
 *
 * Models concurrent workers with inlined lifecycle transitions, shared
 * kanban board, worker pool capacity enforcement, and file conflict
 * detection.
 *
 * Models concurrent workers with 11 lifecycle states (including merge_conflict
 * and needs_multi_resolve routing) while preserving the key safety properties:
 *   - Worker pool capacity limits (main workers, priority workers)
 *   - No duplicate workers per task
 *   - Kanban consistency with worker state
 *   - Bounded merge/recovery counters
 *   - File conflict prevention
 *   - Dependency ordering
 *
 * Designed for Apalache symbolic model checking (type annotations, CInit).
 *)

EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Set(Str);
    Tasks,
    \* @type: Int;
    MaxWorkers,
    \* @type: Int;
    FixWorkerLimit,
    \* @type: Int;
    MaxMergeAttempts,
    \* @type: Int;
    MaxRecoveryAttempts,
    \* @type: Str -> Set(Str);
    TaskFiles,         \* function: task -> set of files it touches
    \* @type: Str -> Set(Str);
    TaskDeps           \* function: task -> set of prerequisite task IDs

VARIABLES
    \* @type: Str -> Str;
    kanban,            \* task -> kanban status: " ", "=", "x", "*"
    \* @type: Str -> Str;
    wState,            \* task -> worker state (simplified lifecycle)
    \* @type: Str -> Str;
    wType,             \* task -> worker type: "none", "main", "fix", "resolve"
    \* @type: Str -> Int;
    mergeAttempts,     \* task -> merge attempt counter
    \* @type: Str -> Int;
    recoveryAttempts   \* task -> recovery attempt counter

\* @type: <<Str -> Str, Str -> Str, Str -> Str, Str -> Int, Str -> Int>>;
vars == <<kanban, wState, wType, mergeAttempts, recoveryAttempts>>

\* =========================================================================
\* State and type definitions
\* =========================================================================

WorkerStates == {
    "idle", "needs_fix", "fixing", "needs_merge", "merging",
    "merge_conflict", "needs_resolve", "needs_multi_resolve",
    "resolving", "merged", "failed"
}

KanbanValues == {" ", "=", "x", "*"}

WorkerTypes == {"none", "main", "fix", "resolve"}

\* =========================================================================
\* Derived sets
\* =========================================================================

\* Active main workers (spawned, not terminal/idle)
\* NOTE: Bound variable 'w' avoids shadowing operator parameter 't' --
\* Apalache's SubstRule cannot resolve substitutions through shadowed bindings.
ActiveMain == {w \in Tasks : wType[w] = "main" /\ wState[w] \notin {"idle", "merged", "failed"}}

\* Active priority workers (fix/resolve)
ActivePriority == {w \in Tasks : wType[w] \in {"fix", "resolve"} /\ wState[w] \notin {"idle", "merged", "failed"}}

\* Tasks whose dependencies are all completed
DepsCompleted(q) == \A d \in TaskDeps[q] : kanban[d] = "x"

\* Ready tasks: pending in kanban, idle worker state, deps met
ReadyTasks == {w \in Tasks : kanban[w] = " " /\ wState[w] = "idle" /\ DepsCompleted(w)}

\* File conflict: task q shares files with an active main worker
HasFileConflict(q) == \E w \in ActiveMain : w /= q /\ TaskFiles[q] \cap TaskFiles[w] /= {}

\* =========================================================================
\* Init and CInit
\* =========================================================================

Init ==
    /\ kanban = [u \in Tasks |-> " "]
    /\ wState = [u \in Tasks |-> "idle"]
    /\ wType = [u \in Tasks |-> "none"]
    /\ mergeAttempts = [u \in Tasks |-> 0]
    /\ recoveryAttempts = [u \in Tasks |-> 0]

\* Apalache constant initialization
\* 3 tasks: T1 uses {f1}, T2 uses {f2}, T3 uses {f1, f3}
\* T3 depends on T1 (exercises dependency ordering + file conflict)
CInit ==
    /\ Tasks = {"T1", "T2", "T3"}
    /\ MaxWorkers = 2
    /\ FixWorkerLimit = 1
    /\ MaxMergeAttempts = 2
    /\ MaxRecoveryAttempts = 1
    /\ TaskFiles = [u \in {"T1", "T2", "T3"} |->
        CASE u = "T1" -> {"f1"}
          [] u = "T2" -> {"f2"}
          [] u = "T3" -> {"f1", "f3"}]
    /\ TaskDeps = [u \in {"T1", "T2", "T3"} |->
        CASE u = "T1" -> {}
          [] u = "T2" -> {}
          [] u = "T3" -> {"T1"}]

\* =========================================================================
\* Actions - Spawn Main Worker
\* =========================================================================

\* Pick a ready task, check capacity and no file conflict, spawn
SpawnMainWorker(t) ==
    /\ t \in ReadyTasks
    /\ Cardinality(ActiveMain) < MaxWorkers
    /\ ~HasFileConflict(t)
    /\ kanban' = [kanban EXCEPT ![t] = "="]
    /\ wState' = [wState EXCEPT ![t] = "needs_merge"]
    /\ wType' = [wType EXCEPT ![t] = "main"]
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* =========================================================================
\* Actions - Merge Cycle
\* =========================================================================

\* Worker starts merge (guarded: merge_attempts < max)
WorkerMergeStart(t) ==
    /\ wState[t] = "needs_merge"
    /\ mergeAttempts[t] < MaxMergeAttempts
    /\ wState' = [wState EXCEPT ![t] = "merging"]
    /\ mergeAttempts' = [mergeAttempts EXCEPT ![t] = mergeAttempts[t] + 1]
    /\ UNCHANGED <<kanban, wType, recoveryAttempts>>

\* Worker starts merge (fallback: max exceeded -> failed)
WorkerMergeStartFallback(t) ==
    /\ wState[t] = "needs_merge"
    /\ mergeAttempts[t] >= MaxMergeAttempts
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ kanban' = [kanban EXCEPT ![t] =
        IF recoveryAttempts[t] >= MaxRecoveryAttempts THEN "*" ELSE kanban[t]]
    /\ UNCHANGED <<wType, mergeAttempts, recoveryAttempts>>

\* Merge succeeded
MergeSucceeded(t) ==
    /\ wState[t] = "merging"
    /\ wState' = [wState EXCEPT ![t] = "merged"]
    /\ kanban' = [kanban EXCEPT ![t] = "x"]
    /\ wType' = [wType EXCEPT ![t] = "none"]
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* Merge conflict detected: merging -> merge_conflict (pure state transition)
MergeConflictDetected(t) ==
    /\ wState[t] = "merging"
    /\ wState' = [wState EXCEPT ![t] = "merge_conflict"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>

\* Conflict routed to single-PR resolve (guarded: merge_attempts < max)
ConflictToResolve(t) ==
    /\ wState[t] = "merge_conflict"
    /\ mergeAttempts[t] < MaxMergeAttempts
    /\ wState' = [wState EXCEPT ![t] = "needs_resolve"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>

\* Conflict routed to multi-PR resolve (guarded: merge_attempts < max)
ConflictToMultiResolve(t) ==
    /\ wState[t] = "merge_conflict"
    /\ mergeAttempts[t] < MaxMergeAttempts
    /\ wState' = [wState EXCEPT ![t] = "needs_multi_resolve"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>

\* Conflict fallback: merge_conflict -> failed (attempts exhausted)
ConflictToFailed(t) ==
    /\ wState[t] = "merge_conflict"
    /\ mergeAttempts[t] >= MaxMergeAttempts
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ kanban' = [kanban EXCEPT ![t] =
        IF recoveryAttempts[t] >= MaxRecoveryAttempts THEN "*" ELSE kanban[t]]
    /\ UNCHANGED <<wType, mergeAttempts, recoveryAttempts>>

\* Merge out of date: nondeterministic rebase outcome
MergeOutOfDateOk(t) ==
    /\ wState[t] = "merging"
    /\ wState' = [wState EXCEPT ![t] = "needs_merge"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>

MergeOutOfDateFail(t) ==
    /\ wState[t] = "merging"
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ kanban' = [kanban EXCEPT ![t] =
        IF recoveryAttempts[t] >= MaxRecoveryAttempts THEN "*" ELSE kanban[t]]
    /\ UNCHANGED <<wType, mergeAttempts, recoveryAttempts>>

\* Merge hard fail
MergeHardFail(t) ==
    /\ wState[t] = "merging"
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ kanban' = [kanban EXCEPT ![t] =
        IF recoveryAttempts[t] >= MaxRecoveryAttempts THEN "*" ELSE kanban[t]]
    /\ UNCHANGED <<wType, mergeAttempts, recoveryAttempts>>

\* =========================================================================
\* Actions - Fix Cycle (PR comments event)
\* =========================================================================

\* Spawn fix worker: PR comments / fix detected on an active task
SpawnFixWorker(t) ==
    /\ wState[t] = "needs_merge"
    /\ Cardinality(ActivePriority) < FixWorkerLimit
    /\ wState' = [wState EXCEPT ![t] = "needs_fix"]
    /\ wType' = [wType EXCEPT ![t] = "fix"]
    /\ UNCHANGED <<kanban, mergeAttempts, recoveryAttempts>>

\* Spawn fix worker from failed: recovery via fix (guarded by recovery attempts)
SpawnFixWorkerFromFailed(t) ==
    /\ wState[t] = "failed"
    /\ recoveryAttempts[t] < MaxRecoveryAttempts
    /\ Cardinality(ActivePriority) < FixWorkerLimit
    /\ wState' = [wState EXCEPT ![t] = "needs_fix"]
    /\ wType' = [wType EXCEPT ![t] = "fix"]
    /\ kanban' = [kanban EXCEPT ![t] = "="]
    /\ recoveryAttempts' = [recoveryAttempts EXCEPT ![t] = recoveryAttempts[t] + 1]
    /\ UNCHANGED <<mergeAttempts>>

\* Fix started: needs_fix -> fixing
FixStarted(t) ==
    /\ wState[t] = "needs_fix"
    /\ wState' = [wState EXCEPT ![t] = "fixing"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>

\* Fix pass: fixing -> needs_merge (guarded: merge_attempts < max)
\* Worker retains its current wType (fix) through the merge cycle.
\* wType is only set to "none" on terminal transitions (MergeSucceeded, etc.)
FixPassGuarded(t) ==
    /\ wState[t] = "fixing"
    /\ mergeAttempts[t] < MaxMergeAttempts
    /\ wState' = [wState EXCEPT ![t] = "needs_merge"]
    /\ mergeAttempts' = [mergeAttempts EXCEPT ![t] = mergeAttempts[t] + 1]
    /\ UNCHANGED <<kanban, wType, recoveryAttempts>>

\* Fix pass fallback: fixing -> failed (merge budget exhausted)
FixPassFallback(t) ==
    /\ wState[t] = "fixing"
    /\ mergeAttempts[t] >= MaxMergeAttempts
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ kanban' = [kanban EXCEPT ![t] =
        IF recoveryAttempts[t] >= MaxRecoveryAttempts THEN "*" ELSE kanban[t]]
    /\ UNCHANGED <<wType, mergeAttempts, recoveryAttempts>>

\* Fix fail: fixing -> failed
FixFail(t) ==
    /\ wState[t] = "fixing"
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ kanban' = [kanban EXCEPT ![t] =
        IF recoveryAttempts[t] >= MaxRecoveryAttempts THEN "*" ELSE kanban[t]]
    /\ UNCHANGED <<wType, mergeAttempts, recoveryAttempts>>

\* Fix partial: fixing -> needs_fix (retry)
FixPartial(t) ==
    /\ wState[t] = "fixing"
    /\ wState' = [wState EXCEPT ![t] = "needs_fix"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>

\* =========================================================================
\* Actions - Resolve Cycle
\* =========================================================================

\* Resolve started: needs_resolve -> resolving
ResolveStarted(t) ==
    /\ wState[t] = "needs_resolve"
    /\ wState' = [wState EXCEPT ![t] = "resolving"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>

\* Resolve succeeded: resolving -> needs_merge (chain through resolved)
ResolveSucceeded(t) ==
    /\ wState[t] = "resolving"
    /\ wState' = [wState EXCEPT ![t] = "needs_merge"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>

\* Resolve fail: resolving -> failed
ResolveFail(t) ==
    /\ wState[t] = "resolving"
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ kanban' = [kanban EXCEPT ![t] =
        IF recoveryAttempts[t] >= MaxRecoveryAttempts THEN "*" ELSE kanban[t]]
    /\ UNCHANGED <<wType, mergeAttempts, recoveryAttempts>>

\* Resolve timeout: resolving -> needs_resolve
ResolveTimeout(t) ==
    /\ wState[t] = "resolving"
    /\ wState' = [wState EXCEPT ![t] = "needs_resolve"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>

\* =========================================================================
\* Actions - Multi-Resolve Cycle
\* =========================================================================

\* Resolve started from multi-resolve: needs_multi_resolve -> resolving
ResolveStartedFromMulti(t) ==
    /\ wState[t] = "needs_multi_resolve"
    /\ wState' = [wState EXCEPT ![t] = "resolving"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>

\* Multi-resolve batch failed: needs_multi_resolve -> needs_resolve (fallback to single-PR)
ResolveBatchFailed(t) ==
    /\ wState[t] = "needs_multi_resolve"
    /\ wState' = [wState EXCEPT ![t] = "needs_resolve"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>

\* =========================================================================
\* Actions - Recovery
\* =========================================================================

\* Recovery from failed (guarded: recovery_attempts < max)
\* Reset wType to "main" -- recovered worker re-enters merge cycle
Recovery(t) ==
    /\ wState[t] = "failed"
    /\ recoveryAttempts[t] < MaxRecoveryAttempts
    /\ wState' = [wState EXCEPT ![t] = "needs_merge"]
    /\ recoveryAttempts' = [recoveryAttempts EXCEPT ![t] = recoveryAttempts[t] + 1]
    /\ mergeAttempts' = [mergeAttempts EXCEPT ![t] = 0]
    /\ kanban' = [kanban EXCEPT ![t] = "="]
    /\ wType' = [wType EXCEPT ![t] = "main"]

\* Recovery fallback: failed -> permanent failure
RecoveryFallback(t) ==
    /\ wState[t] = "failed"
    /\ recoveryAttempts[t] >= MaxRecoveryAttempts
    /\ kanban' = [kanban EXCEPT ![t] = "*"]
    /\ UNCHANGED <<wState, wType, mergeAttempts, recoveryAttempts>>

\* =========================================================================
\* Actions - External Events
\* =========================================================================

\* External PR merged: any non-idle/non-merged -> merged (wildcard)
ExternalPrMerged(t) ==
    /\ wState[t] \notin {"idle", "merged"}
    /\ wState' = [wState EXCEPT ![t] = "merged"]
    /\ kanban' = [kanban EXCEPT ![t] = "x"]
    /\ wType' = [wType EXCEPT ![t] = "none"]
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* =========================================================================
\* Actions - Startup Reset
\* =========================================================================

\* Reset running states back to waiting counterparts on orchestrator restart.
\* Each running state gets its own action to avoid partial UNCHANGED issues.
StartupResetFixing(t) ==
    /\ wState[t] = "fixing"
    /\ wState' = [wState EXCEPT ![t] = "needs_fix"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>

StartupResetMerging(t) ==
    /\ wState[t] = "merging"
    /\ wState' = [wState EXCEPT ![t] = "needs_merge"]
    /\ mergeAttempts' = [mergeAttempts EXCEPT ![t] = 0]
    /\ UNCHANGED <<kanban, wType, recoveryAttempts>>

StartupResetResolving(t) ==
    /\ wState[t] = "resolving"
    /\ wState' = [wState EXCEPT ![t] = "needs_resolve"]
    /\ mergeAttempts' = [mergeAttempts EXCEPT ![t] = 0]
    /\ UNCHANGED <<kanban, wType, recoveryAttempts>>

\* =========================================================================
\* Next-state relation
\* =========================================================================

Next ==
    \E t \in Tasks :
        \* Spawn
        \/ SpawnMainWorker(t)
        \* Merge cycle
        \/ WorkerMergeStart(t)
        \/ WorkerMergeStartFallback(t)
        \/ MergeSucceeded(t)
        \/ MergeConflictDetected(t)
        \/ ConflictToResolve(t)
        \/ ConflictToMultiResolve(t)
        \/ ConflictToFailed(t)
        \/ MergeOutOfDateOk(t)
        \/ MergeOutOfDateFail(t)
        \/ MergeHardFail(t)
        \* Fix cycle
        \/ SpawnFixWorker(t)
        \/ SpawnFixWorkerFromFailed(t)
        \/ FixStarted(t)
        \/ FixPassGuarded(t)
        \/ FixPassFallback(t)
        \/ FixFail(t)
        \/ FixPartial(t)
        \* Resolve cycle
        \/ ResolveStarted(t)
        \/ ResolveSucceeded(t)
        \/ ResolveFail(t)
        \/ ResolveTimeout(t)
        \* Multi-resolve cycle
        \/ ResolveStartedFromMulti(t)
        \/ ResolveBatchFailed(t)
        \* Recovery
        \/ Recovery(t)
        \/ RecoveryFallback(t)
        \* External events
        \/ ExternalPrMerged(t)
        \* Startup reset
        \/ StartupResetFixing(t)
        \/ StartupResetMerging(t)
        \/ StartupResetResolving(t)

\* =========================================================================
\* Fairness
\* =========================================================================

\* NOTE: Fairness uses 'q' (not 't') as its quantifier variable to avoid
\* Apalache SubstRule collisions with Next (\E t).
\*
\* NOTE: Apalache --temporal does not enforce fairness ("Handling fairness
\* is not supported yet!"). Temporal properties require TLC for verification.
\* Fairness and Spec are kept for documentation and TLC compatibility.
Fairness ==
    /\ \A q \in Tasks :
        /\ WF_vars(SpawnMainWorker(q))
        /\ WF_vars(WorkerMergeStart(q) \/ WorkerMergeStartFallback(q))
        /\ WF_vars(MergeSucceeded(q) \/ MergeHardFail(q)
                   \/ MergeConflictDetected(q)
                   \/ MergeOutOfDateOk(q) \/ MergeOutOfDateFail(q))
        /\ WF_vars(ConflictToResolve(q) \/ ConflictToMultiResolve(q) \/ ConflictToFailed(q))
        /\ WF_vars(SpawnFixWorkerFromFailed(q))
        /\ WF_vars(FixStarted(q))
        /\ WF_vars(FixPassGuarded(q) \/ FixPassFallback(q) \/ FixFail(q))
        /\ WF_vars(ResolveStarted(q))
        /\ WF_vars(ResolveStartedFromMulti(q))
        /\ WF_vars(ResolveSucceeded(q) \/ ResolveFail(q))
        /\ WF_vars(Recovery(q) \/ RecoveryFallback(q))

Spec == Init /\ [][Next]_vars /\ Fairness

\* =========================================================================
\* Safety Invariants
\* =========================================================================

\* TypeInvariant: all per-task variables within declared domains
TypeInvariant ==
    /\ \A t \in Tasks : kanban[t] \in KanbanValues
    /\ \A t \in Tasks : wState[t] \in WorkerStates
    /\ \A t \in Tasks : wType[t] \in WorkerTypes
    /\ \A t \in Tasks : mergeAttempts[t] \in 0..(MaxMergeAttempts + 1)
    /\ \A t \in Tasks : recoveryAttempts[t] \in 0..(MaxRecoveryAttempts + 1)

\* WorkerPoolCapacity: main and priority workers within limits
WorkerPoolCapacity ==
    /\ Cardinality(ActiveMain) <= MaxWorkers
    /\ Cardinality(ActivePriority) <= FixWorkerLimit

\* BoundedCounters: merge/recovery within limits per task
BoundedCounters ==
    /\ \A t \in Tasks : mergeAttempts[t] <= MaxMergeAttempts + 1
    /\ \A t \in Tasks : recoveryAttempts[t] <= MaxRecoveryAttempts + 1

\* KanbanMergedConsistency: kanban "x" iff worker state is "merged"
KanbanMergedConsistency ==
    \A t \in Tasks : kanban[t] = "x" <=> wState[t] = "merged"

\* NoIdleInProgress: in-progress kanban implies worker is not idle
NoIdleInProgress ==
    \A t \in Tasks : kanban[t] = "=" => wState[t] /= "idle"

\* NoFileConflictActive: no two active main workers share files
NoFileConflictActive ==
    \A t1, t2 \in ActiveMain :
        t1 /= t2 => TaskFiles[t1] \cap TaskFiles[t2] = {}

\* DependencyOrdering: a task can only leave idle if deps are completed
DependencyOrdering ==
    \A t \in Tasks :
        wState[t] \notin {"idle", "merged", "failed"} => DepsCompleted(t)

\* NoDuplicateWorkers: no task has workers of multiple types active
\* (a task can only be in one worker type at a time)
NoDuplicateActiveWorkers ==
    \A t \in Tasks :
        wType[t] /= "none" => wState[t] /= "idle"

\* =========================================================================
\* Liveness Properties (require fairness)
\* =========================================================================

\* NOTE: Temporal properties are manually unrolled for CInit's concrete tasks
\* because Apalache's temporal loop-detection rewriting cannot handle \A-quantified
\* temporal formulas (SubstRule fails to assign the copied bound variable).
\* Semantically equivalent to: \A t \in Tasks : wState[t] /= "idle" ~> ...

\* EventualTermination: every spawned worker eventually reaches merged or failed
EventualTermination ==
    /\ wState["T1"] /= "idle" ~> wState["T1"] \in {"merged", "failed"}
    /\ wState["T2"] /= "idle" ~> wState["T2"] \in {"merged", "failed"}
    /\ wState["T3"] /= "idle" ~> wState["T3"] \in {"merged", "failed"}

\* NoStarvation: ready tasks eventually get a worker (or deps become unsat)
NoStarvation ==
    /\ (kanban["T1"] = " " /\ DepsCompleted("T1")) ~> (wState["T1"] /= "idle" \/ ~DepsCompleted("T1"))
    /\ (kanban["T2"] = " " /\ DepsCompleted("T2")) ~> (wState["T2"] /= "idle" \/ ~DepsCompleted("T2"))
    /\ (kanban["T3"] = " " /\ DepsCompleted("T3")) ~> (wState["T3"] /= "idle" \/ ~DepsCompleted("T3"))

=============================================================================
