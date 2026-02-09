---------------------------- MODULE Orchestrator -----------------------------
(*
 * TLA+ formal model of Chief Wiggum's multi-worker orchestrator.
 *
 * Models concurrent workers with inlined lifecycle transitions, shared
 * kanban board, worker pool capacity enforcement, and file conflict
 * detection.
 *
 * Simplifies the full lifecycle to 9 states (dropping transient states and
 * multi_resolve for tractability) while preserving the key safety properties:
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
    "needs_resolve", "resolving", "merged", "failed"
}

KanbanValues == {" ", "=", "x", "*"}

WorkerTypes == {"none", "main", "fix", "resolve"}

\* =========================================================================
\* Derived sets
\* =========================================================================

\* Active main workers (spawned, not terminal/idle)
ActiveMain == {t \in Tasks : wType[t] = "main" /\ wState[t] \notin {"idle", "merged", "failed"}}

\* Active priority workers (fix/resolve)
ActivePriority == {t \in Tasks : wType[t] \in {"fix", "resolve"} /\ wState[t] \notin {"idle", "merged", "failed"}}

\* Tasks whose dependencies are all completed
DepsCompleted(t) == \A d \in TaskDeps[t] : kanban[d] = "x"

\* Ready tasks: pending in kanban, idle worker state, deps met
ReadyTasks == {t \in Tasks : kanban[t] = " " /\ wState[t] = "idle" /\ DepsCompleted(t)}

\* File conflict: task t shares files with an active main worker
HasFileConflict(t) == \E w \in ActiveMain : w /= t /\ TaskFiles[t] \cap TaskFiles[w] /= {}

\* =========================================================================
\* Init and CInit
\* =========================================================================

Init ==
    /\ kanban = [t \in Tasks |-> " "]
    /\ wState = [t \in Tasks |-> "idle"]
    /\ wType = [t \in Tasks |-> "none"]
    /\ mergeAttempts = [t \in Tasks |-> 0]
    /\ recoveryAttempts = [t \in Tasks |-> 0]

\* Apalache constant initialization
\* 3 tasks: T1 uses {f1}, T2 uses {f2}, T3 uses {f1, f3}
\* T3 depends on T1 (exercises dependency ordering + file conflict)
CInit ==
    /\ Tasks = {"T1", "T2", "T3"}
    /\ MaxWorkers = 2
    /\ FixWorkerLimit = 1
    /\ MaxMergeAttempts = 2
    /\ MaxRecoveryAttempts = 1
    /\ TaskFiles = [t \in {"T1", "T2", "T3"} |->
        CASE t = "T1" -> {"f1"}
          [] t = "T2" -> {"f2"}
          [] t = "T3" -> {"f1", "f3"}]
    /\ TaskDeps = [t \in {"T1", "T2", "T3"} |->
        CASE t = "T1" -> {}
          [] t = "T2" -> {}
          [] t = "T3" -> {"T1"}]

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

\* Merge conflict: merging -> needs_resolve (guarded: merge_attempts < max)
\* Collapses merging -> merge_conflict -> needs_resolve atomically,
\* preserving the guard from conflict.needs_resolve
MergeConflictGuarded(t) ==
    /\ wState[t] = "merging"
    /\ mergeAttempts[t] < MaxMergeAttempts
    /\ wState' = [wState EXCEPT ![t] = "needs_resolve"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>

\* Merge conflict: merging -> failed (fallback: merge_attempts exhausted)
MergeConflictFallback(t) ==
    /\ wState[t] = "merging"
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

\* Spawn fix worker: PR comments detected on a needs_merge or none task
SpawnFixWorker(t) ==
    /\ wState[t] \in {"none", "needs_merge"}
    /\ Cardinality(ActivePriority) < FixWorkerLimit
    /\ wState' = [wState EXCEPT ![t] = "needs_fix"]
    /\ wType' = [wType EXCEPT ![t] = "fix"]
    /\ UNCHANGED <<kanban, mergeAttempts, recoveryAttempts>>

\* Fix started: needs_fix -> fixing
FixStarted(t) ==
    /\ wState[t] = "needs_fix"
    /\ wState' = [wState EXCEPT ![t] = "fixing"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>

\* Fix pass: fixing -> needs_merge (chain through fix_completed)
FixPass(t) ==
    /\ wState[t] = "fixing"
    /\ wState' = [wState EXCEPT ![t] = "needs_merge"]
    /\ mergeAttempts' = [mergeAttempts EXCEPT ![t] = mergeAttempts[t] + 1]
    /\ UNCHANGED <<kanban, wType, recoveryAttempts>>

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
\* Actions - Recovery
\* =========================================================================

\* Recovery from failed (guarded: recovery_attempts < max)
Recovery(t) ==
    /\ wState[t] = "failed"
    /\ recoveryAttempts[t] < MaxRecoveryAttempts
    /\ wState' = [wState EXCEPT ![t] = "needs_merge"]
    /\ recoveryAttempts' = [recoveryAttempts EXCEPT ![t] = recoveryAttempts[t] + 1]
    /\ mergeAttempts' = [mergeAttempts EXCEPT ![t] = 0]
    /\ kanban' = [kanban EXCEPT ![t] = "="]
    /\ UNCHANGED wType

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
        \/ MergeConflictGuarded(t)
        \/ MergeConflictFallback(t)
        \/ MergeOutOfDateOk(t)
        \/ MergeOutOfDateFail(t)
        \/ MergeHardFail(t)
        \* Fix cycle
        \/ SpawnFixWorker(t)
        \/ FixStarted(t)
        \/ FixPass(t)
        \/ FixFail(t)
        \/ FixPartial(t)
        \* Resolve cycle
        \/ ResolveStarted(t)
        \/ ResolveSucceeded(t)
        \/ ResolveFail(t)
        \/ ResolveTimeout(t)
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

Fairness ==
    /\ \A t \in Tasks :
        /\ WF_vars(SpawnMainWorker(t))
        /\ WF_vars(WorkerMergeStart(t) \/ WorkerMergeStartFallback(t))
        /\ WF_vars(MergeSucceeded(t) \/ MergeHardFail(t)
                   \/ MergeConflictGuarded(t) \/ MergeConflictFallback(t)
                   \/ MergeOutOfDateOk(t) \/ MergeOutOfDateFail(t))
        /\ WF_vars(FixStarted(t))
        /\ WF_vars(FixPass(t) \/ FixFail(t))
        /\ WF_vars(ResolveStarted(t))
        /\ WF_vars(ResolveSucceeded(t) \/ ResolveFail(t))
        /\ WF_vars(Recovery(t) \/ RecoveryFallback(t))

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
        wState[t] /= "idle" => DepsCompleted(t)

\* NoDuplicateWorkers: no task has workers of multiple types active
\* (a task can only be in one worker type at a time)
NoDuplicateActiveWorkers ==
    \A t \in Tasks :
        wType[t] /= "none" => wState[t] /= "idle"

\* =========================================================================
\* Liveness Properties (require fairness)
\* =========================================================================

\* EventualTermination: every spawned worker eventually reaches merged or failed
EventualTermination ==
    \A t \in Tasks :
        wState[t] /= "idle" ~> wState[t] \in {"merged", "failed"}

\* NoStarvation: ready tasks eventually get a worker (or deps become unsat)
NoStarvation ==
    \A t \in Tasks :
        (kanban[t] = " " /\ DepsCompleted(t)) ~> (wState[t] /= "idle" \/ ~DepsCompleted(t))

=============================================================================
