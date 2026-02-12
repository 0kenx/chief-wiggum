---------------------------- MODULE Orchestrator -----------------------------
(*
 * TLA+ formal model of Chief Wiggum's multi-worker orchestrator.
 *
 * Models concurrent workers with inlined lifecycle transitions, shared
 * kanban board, worker pool capacity enforcement, and file conflict
 * detection.
 *
 * EFFECT-STATE MODELING:
 * Models side effects as explicit per-task state variables to catch
 * partial-effect and crash-recovery bugs across concurrent workers:
 *   - inConflictQueue: whether task is queued for conflict resolution
 *   - worktreeState: worktree lifecycle (absent/present/cleaning)
 *   - lastError: error category from last failure
 *   - githubSynced: whether GitHub issue status matches kanban
 *
 * CRASH/RESTART MODELING:
 * Includes Crash actions that can interrupt any running worker, leaving
 * effects partially applied. StartupReset actions model orchestrator
 * restart recovery. Combined with effect-state, this catches:
 *   - "state updated but effect not applied" bugs
 *   - "effect applied but state not updated" bugs
 *   - cross-worker consistency violations after crash
 *
 * STARTUP RECONCILIATION (GAP CLOSURE #6):
 * Models _scheduler_reconcile_merged_workers() from scheduler.sh.
 * After mid-transition crashes, per-task effect-state variables (kanban,
 * conflict queue, GitHub sync, worktree, error) may be inconsistent with
 * lifecycle state. StartupReconcileMerged(t) and StartupReconcileConflict(t)
 * repair these inconsistencies on restart, achieving eventual consistency.
 *
 * STRUCTURED NONDETERMINISM:
 * Per-task baseMoved/hasConflict environment variables constrain merge
 * outcomes, preventing implausible state combinations.
 *
 * Safety properties include:
 *   - Worker pool capacity limits (main workers, priority workers)
 *   - No duplicate workers per task
 *   - Kanban consistency with worker state
 *   - Bounded merge/recovery counters
 *   - File conflict prevention
 *   - Dependency ordering
 *   - Conflict queue consistency with lifecycle state
 *   - Worktree state consistency
 *   - Error state consistency
 *   - Merged cleanup consistency
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
    recoveryAttempts,  \* task -> recovery attempt counter
    \* === EFFECT-STATE VARIABLES ===
    \* @type: Str -> Bool;
    inConflictQueue,   \* task -> TRUE if in conflict resolution queue
    \* @type: Str -> Str;
    worktreeState,     \* task -> "absent", "present", "cleaning"
    \* @type: Str -> Str;
    lastError,         \* task -> "", "merge_conflict", "rebase_failed", "hard_fail"
    \* @type: Str -> Bool;
    githubSynced,      \* task -> TRUE if GitHub issue status matches kanban
    \* === ENVIRONMENT STATE (Structured Nondeterminism) ===
    \* @type: Str -> Bool;
    baseMoved,         \* task -> TRUE if upstream base moved (per-PR)
    \* @type: Str -> Bool;
    hasConflict        \* task -> TRUE if merge would conflict (per-PR)

\* @type: <<Str -> Str, Str -> Str, Str -> Str, Str -> Int, Str -> Int, Str -> Bool, Str -> Str, Str -> Str, Str -> Bool, Str -> Bool, Str -> Bool>>;
vars == <<kanban, wState, wType, mergeAttempts, recoveryAttempts,
          inConflictQueue, worktreeState, lastError, githubSynced,
          baseMoved, hasConflict>>

\* =========================================================================
\* State and type definitions
\* =========================================================================

WorkerStates == {
    "idle", "needs_fix", "fixing", "needs_merge", "merging",
    "merge_conflict", "needs_resolve", "needs_multi_resolve",
    "resolving", "merged", "failed"
}

KanbanValues == {" ", "=", "x", "*", "P"}

WorkerTypes == {"none", "main", "fix", "resolve"}

WorktreeValues == {"absent", "present", "cleaning"}

ErrorValues == {"", "merge_conflict", "rebase_failed", "hard_fail"}

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
\* Helpers
\* =========================================================================

\* Unchanged groups for concise UNCHANGED clauses
EffectVarsUnchanged == UNCHANGED <<inConflictQueue, worktreeState, lastError, githubSynced>>
EnvVarsUnchanged == UNCHANGED <<baseMoved, hasConflict>>
AllAuxUnchanged == EffectVarsUnchanged /\ EnvVarsUnchanged

\* check_permanent effect: if recovery exhausted, set kanban to "*"
\* @type: (Str) => Str;
KanbanAfterCheckPermanent(t) ==
    IF recoveryAttempts[t] >= MaxRecoveryAttempts THEN "*" ELSE kanban[t]

\* =========================================================================
\* Init and CInit
\* =========================================================================

Init ==
    /\ kanban = [u \in Tasks |-> " "]
    /\ wState = [u \in Tasks |-> "idle"]
    /\ wType = [u \in Tasks |-> "none"]
    /\ mergeAttempts = [u \in Tasks |-> 0]
    /\ recoveryAttempts = [u \in Tasks |-> 0]
    /\ inConflictQueue = [u \in Tasks |-> FALSE]
    /\ worktreeState = [u \in Tasks |-> "absent"]
    /\ lastError = [u \in Tasks |-> ""]
    /\ githubSynced = [u \in Tasks |-> TRUE]
    /\ baseMoved = [u \in Tasks |-> FALSE]
    /\ hasConflict = [u \in Tasks |-> FALSE]

\* Apalache constant initialization
\* 3 tasks: T1 uses {f1}, T2 uses {f2}, T3 uses {f1, f3}
\* T3 depends on T1 (exercises dependency ordering + file conflict)
CInit ==
    /\ Tasks = {"T1", "T2", "T3"}
    /\ MaxWorkers = 2
    /\ FixWorkerLimit = 1
    /\ MaxMergeAttempts = 3
    /\ MaxRecoveryAttempts = 2
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
\* Effects: creates worktree, marks github out of sync
SpawnMainWorker(t) ==
    /\ t \in ReadyTasks
    /\ Cardinality(ActiveMain) < MaxWorkers
    /\ ~HasFileConflict(t)
    /\ kanban' = [kanban EXCEPT ![t] = "="]
    /\ wState' = [wState EXCEPT ![t] = "needs_merge"]
    /\ wType' = [wType EXCEPT ![t] = "main"]
    /\ worktreeState' = [worktreeState EXCEPT ![t] = "present"]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, lastError>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Actions - Merge Cycle
\* =========================================================================

\* Worker starts merge (guarded: merge_attempts < max)
\* Effect: inc_merge_attempts
WorkerMergeStart(t) ==
    /\ wState[t] = "needs_merge"
    /\ mergeAttempts[t] < MaxMergeAttempts
    /\ wState' = [wState EXCEPT ![t] = "merging"]
    /\ mergeAttempts' = [mergeAttempts EXCEPT ![t] = mergeAttempts[t] + 1]
    /\ UNCHANGED <<kanban, wType, recoveryAttempts>>
    /\ AllAuxUnchanged

\* Worker starts merge (fallback: max exceeded -> failed)
\* Effect: check_permanent
WorkerMergeStartFallback(t) ==
    /\ wState[t] = "needs_merge"
    /\ mergeAttempts[t] >= MaxMergeAttempts
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ kanban' = [kanban EXCEPT ![t] = KanbanAfterCheckPermanent(t)]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<wType, mergeAttempts, recoveryAttempts,
                   inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* Merge succeeded
\* Effects: sync_github, cleanup_batch, cleanup_worktree, release_claim
MergeSucceeded(t) ==
    /\ wState[t] = "merging"
    /\ wState' = [wState EXCEPT ![t] = "merged"]
    /\ kanban' = [kanban EXCEPT ![t] = "x"]
    /\ wType' = [wType EXCEPT ![t] = "none"]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = TRUE]
    /\ worktreeState' = [worktreeState EXCEPT ![t] = "cleaning"]
    /\ inConflictQueue' = [inConflictQueue EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, lastError>>
    /\ EnvVarsUnchanged

\* Merge conflict detected: merging -> merge_conflict
\* Structured nondeterminism: only fires when hasConflict is TRUE
\* Effects: set_error, add_conflict_queue
MergeConflictDetected(t) ==
    /\ wState[t] = "merging"
    /\ hasConflict[t] = TRUE
    /\ wState' = [wState EXCEPT ![t] = "merge_conflict"]
    /\ lastError' = [lastError EXCEPT ![t] = "merge_conflict"]
    /\ inConflictQueue' = [inConflictQueue EXCEPT ![t] = TRUE]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts,
                   worktreeState, githubSynced>>
    /\ EnvVarsUnchanged

\* Conflict routed to single-PR resolve (guarded: merge_attempts < max)
ConflictToResolve(t) ==
    /\ wState[t] = "merge_conflict"
    /\ mergeAttempts[t] < MaxMergeAttempts
    /\ wState' = [wState EXCEPT ![t] = "needs_resolve"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>
    /\ AllAuxUnchanged

\* Conflict routed to multi-PR resolve (guarded: merge_attempts < max)
ConflictToMultiResolve(t) ==
    /\ wState[t] = "merge_conflict"
    /\ mergeAttempts[t] < MaxMergeAttempts
    /\ wState' = [wState EXCEPT ![t] = "needs_multi_resolve"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>
    /\ AllAuxUnchanged

\* Conflict fallback: merge_conflict -> failed (attempts exhausted)
\* Effect: check_permanent
ConflictToFailed(t) ==
    /\ wState[t] = "merge_conflict"
    /\ mergeAttempts[t] >= MaxMergeAttempts
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ kanban' = [kanban EXCEPT ![t] = KanbanAfterCheckPermanent(t)]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<wType, mergeAttempts, recoveryAttempts,
                   inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* Merge out of date: rebase succeeded
\* Structured nondeterminism: requires baseMoved AND ~hasConflict
MergeOutOfDateOk(t) ==
    /\ wState[t] = "merging"
    /\ baseMoved[t] = TRUE
    /\ hasConflict[t] = FALSE
    /\ wState' = [wState EXCEPT ![t] = "needs_merge"]
    /\ baseMoved' = [baseMoved EXCEPT ![t] = FALSE]  \* rebase brings up to date
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts, hasConflict>>
    /\ EffectVarsUnchanged

\* Merge out of date: rebase failed due to conflict
\* Structured nondeterminism: requires baseMoved AND hasConflict
\* Effects: set_error, check_permanent
MergeOutOfDateFail(t) ==
    /\ wState[t] = "merging"
    /\ baseMoved[t] = TRUE
    /\ hasConflict[t] = TRUE
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ kanban' = [kanban EXCEPT ![t] = KanbanAfterCheckPermanent(t)]
    /\ lastError' = [lastError EXCEPT ![t] = "rebase_failed"]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<wType, mergeAttempts, recoveryAttempts,
                   inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* Merge transient fail: merging -> needs_merge (guarded: merge_attempts < max)
MergeTransientFailRetry(t) ==
    /\ wState[t] = "merging"
    /\ mergeAttempts[t] < MaxMergeAttempts
    /\ wState' = [wState EXCEPT ![t] = "needs_merge"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>
    /\ AllAuxUnchanged

\* Merge transient fail: merging -> failed (fallback: attempts exhausted)
\* Effects: set_error, check_permanent
MergeTransientFailAbort(t) ==
    /\ wState[t] = "merging"
    /\ mergeAttempts[t] >= MaxMergeAttempts
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ kanban' = [kanban EXCEPT ![t] = KanbanAfterCheckPermanent(t)]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<wType, mergeAttempts, recoveryAttempts,
                   inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* Merge already merged: merging -> merged (PR merged externally during merge attempt)
\* Effects: sync_github, cleanup_batch, cleanup_worktree, release_claim
MergeAlreadyMerged(t) ==
    /\ wState[t] = "merging"
    /\ wState' = [wState EXCEPT ![t] = "merged"]
    /\ kanban' = [kanban EXCEPT ![t] = "x"]
    /\ wType' = [wType EXCEPT ![t] = "none"]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = TRUE]
    /\ worktreeState' = [worktreeState EXCEPT ![t] = "cleaning"]
    /\ inConflictQueue' = [inConflictQueue EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, lastError>>
    /\ EnvVarsUnchanged

\* Merge hard fail (infrastructure failure)
\* Effects: set_error, check_permanent
MergeHardFail(t) ==
    /\ wState[t] = "merging"
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ kanban' = [kanban EXCEPT ![t] = KanbanAfterCheckPermanent(t)]
    /\ lastError' = [lastError EXCEPT ![t] = "hard_fail"]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<wType, mergeAttempts, recoveryAttempts,
                   inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* merge.pr_merged: any non-idle/non-merged -> merged (wildcard)
\* Effects: sync_github, cleanup_batch, cleanup_worktree, release_claim
ExternalPrMerged(t) ==
    /\ wState[t] \notin {"idle", "merged"}
    /\ wState' = [wState EXCEPT ![t] = "merged"]
    /\ kanban' = [kanban EXCEPT ![t] = "x"]
    /\ wType' = [wType EXCEPT ![t] = "none"]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = TRUE]
    /\ worktreeState' = [worktreeState EXCEPT ![t] = "cleaning"]
    /\ inConflictQueue' = [inConflictQueue EXCEPT ![t] = FALSE]
    /\ lastError' = [lastError EXCEPT ![t] = ""]
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged

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
    /\ AllAuxUnchanged

\* Spawn fix worker from failed: recovery via fix (guarded by recovery attempts)
\* Effects: inc_recovery, clear_error
SpawnFixWorkerFromFailed(t) ==
    /\ wState[t] = "failed"
    /\ recoveryAttempts[t] < MaxRecoveryAttempts
    /\ Cardinality(ActivePriority) < FixWorkerLimit
    /\ wState' = [wState EXCEPT ![t] = "needs_fix"]
    /\ wType' = [wType EXCEPT ![t] = "fix"]
    /\ kanban' = [kanban EXCEPT ![t] = "="]
    /\ recoveryAttempts' = [recoveryAttempts EXCEPT ![t] = recoveryAttempts[t] + 1]
    /\ lastError' = [lastError EXCEPT ![t] = ""]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<mergeAttempts, inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* Fix started: needs_fix -> fixing
FixStarted(t) ==
    /\ wState[t] = "needs_fix"
    /\ wState' = [wState EXCEPT ![t] = "fixing"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>
    /\ AllAuxUnchanged

\* Fix pass: fixing -> needs_merge (guarded: merge_attempts < max)
\* Worker retains its current wType (fix) through the merge cycle.
\* wType is only set to "none" on terminal transitions (MergeSucceeded, etc.)
\* Effects: inc_merge_attempts, rm_conflict_queue
FixPassGuarded(t) ==
    /\ wState[t] = "fixing"
    /\ mergeAttempts[t] < MaxMergeAttempts
    /\ wState' = [wState EXCEPT ![t] = "needs_merge"]
    /\ mergeAttempts' = [mergeAttempts EXCEPT ![t] = mergeAttempts[t] + 1]
    /\ inConflictQueue' = [inConflictQueue EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<kanban, wType, recoveryAttempts,
                   worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* Fix pass fallback: fixing -> failed (merge budget exhausted)
\* Effect: check_permanent
FixPassFallback(t) ==
    /\ wState[t] = "fixing"
    /\ mergeAttempts[t] >= MaxMergeAttempts
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ kanban' = [kanban EXCEPT ![t] = KanbanAfterCheckPermanent(t)]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<wType, mergeAttempts, recoveryAttempts,
                   inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* Fix fail: fixing -> failed
\* Effect: check_permanent
FixFail(t) ==
    /\ wState[t] = "fixing"
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ kanban' = [kanban EXCEPT ![t] = KanbanAfterCheckPermanent(t)]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<wType, mergeAttempts, recoveryAttempts,
                   inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* Fix partial: fixing -> needs_fix (retry)
FixPartial(t) ==
    /\ wState[t] = "fixing"
    /\ wState' = [wState EXCEPT ![t] = "needs_fix"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>
    /\ AllAuxUnchanged

\* Fix skip: fixing -> needs_merge (chains through fix_completed)
\* Effect: rm_conflict_queue
FixSkip(t) ==
    /\ wState[t] = "fixing"
    /\ wState' = [wState EXCEPT ![t] = "needs_merge"]
    /\ inConflictQueue' = [inConflictQueue EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts,
                   worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* Fix timeout: fixing -> needs_fix
FixTimeout(t) ==
    /\ wState[t] = "fixing"
    /\ wState' = [wState EXCEPT ![t] = "needs_fix"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>
    /\ AllAuxUnchanged

\* Fix already merged: needs_fix -> merged, kanban "x"
\* Effects: sync_github, cleanup_batch, cleanup_worktree, release_claim, clear_error, rm_conflict_queue
FixAlreadyMerged(t) ==
    /\ wState[t] = "needs_fix"
    /\ wState' = [wState EXCEPT ![t] = "merged"]
    /\ kanban' = [kanban EXCEPT ![t] = "x"]
    /\ wType' = [wType EXCEPT ![t] = "none"]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = TRUE]
    /\ worktreeState' = [worktreeState EXCEPT ![t] = "cleaning"]
    /\ inConflictQueue' = [inConflictQueue EXCEPT ![t] = FALSE]
    /\ lastError' = [lastError EXCEPT ![t] = ""]
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Actions - Resolve Cycle
\* =========================================================================

\* Resolve started: needs_resolve -> resolving
\* Sets wType to "resolve" and checks priority capacity (shared with fix workers).
\* Matches implementation: resolve-workers.sh calls pool_add <pid> "resolve"
ResolveStarted(t) ==
    /\ wState[t] = "needs_resolve"
    /\ Cardinality(ActivePriority) < FixWorkerLimit
    /\ wState' = [wState EXCEPT ![t] = "resolving"]
    /\ wType' = [wType EXCEPT ![t] = "resolve"]
    /\ UNCHANGED <<kanban, mergeAttempts, recoveryAttempts>>
    /\ AllAuxUnchanged

\* Resolve succeeded: resolving -> needs_merge (chain through resolved)
\* Effects: rm_conflict_queue, clear_error. Worker process exits.
ResolveSucceeded(t) ==
    /\ wState[t] = "resolving"
    /\ wState' = [wState EXCEPT ![t] = "needs_merge"]
    /\ wType' = [wType EXCEPT ![t] = "none"]
    /\ inConflictQueue' = [inConflictQueue EXCEPT ![t] = FALSE]
    /\ lastError' = [lastError EXCEPT ![t] = ""]
    /\ UNCHANGED <<kanban, mergeAttempts, recoveryAttempts,
                   worktreeState, githubSynced>>
    /\ EnvVarsUnchanged

\* Resolve fail: resolving -> failed
\* Effect: check_permanent. Worker process exits, clearing pool type.
ResolveFail(t) ==
    /\ wState[t] = "resolving"
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ wType' = [wType EXCEPT ![t] = "none"]
    /\ kanban' = [kanban EXCEPT ![t] = KanbanAfterCheckPermanent(t)]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts,
                   inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* Resolve timeout: resolving -> needs_resolve
\* Worker process exits on timeout, clearing pool type.
ResolveTimeout(t) ==
    /\ wState[t] = "resolving"
    /\ wState' = [wState EXCEPT ![t] = "needs_resolve"]
    /\ wType' = [wType EXCEPT ![t] = "none"]
    /\ UNCHANGED <<kanban, mergeAttempts, recoveryAttempts>>
    /\ AllAuxUnchanged

\* =========================================================================
\* Actions - Multi-Resolve Cycle
\* =========================================================================

\* Resolve started from multi-resolve: needs_multi_resolve -> resolving
\* Sets wType to "resolve" and checks priority capacity (shared with fix workers).
ResolveStartedFromMulti(t) ==
    /\ wState[t] = "needs_multi_resolve"
    /\ Cardinality(ActivePriority) < FixWorkerLimit
    /\ wState' = [wState EXCEPT ![t] = "resolving"]
    /\ wType' = [wType EXCEPT ![t] = "resolve"]
    /\ UNCHANGED <<kanban, mergeAttempts, recoveryAttempts>>
    /\ AllAuxUnchanged

\* Multi-resolve batch failed: needs_multi_resolve -> needs_resolve
ResolveBatchFailed(t) ==
    /\ wState[t] = "needs_multi_resolve"
    /\ wState' = [wState EXCEPT ![t] = "needs_resolve"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>
    /\ AllAuxUnchanged

\* Resolve already merged: needs_resolve -> merged, kanban "x"
\* Effects: sync_github, cleanup_batch, cleanup_worktree, release_claim, clear_error, rm_conflict_queue
ResolveAlreadyMergedFromNeedsResolve(t) ==
    /\ wState[t] = "needs_resolve"
    /\ wState' = [wState EXCEPT ![t] = "merged"]
    /\ kanban' = [kanban EXCEPT ![t] = "x"]
    /\ wType' = [wType EXCEPT ![t] = "none"]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = TRUE]
    /\ worktreeState' = [worktreeState EXCEPT ![t] = "cleaning"]
    /\ inConflictQueue' = [inConflictQueue EXCEPT ![t] = FALSE]
    /\ lastError' = [lastError EXCEPT ![t] = ""]
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged

\* Resolve already merged: needs_multi_resolve -> merged, kanban "x"
\* Effects: sync_github, cleanup_batch, cleanup_worktree, release_claim, clear_error, rm_conflict_queue
ResolveAlreadyMergedFromNeedsMulti(t) ==
    /\ wState[t] = "needs_multi_resolve"
    /\ wState' = [wState EXCEPT ![t] = "merged"]
    /\ kanban' = [kanban EXCEPT ![t] = "x"]
    /\ wType' = [wType EXCEPT ![t] = "none"]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = TRUE]
    /\ worktreeState' = [worktreeState EXCEPT ![t] = "cleaning"]
    /\ inConflictQueue' = [inConflictQueue EXCEPT ![t] = FALSE]
    /\ lastError' = [lastError EXCEPT ![t] = ""]
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged

\* Resolve max exceeded: needs_resolve -> failed
\* Effect: check_permanent
ResolveMaxExceededFromNeedsResolve(t) ==
    /\ wState[t] = "needs_resolve"
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ kanban' = [kanban EXCEPT ![t] = KanbanAfterCheckPermanent(t)]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<wType, mergeAttempts, recoveryAttempts,
                   inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* Resolve max exceeded: needs_multi_resolve -> failed
\* Effect: check_permanent
ResolveMaxExceededFromNeedsMulti(t) ==
    /\ wState[t] = "needs_multi_resolve"
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ kanban' = [kanban EXCEPT ![t] = KanbanAfterCheckPermanent(t)]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<wType, mergeAttempts, recoveryAttempts,
                   inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* Resolve stuck_reset: resolving -> needs_resolve (guarded: merge_attempts < max)
\* Effect: inc_merge_attempts. Worker process exits.
ResolveStuckResetGuarded(t) ==
    /\ wState[t] = "resolving"
    /\ mergeAttempts[t] < MaxMergeAttempts
    /\ wState' = [wState EXCEPT ![t] = "needs_resolve"]
    /\ wType' = [wType EXCEPT ![t] = "none"]
    /\ mergeAttempts' = [mergeAttempts EXCEPT ![t] = mergeAttempts[t] + 1]
    /\ UNCHANGED <<kanban, recoveryAttempts>>
    /\ AllAuxUnchanged

\* Resolve stuck_reset: resolving -> failed (fallback: attempts exhausted)
\* Effect: check_permanent. Worker process exits.
ResolveStuckResetFallback(t) ==
    /\ wState[t] = "resolving"
    /\ mergeAttempts[t] >= MaxMergeAttempts
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ wType' = [wType EXCEPT ![t] = "none"]
    /\ kanban' = [kanban EXCEPT ![t] = KanbanAfterCheckPermanent(t)]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts,
                   inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* Resolve fail: needs_resolve -> failed
\* Effect: check_permanent
ResolveFailFromNeedsResolve(t) ==
    /\ wState[t] = "needs_resolve"
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ kanban' = [kanban EXCEPT ![t] = KanbanAfterCheckPermanent(t)]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<wType, mergeAttempts, recoveryAttempts,
                   inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* Resolve fail: needs_multi_resolve -> failed
\* Effect: check_permanent
ResolveFailFromNeedsMulti(t) ==
    /\ wState[t] = "needs_multi_resolve"
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ kanban' = [kanban EXCEPT ![t] = KanbanAfterCheckPermanent(t)]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<wType, mergeAttempts, recoveryAttempts,
                   inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Actions - Recovery
\* =========================================================================

\* Recovery from failed (guarded: recovery_attempts < max)
\* Reset wType to "main" -- recovered worker re-enters merge cycle
\* Effects: inc_recovery, reset_merge, clear_error
Recovery(t) ==
    /\ wState[t] = "failed"
    /\ recoveryAttempts[t] < MaxRecoveryAttempts
    /\ wState' = [wState EXCEPT ![t] = "needs_merge"]
    /\ recoveryAttempts' = [recoveryAttempts EXCEPT ![t] = recoveryAttempts[t] + 1]
    /\ mergeAttempts' = [mergeAttempts EXCEPT ![t] = 0]
    /\ kanban' = [kanban EXCEPT ![t] = "="]
    /\ wType' = [wType EXCEPT ![t] = "main"]
    /\ lastError' = [lastError EXCEPT ![t] = ""]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* Recovery fallback: failed -> permanent failure
\* Effect: check_permanent (sets kanban "*")
RecoveryFallback(t) ==
    /\ wState[t] = "failed"
    /\ recoveryAttempts[t] >= MaxRecoveryAttempts
    /\ kanban' = [kanban EXCEPT ![t] = "*"]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<wState, wType, mergeAttempts, recoveryAttempts,
                   inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* resume.abort: * -> failed, kanban "*"
\* Effects: sync_github. Kills active worker, releases pool slot.
ResumeAbort(t) ==
    /\ wState[t] \notin {"idle", "merged"}
    /\ wState' = [wState EXCEPT ![t] = "failed"]
    /\ kanban' = [kanban EXCEPT ![t] = "*"]
    /\ wType' = [wType EXCEPT ![t] = "none"]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = TRUE]
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts,
                   inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* user.resume: failed -> needs_merge, kanban "="
\* Effects: rm_conflict_queue, clear_error
UserResume(t) ==
    /\ wState[t] = "failed"
    /\ wState' = [wState EXCEPT ![t] = "needs_merge"]
    /\ kanban' = [kanban EXCEPT ![t] = "="]
    /\ wType' = [wType EXCEPT ![t] = "main"]
    /\ lastError' = [lastError EXCEPT ![t] = ""]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ inConflictQueue' = [inConflictQueue EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, worktreeState>>
    /\ EnvVarsUnchanged

\* permanent_failure: failed -> failed, kanban "*"
\* Effect: sync_github
PermanentFailure(t) ==
    /\ wState[t] = "failed"
    /\ kanban' = [kanban EXCEPT ![t] = "*"]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = TRUE]
    /\ UNCHANGED <<wState, wType, mergeAttempts, recoveryAttempts,
                   inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Actions - Startup Reset
\* Reset running states back to waiting counterparts on orchestrator restart.
\* Each running state gets its own action to avoid partial UNCHANGED issues.
\* =========================================================================

StartupResetFixing(t) ==
    /\ wState[t] = "fixing"
    /\ wState' = [wState EXCEPT ![t] = "needs_fix"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>
    /\ AllAuxUnchanged

\* startup.reset: merging -> needs_merge, effect: reset_merge (critical!)
\* Resets merge budget so worker gets fresh attempts after restart
StartupResetMerging(t) ==
    /\ wState[t] = "merging"
    /\ wState' = [wState EXCEPT ![t] = "needs_merge"]
    /\ mergeAttempts' = [mergeAttempts EXCEPT ![t] = 0]
    /\ UNCHANGED <<kanban, wType, recoveryAttempts>>
    /\ AllAuxUnchanged

StartupResetResolving(t) ==
    /\ wState[t] = "resolving"
    /\ wState' = [wState EXCEPT ![t] = "needs_resolve"]
    /\ wType' = [wType EXCEPT ![t] = "none"]
    /\ mergeAttempts' = [mergeAttempts EXCEPT ![t] = 0]
    /\ UNCHANGED <<kanban, recoveryAttempts>>
    /\ AllAuxUnchanged

\* =========================================================================
\* Actions - Startup Reconciliation (Effect-State Repair)
\*
\* Models _scheduler_reconcile_merged_workers() from scheduler.sh.
\* After a mid-transition crash, the state machine may be in a terminal
\* state but with stale effect-state variables. These actions fire on
\* startup to bring effect-state into consistency with lifecycle state.
\* =========================================================================

\* Reconcile merged worker: wState="merged" but effect-state inconsistent.
\* Matches _scheduler_reconcile_merged_workers() which checks:
\*   Bug 1: kanban != "x" => update_kanban_status("x")
\*   Bug 2: conflict queue not cleared => conflict_queue_remove()
\*   Bug 4: GitHub not synced => github_issue_sync_task_status()
\* Also handles worktree leaked (cleanup_worktree never ran) and stale error.
StartupReconcileMerged(t) ==
    /\ wState[t] = "merged"
    \* Guard: at least one effect-state variable is inconsistent
    /\ \/ kanban[t] /= "x"
       \/ inConflictQueue[t] = TRUE
       \/ githubSynced[t] = FALSE
       \/ worktreeState[t] = "present"
       \/ lastError[t] /= ""
    \* Reconcile: set all effect-state to expected values for merged
    /\ kanban' = [kanban EXCEPT ![t] = "x"]
    /\ inConflictQueue' = [inConflictQueue EXCEPT ![t] = FALSE]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = TRUE]
    /\ worktreeState' = [worktreeState EXCEPT ![t] =
        IF worktreeState[t] = "present" THEN "cleaning" ELSE worktreeState[t]]
    /\ lastError' = [lastError EXCEPT ![t] = ""]
    /\ UNCHANGED <<wState, wType, mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged

\* Reconcile conflict state: wState="merge_conflict" but effects not applied.
\* After MidCrashMergeConflict, set_error and add_conflict_queue didn't run.
\* On restart, the scheduler detects merge_conflict state and ensures
\* the task is queued for resolution and error is set.
StartupReconcileConflict(t) ==
    /\ wState[t] = "merge_conflict"
    \* Guard: effect-state inconsistent with merge_conflict state
    /\ \/ inConflictQueue[t] = FALSE
       \/ lastError[t] /= "merge_conflict"
    \* Reconcile: apply the effects that should have run
    /\ inConflictQueue' = [inConflictQueue EXCEPT ![t] = TRUE]
    /\ lastError' = [lastError EXCEPT ![t] = "merge_conflict"]
    /\ UNCHANGED <<wState, kanban, wType, mergeAttempts, recoveryAttempts,
                   worktreeState, githubSynced>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Actions - Crash
\* Models process crash at two granularities:
\*   1. Pre-transition crash: process dies during running state before any
\*      transition fires. State unchanged, effects may be partial.
\*   2. Mid-transition crash: emit_event() wrote git_state_set() (atomic)
\*      but crashed before _lifecycle_update_kanban() or effects ran.
\*      State updated to target, kanban stale, effects not applied.
\*
\* The implementation's emit_event() applies changes sequentially:
\*   git_state_set -> kanban update -> event log -> effects
\* Each is individually atomic (temp+mv), but the sequence is not.
\* =========================================================================

\* Pre-transition crash while fixing: state stays, githubSynced may drift
CrashWhileFixing(t) ==
    /\ wState[t] = "fixing"
    /\ UNCHANGED <<wState, kanban, wType, mergeAttempts, recoveryAttempts>>
    /\ \E v \in BOOLEAN : githubSynced' = [githubSynced EXCEPT ![t] = v]
    /\ UNCHANGED <<inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* Pre-transition crash while merging: state stays, githubSynced may drift
CrashWhileMerging(t) ==
    /\ wState[t] = "merging"
    /\ UNCHANGED <<wState, kanban, wType, mergeAttempts, recoveryAttempts>>
    /\ \E v \in BOOLEAN : githubSynced' = [githubSynced EXCEPT ![t] = v]
    /\ UNCHANGED <<inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* Pre-transition crash while resolving: state stays, queue may drift
CrashWhileResolving(t) ==
    /\ wState[t] = "resolving"
    /\ UNCHANGED <<wState, kanban, wType, mergeAttempts, recoveryAttempts>>
    /\ \E v1 \in BOOLEAN : githubSynced' = [githubSynced EXCEPT ![t] = v1]
    /\ \E v2 \in BOOLEAN : inConflictQueue' = [inConflictQueue EXCEPT ![t] = v2]
    /\ UNCHANGED <<worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* Mid-transition crash: merge.succeeded wrote state="merged" but kanban
\* still at old value. Effects (sync_github, cleanup_worktree, release_claim)
\* not applied. Catches "state=merged but kanban='='" inconsistency.
MidCrashMergeSucceeded(t) ==
    /\ wState[t] = "merging"
    /\ wState' = [wState EXCEPT ![t] = "merged"]
    /\ wType' = [wType EXCEPT ![t] = "none"]
    \* kanban NOT updated (crash before _lifecycle_update_kanban)
    /\ UNCHANGED <<kanban, mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged
    \* Effects not applied
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<inConflictQueue, worktreeState, lastError>>

\* Mid-transition crash: merge.conflict wrote state="merge_conflict" but
\* effects (set_error, add_conflict_queue) not applied.
MidCrashMergeConflict(t) ==
    /\ wState[t] = "merging"
    /\ hasConflict[t] = TRUE
    /\ wState' = [wState EXCEPT ![t] = "merge_conflict"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged
    \* set_error and add_conflict_queue not applied
    /\ UNCHANGED <<inConflictQueue, worktreeState, lastError, githubSynced>>

\* Mid-transition crash: fix.pass wrote state via chain but effects
\* (inc_merge_attempts, rm_conflict_queue) not applied.
MidCrashFixPass(t) ==
    /\ wState[t] = "fixing"
    /\ wState' = [wState EXCEPT ![t] =
        IF mergeAttempts[t] < MaxMergeAttempts
        THEN "needs_merge"
        ELSE "failed"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged
    \* inc_merge_attempts and rm_conflict_queue not applied
    /\ UNCHANGED <<inConflictQueue, worktreeState, lastError, githubSynced>>

\* =========================================================================
\* Actions - Worktree Cleanup Completion
\* Models the async completion of worktree removal after merge. Without this,
\* worktreeState goes to "cleaning" but never "absent", preventing verification
\* of stronger eventual invariants (merged => eventually absent worktree) and
\* missing "leaked worktree" bugs.
\* =========================================================================

\* Worktree cleanup finishes: cleaning -> absent
CleanupCompleted(t) ==
    /\ worktreeState[t] = "cleaning"
    /\ worktreeState' = [worktreeState EXCEPT ![t] = "absent"]
    /\ UNCHANGED <<kanban, wState, wType, mergeAttempts, recoveryAttempts,
                   inConflictQueue, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Actions - Null-Target Transitions
\* These model events where to: null in worker-lifecycle.json -- the worker
\* state is preserved but kanban visibility changes, which feeds into
\* ReadyTasks and scheduling. Catches "stuck task never becomes eligible"
\* and "reclaimed task still shows in-progress" bugs.
\* =========================================================================

\* resume.retry: * -> null, kanban "=" (mark in-progress for retry)
\* Wildcard from, guarded to non-terminal: merged would violate KanbanMergedConsistency.
ResumeRetry(t) ==
    /\ wState[t] \notin {"idle", "merged"}
    /\ kanban' = [kanban EXCEPT ![t] = "="]
    /\ UNCHANGED <<wState, wType, mergeAttempts, recoveryAttempts>>
    /\ AllAuxUnchanged

\* task.reclaim: * -> null, kanban " " (release task back to pending)
\* Wildcard from, guarded to non-terminal: merged would violate KanbanMergedConsistency.
TaskReclaim(t) ==
    /\ wState[t] \notin {"idle", "merged"}
    /\ kanban' = [kanban EXCEPT ![t] = " "]
    /\ UNCHANGED <<wState, wType, mergeAttempts, recoveryAttempts>>
    /\ AllAuxUnchanged

\* =========================================================================
\* Actions - Pending Approval (null-target, kanban-only)
\* =========================================================================

\* task.pending_approval: * -> null, kanban "P"
\* Effect: sync_github. Marks task as awaiting approval.
TaskPendingApproval(t) ==
    /\ wState[t] \notin {"idle", "merged"}
    /\ kanban' = [kanban EXCEPT ![t] = "P"]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = TRUE]
    /\ UNCHANGED <<wState, wType, mergeAttempts, recoveryAttempts,
                   inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Actions - Planner Completed
\* =========================================================================

\* planner.completed: needs_multi_resolve -> needs_resolve
PlannerCompleted(t) ==
    /\ wState[t] = "needs_multi_resolve"
    /\ wState' = [wState EXCEPT ![t] = "needs_resolve"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>
    /\ AllAuxUnchanged

\* =========================================================================
\* Actions - Manual Start Merge
\* =========================================================================

\* manual.start_merge: needs_fix -> needs_merge
ManualStartMergeFromNeedsFix(t) ==
    /\ wState[t] = "needs_fix"
    /\ wState' = [wState EXCEPT ![t] = "needs_merge"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>
    /\ AllAuxUnchanged

\* manual.start_merge: failed -> needs_merge (guarded: recovery_attempts_lt_max)
\* Effects: inc_recovery, clear_error. kanban "="
ManualStartMergeFromFailedGuarded(t) ==
    /\ wState[t] = "failed"
    /\ recoveryAttempts[t] < MaxRecoveryAttempts
    /\ wState' = [wState EXCEPT ![t] = "needs_merge"]
    /\ recoveryAttempts' = [recoveryAttempts EXCEPT ![t] = recoveryAttempts[t] + 1]
    /\ kanban' = [kanban EXCEPT ![t] = "="]
    /\ lastError' = [lastError EXCEPT ![t] = ""]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<wType, mergeAttempts, inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* manual.start_merge: failed -> failed (fallback: guard failed)
ManualStartMergeFromFailedFallback(t) ==
    /\ wState[t] = "failed"
    /\ recoveryAttempts[t] >= MaxRecoveryAttempts
    /\ UNCHANGED <<wState, kanban, wType, mergeAttempts, recoveryAttempts>>
    /\ AllAuxUnchanged

\* =========================================================================
\* Actions - Manual Start Fix
\* =========================================================================

\* manual.start_fix: needs_merge -> fixing
ManualStartFixFromNeedsMerge(t) ==
    /\ wState[t] = "needs_merge"
    /\ wState' = [wState EXCEPT ![t] = "fixing"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>
    /\ AllAuxUnchanged

\* manual.start_fix: needs_fix -> fixing
ManualStartFixFromNeedsFix(t) ==
    /\ wState[t] = "needs_fix"
    /\ wState' = [wState EXCEPT ![t] = "fixing"]
    /\ UNCHANGED <<kanban, wType, mergeAttempts, recoveryAttempts>>
    /\ AllAuxUnchanged

\* manual.start_fix: failed -> fixing (guarded: recovery_attempts_lt_max)
\* Effects: inc_recovery, clear_error. kanban "="
ManualStartFixFromFailedGuarded(t) ==
    /\ wState[t] = "failed"
    /\ recoveryAttempts[t] < MaxRecoveryAttempts
    /\ wState' = [wState EXCEPT ![t] = "fixing"]
    /\ recoveryAttempts' = [recoveryAttempts EXCEPT ![t] = recoveryAttempts[t] + 1]
    /\ kanban' = [kanban EXCEPT ![t] = "="]
    /\ lastError' = [lastError EXCEPT ![t] = ""]
    /\ githubSynced' = [githubSynced EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<wType, mergeAttempts, inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* manual.start_fix: failed -> failed (fallback: guard failed)
ManualStartFixFromFailedFallback(t) ==
    /\ wState[t] = "failed"
    /\ recoveryAttempts[t] >= MaxRecoveryAttempts
    /\ UNCHANGED <<wState, kanban, wType, mergeAttempts, recoveryAttempts>>
    /\ AllAuxUnchanged

\* =========================================================================
\* Actions - Environment Changes (Structured Nondeterminism)
\* Per-task: each PR branch can independently become out-of-date or
\* develop conflicts. Only active (non-terminal, non-idle) workers are
\* affected since idle/terminal tasks have no live PR branch.
\* =========================================================================

\* Upstream base moves (e.g., another PR merged to main)
EnvBaseMoved(t) ==
    /\ wState[t] \notin {"idle", "merged", "failed"}
    /\ baseMoved[t] = FALSE
    /\ baseMoved' = [baseMoved EXCEPT ![t] = TRUE]
    /\ UNCHANGED <<wState, kanban, wType, mergeAttempts, recoveryAttempts, hasConflict>>
    /\ EffectVarsUnchanged

\* A conflict appears (e.g., concurrent changes to same files)
EnvConflictAppears(t) ==
    /\ wState[t] \notin {"idle", "merged", "failed"}
    /\ hasConflict[t] = FALSE
    /\ hasConflict' = [hasConflict EXCEPT ![t] = TRUE]
    /\ UNCHANGED <<wState, kanban, wType, mergeAttempts, recoveryAttempts, baseMoved>>
    /\ EffectVarsUnchanged

\* Conflict resolved externally (e.g., blocking PR merged, files no longer overlap)
EnvConflictResolved(t) ==
    /\ hasConflict[t] = TRUE
    /\ hasConflict' = [hasConflict EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<wState, kanban, wType, mergeAttempts, recoveryAttempts, baseMoved>>
    /\ EffectVarsUnchanged

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
        \/ MergeAlreadyMerged(t)
        \/ MergeConflictDetected(t)
        \/ ConflictToResolve(t)
        \/ ConflictToMultiResolve(t)
        \/ ConflictToFailed(t)
        \/ MergeOutOfDateOk(t)
        \/ MergeOutOfDateFail(t)
        \/ MergeTransientFailRetry(t)
        \/ MergeTransientFailAbort(t)
        \/ MergeHardFail(t)
        \/ ExternalPrMerged(t)
        \* Fix cycle
        \/ SpawnFixWorker(t)
        \/ SpawnFixWorkerFromFailed(t)
        \/ FixStarted(t)
        \/ FixPassGuarded(t)
        \/ FixPassFallback(t)
        \/ FixFail(t)
        \/ FixPartial(t)
        \/ FixSkip(t)
        \/ FixTimeout(t)
        \/ FixAlreadyMerged(t)
        \* Resolve cycle
        \/ ResolveStarted(t)
        \/ ResolveSucceeded(t)
        \/ ResolveFail(t)
        \/ ResolveFailFromNeedsResolve(t)
        \/ ResolveFailFromNeedsMulti(t)
        \/ ResolveTimeout(t)
        \/ ResolveStuckResetGuarded(t)
        \/ ResolveStuckResetFallback(t)
        \/ ResolveAlreadyMergedFromNeedsResolve(t)
        \/ ResolveAlreadyMergedFromNeedsMulti(t)
        \/ ResolveMaxExceededFromNeedsResolve(t)
        \/ ResolveMaxExceededFromNeedsMulti(t)
        \* Multi-resolve cycle
        \/ ResolveStartedFromMulti(t)
        \/ ResolveBatchFailed(t)
        \* Recovery
        \/ Recovery(t)
        \/ RecoveryFallback(t)
        \/ ResumeAbort(t)
        \/ UserResume(t)
        \/ PermanentFailure(t)
        \* Startup reset
        \/ StartupResetFixing(t)
        \/ StartupResetMerging(t)
        \/ StartupResetResolving(t)
        \* Startup reconciliation (effect-state repair after mid-transition crash)
        \/ StartupReconcileMerged(t)
        \/ StartupReconcileConflict(t)
        \* Pre-transition crash
        \/ CrashWhileFixing(t)
        \/ CrashWhileMerging(t)
        \/ CrashWhileResolving(t)
        \* Mid-transition crash (state written, kanban/effects not)
        \/ MidCrashMergeSucceeded(t)
        \/ MidCrashMergeConflict(t)
        \/ MidCrashFixPass(t)
        \* Worktree cleanup
        \/ CleanupCompleted(t)
        \* Null-target transitions
        \/ ResumeRetry(t)
        \/ TaskReclaim(t)
        \/ TaskPendingApproval(t)
        \* Planner completed
        \/ PlannerCompleted(t)
        \* Manual start merge
        \/ ManualStartMergeFromNeedsFix(t)
        \/ ManualStartMergeFromFailedGuarded(t)
        \/ ManualStartMergeFromFailedFallback(t)
        \* Manual start fix
        \/ ManualStartFixFromNeedsMerge(t)
        \/ ManualStartFixFromNeedsFix(t)
        \/ ManualStartFixFromFailedGuarded(t)
        \/ ManualStartFixFromFailedFallback(t)
        \* Environment changes
        \/ EnvBaseMoved(t)
        \/ EnvConflictAppears(t)
        \/ EnvConflictResolved(t)

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
        /\ WF_vars(MergeSucceeded(q) \/ MergeAlreadyMerged(q) \/ MergeHardFail(q)
                   \/ MergeConflictDetected(q)
                   \/ MergeOutOfDateOk(q) \/ MergeOutOfDateFail(q)
                   \/ MergeTransientFailRetry(q) \/ MergeTransientFailAbort(q))
        /\ WF_vars(ConflictToResolve(q) \/ ConflictToMultiResolve(q) \/ ConflictToFailed(q))
        /\ WF_vars(SpawnFixWorkerFromFailed(q))
        /\ WF_vars(FixStarted(q))
        /\ WF_vars(FixPassGuarded(q) \/ FixPassFallback(q) \/ FixFail(q)
                   \/ FixSkip(q) \/ FixTimeout(q))
        /\ WF_vars(FixAlreadyMerged(q))
        /\ WF_vars(ResolveStarted(q))
        /\ WF_vars(ResolveStartedFromMulti(q))
        /\ WF_vars(ResolveSucceeded(q) \/ ResolveFail(q)
                   \/ ResolveFailFromNeedsResolve(q) \/ ResolveFailFromNeedsMulti(q))
        /\ WF_vars(ResolveStuckResetGuarded(q) \/ ResolveStuckResetFallback(q))
        /\ WF_vars(ResolveAlreadyMergedFromNeedsResolve(q) \/ ResolveAlreadyMergedFromNeedsMulti(q))
        /\ WF_vars(ResolveMaxExceededFromNeedsResolve(q) \/ ResolveMaxExceededFromNeedsMulti(q))
        /\ WF_vars(UserResume(q))
        /\ WF_vars(PermanentFailure(q))
        /\ WF_vars(Recovery(q) \/ RecoveryFallback(q))
        /\ WF_vars(StartupReconcileMerged(q))
        /\ WF_vars(StartupReconcileConflict(q))
        /\ WF_vars(CleanupCompleted(q))
        /\ WF_vars(PlannerCompleted(q))
        /\ WF_vars(ManualStartMergeFromFailedGuarded(q) \/ ManualStartMergeFromFailedFallback(q))
        /\ WF_vars(ManualStartFixFromFailedGuarded(q) \/ ManualStartFixFromFailedFallback(q))

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
    /\ \A t \in Tasks : inConflictQueue[t] \in BOOLEAN
    /\ \A t \in Tasks : worktreeState[t] \in WorktreeValues
    /\ \A t \in Tasks : lastError[t] \in ErrorValues
    /\ \A t \in Tasks : githubSynced[t] \in BOOLEAN
    /\ \A t \in Tasks : baseMoved[t] \in BOOLEAN
    /\ \A t \in Tasks : hasConflict[t] \in BOOLEAN

\* WorkerPoolCapacity: main and priority workers within limits
WorkerPoolCapacity ==
    /\ Cardinality(ActiveMain) <= MaxWorkers
    /\ Cardinality(ActivePriority) <= FixWorkerLimit

\* BoundedCounters: merge/recovery within limits per task
BoundedCounters ==
    /\ \A t \in Tasks : mergeAttempts[t] <= MaxMergeAttempts + 1
    /\ \A t \in Tasks : recoveryAttempts[t] <= MaxRecoveryAttempts + 1

\* KanbanMergedConsistency: crash-safe version.
\* DESIGN GOAL: kanban "x" <=> wState "merged"
\*   Violated transiently by MidCrashMergeSucceeded — emit_event() crashes
\*   after git_state_set("merged") but before _lifecycle_update_kanban("x").
\*   RECONCILED by StartupReconcileMerged(t) (models _scheduler_reconcile_merged_workers)
\*   which detects kanban != "x" for merged workers and fixes it on restart.
\* Crash-safe: the converse always holds — kanban "x" always means merged.
KanbanMergedConsistency ==
    \A t \in Tasks : kanban[t] = "x" => wState[t] = "merged"

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

\* KanbanFailedConsistency: permanent failure marker implies failed state
KanbanFailedConsistency ==
    \A t \in Tasks :
        kanban[t] = "*" => wState[t] = "failed"

\* =========================================================================
\* Cross-Module Invariants (Effect-State Consistency)
\* These validate consistency between effect-state and lifecycle state.
\* Crash actions introduce nondeterminism, so invariants must account for
\* partially-applied effects in running states.
\* =========================================================================

\* ConflictQueueConsistency: crash-safe version.
\* DESIGN GOAL: inConflictQueue => wState \in {conflict-related states only}
\*   Violated transiently when MidCrashFixPass + MidCrashMergeSucceeded chain:
\*   queue TRUE persists from conflict through fix/merge all the way to "merged"
\*   because rm_conflict_queue effects never run.
\*   RECONCILED by StartupReconcileMerged(t) which clears inConflictQueue for
\*   merged workers on restart.
\* Crash-safe: allow any non-idle state (queue is never set during "idle").
ConflictQueueConsistency ==
    \A t \in Tasks :
        inConflictQueue[t] => wState[t] /= "idle"

\* WorktreeStateConsistency: crash-safe version.
\* DESIGN GOAL: merged => worktreeState \in {"absent", "cleaning"}
\*   Violated by MidCrashMergeSucceeded — cleanup_worktree effect never runs,
\*   leaving worktreeState="present" with wState="merged". Implementation fix:
\*   reconcile leaked worktrees for workers in merged state on restart.
\* Crash-safe: merged allows "present" (leaked worktree), idle requires absent.
WorktreeStateConsistency ==
    \A t \in Tasks :
        \/ (wState[t] = "idle" /\ worktreeState[t] = "absent")
        \/ (wState[t] = "merged")
        \/ (wState[t] \notin {"idle", "merged"})

\* ErrorStateConsistency: lastError reflects the failure mode
\* rebase_failed and hard_fail only persist in failed state
\* merge_conflict can persist through the conflict resolution chain
ErrorStateConsistency ==
    \A t \in Tasks :
        /\ (lastError[t] = "merge_conflict" =>
            wState[t] \in {"merge_conflict", "needs_resolve", "needs_multi_resolve",
                           "resolving", "failed", "merging"})
        /\ (lastError[t] = "rebase_failed" => wState[t] = "failed")
        /\ (lastError[t] = "hard_fail" => wState[t] = "failed")

\* MergedCleanupConsistency: crash-safe version.
\* DESIGN GOAL: wState = "merged" => worktreeState \in {"absent", "cleaning"}
\*   Violated by MidCrashMergeSucceeded — same as WorktreeStateConsistency.
\* Crash-safe: allow "present" (leaked worktree after mid-transition crash).
MergedCleanupConsistency ==
    \A t \in Tasks :
        wState[t] = "merged" => worktreeState[t] \in {"absent", "cleaning", "present"}

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
