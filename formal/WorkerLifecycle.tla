--------------------------- MODULE WorkerLifecycle ---------------------------
(*
 * TLA+ formal model of Chief Wiggum's worker lifecycle state machine.
 *
 * Faithfully encodes every transition from config/worker-lifecycle.json.
 * Transient states (fix_completed, resolved) are skipped atomically --
 * chains collapse into a single transition. merge_conflict is modeled
 * as a real state since it persists until a conflict.* event fires.
 *
 * Null-target transitions (resume.retry, task.reclaim) are omitted --
 * they don't change state.
 *
 * Designed for Apalache symbolic model checking (type annotations, CInit).
 *)

EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Int;
    MAX_MERGE_ATTEMPTS,
    \* @type: Int;
    MAX_RECOVERY_ATTEMPTS

VARIABLES
    \* @type: Str;
    state,
    \* @type: Int;
    mergeAttempts,
    \* @type: Int;
    recoveryAttempts,
    \* @type: Str;
    kanban

\* @type: <<Str, Int, Int, Str>>;
vars == <<state, mergeAttempts, recoveryAttempts, kanban>>

\* =========================================================================
\* Type and state definitions
\* =========================================================================

AllStates == {
    "none", "needs_fix", "fixing", "needs_merge", "merging",
    "merge_conflict", "needs_resolve", "needs_multi_resolve",
    "resolving", "merged", "failed"
}

TerminalStates == {"merged", "failed"}

KanbanValues == {" ", "=", "x", "*"}

\* =========================================================================
\* Init and CInit
\* =========================================================================

Init ==
    /\ state = "none"
    /\ mergeAttempts = 0
    /\ recoveryAttempts = 0
    /\ kanban = " "

\* Apalache constant initialization (replaces .cfg)
CInit ==
    /\ MAX_MERGE_ATTEMPTS = 2
    /\ MAX_RECOVERY_ATTEMPTS = 1

\* =========================================================================
\* Helper: check_permanent effect (inline)
\* If recovery attempts exhausted, set kanban to "*"
\* =========================================================================

\* @type: (Str) => Str;
KanbanAfterCheckPermanent(currentKanban) ==
    IF recoveryAttempts >= MAX_RECOVERY_ATTEMPTS
    THEN "*"
    ELSE currentKanban

\* =========================================================================
\* Actions - Worker Spawn
\* =========================================================================

\* worker.spawned: none -> needs_merge, kanban "="
WorkerSpawned ==
    /\ state = "none"
    /\ state' = "needs_merge"
    /\ kanban' = "="
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* =========================================================================
\* Actions - Fix Cycle
\* =========================================================================

\* fix.detected: none -> needs_fix
FixDetectedFromNone ==
    /\ state = "none"
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* fix.detected: needs_merge -> needs_fix
FixDetectedFromNeedsMerge ==
    /\ state = "needs_merge"
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* fix.detected: failed -> needs_fix (guarded: recovery_attempts_lt_max)
FixDetectedFromFailed ==
    /\ state = "failed"
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "needs_fix"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ UNCHANGED <<mergeAttempts, kanban>>

\* fix.started: needs_fix -> fixing
FixStarted ==
    /\ state = "needs_fix"
    /\ state' = "fixing"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* fix.pass: fixing -> needs_merge (chains through fix_completed, atomic)
\* Effect: inc_merge_attempts
FixPass ==
    /\ state = "fixing"
    /\ state' = "needs_merge"
    /\ mergeAttempts' = mergeAttempts + 1
    /\ UNCHANGED <<recoveryAttempts, kanban>>

\* fix.skip: fixing -> needs_merge (chains through fix_completed, atomic)
FixSkip ==
    /\ state = "fixing"
    /\ state' = "needs_merge"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* fix.partial: fixing -> needs_fix (retry)
FixPartial ==
    /\ state = "fixing"
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* fix.fail: fixing -> failed, effect: check_permanent
FixFail ==
    /\ state = "fixing"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* fix.timeout: fixing -> needs_fix
FixTimeout ==
    /\ state = "fixing"
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* fix.already_merged: needs_fix -> merged, kanban "x"
FixAlreadyMerged ==
    /\ state = "needs_fix"
    /\ state' = "merged"
    /\ kanban' = "x"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* =========================================================================
\* Actions - Merge Cycle
\* =========================================================================

\* merge.start: needs_merge -> merging (guarded: merge_attempts_lt_max)
\* Effect: inc_merge_attempts
MergeStartGuarded ==
    /\ state = "needs_merge"
    /\ mergeAttempts < MAX_MERGE_ATTEMPTS
    /\ state' = "merging"
    /\ mergeAttempts' = mergeAttempts + 1
    /\ UNCHANGED <<recoveryAttempts, kanban>>

\* merge.start: needs_merge -> failed (fallback when guard fails)
\* Effect: check_permanent
MergeStartFallback ==
    /\ state = "needs_merge"
    /\ mergeAttempts >= MAX_MERGE_ATTEMPTS
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* merge.succeeded: merging -> merged, kanban "x"
MergeSucceeded ==
    /\ state = "merging"
    /\ state' = "merged"
    /\ kanban' = "x"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* merge.already_merged: merging -> merged, kanban "x"
MergeAlreadyMerged ==
    /\ state = "merging"
    /\ state' = "merged"
    /\ kanban' = "x"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* merge.conflict: merging -> merge_conflict
MergeConflict ==
    /\ state = "merging"
    /\ state' = "merge_conflict"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* merge.out_of_date: merging -> needs_merge (guarded: rebase_succeeded)
\* Modeled as nondeterministic boolean
MergeOutOfDateRebaseOk ==
    /\ state = "merging"
    /\ state' = "needs_merge"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* merge.out_of_date: merging -> failed (fallback: rebase failed)
\* Effect: check_permanent
MergeOutOfDateRebaseFail ==
    /\ state = "merging"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* merge.transient_fail: merging -> needs_merge (guarded: merge_attempts_lt_max)
MergeTransientFailRetry ==
    /\ state = "merging"
    /\ mergeAttempts < MAX_MERGE_ATTEMPTS
    /\ state' = "needs_merge"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* merge.transient_fail: merging -> failed (fallback)
\* Effect: check_permanent
MergeTransientFailAbort ==
    /\ state = "merging"
    /\ mergeAttempts >= MAX_MERGE_ATTEMPTS
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* merge.hard_fail: merging -> failed
\* Effect: check_permanent
MergeHardFail ==
    /\ state = "merging"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* merge.pr_merged: * -> merged, kanban "x" (wildcard from)
MergePrMerged ==
    /\ state \notin {"merged"}
    /\ state' = "merged"
    /\ kanban' = "x"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* =========================================================================
\* Actions - Conflict Resolution
\* =========================================================================

\* conflict.needs_resolve: merge_conflict -> needs_resolve (guarded)
ConflictNeedsResolveGuarded ==
    /\ state = "merge_conflict"
    /\ mergeAttempts < MAX_MERGE_ATTEMPTS
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* conflict.needs_resolve: merge_conflict -> failed (fallback)
\* Effect: check_permanent
ConflictNeedsResolveFallback ==
    /\ state = "merge_conflict"
    /\ mergeAttempts >= MAX_MERGE_ATTEMPTS
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* conflict.needs_multi: merge_conflict -> needs_multi_resolve
ConflictNeedsMulti ==
    /\ state = "merge_conflict"
    /\ state' = "needs_multi_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* =========================================================================
\* Actions - Resolve Cycle
\* =========================================================================

\* resolve.startup_reset: resolving -> needs_resolve (effect: reset_merge)
ResolveStartupResetFromResolving ==
    /\ state = "resolving"
    /\ state' = "needs_resolve"
    /\ mergeAttempts' = 0
    /\ UNCHANGED <<recoveryAttempts, kanban>>

\* resolve.startup_reset: none -> needs_resolve
ResolveStartupResetFromNone ==
    /\ state = "none"
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* resolve.startup_reset: resolved is transient and skipped, but this
\* transition is from a state that in the JSON exists. Since we skip
\* "resolved" as transient, this transition is unreachable in our model.
\* Included for documentation completeness but guarded to be unreachable.

\* resolve.started: needs_resolve -> resolving
ResolveStartedFromNeedsResolve ==
    /\ state = "needs_resolve"
    /\ state' = "resolving"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* resolve.started: needs_multi_resolve -> resolving
ResolveStartedFromNeedsMulti ==
    /\ state = "needs_multi_resolve"
    /\ state' = "resolving"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* resolve.succeeded: resolving -> needs_merge (chains through resolved, atomic)
\* Effect: rm_conflict_queue (abstracted away)
ResolveSucceeded ==
    /\ state = "resolving"
    /\ state' = "needs_merge"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* resolve.fail: resolving -> failed
\* Effect: check_permanent
ResolveFailFromResolving ==
    /\ state = "resolving"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* resolve.fail: needs_resolve -> failed
\* Effect: check_permanent
ResolveFailFromNeedsResolve ==
    /\ state = "needs_resolve"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* resolve.fail: needs_multi_resolve -> failed
\* Effect: check_permanent
ResolveFailFromNeedsMulti ==
    /\ state = "needs_multi_resolve"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* resolve.timeout: resolving -> needs_resolve
ResolveTimeout ==
    /\ state = "resolving"
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* resolve.stuck_reset: resolving -> needs_resolve, effect: inc_merge_attempts
ResolveStuckReset ==
    /\ state = "resolving"
    /\ state' = "needs_resolve"
    /\ mergeAttempts' = mergeAttempts + 1
    /\ UNCHANGED <<recoveryAttempts, kanban>>

\* resolve.already_merged: needs_resolve -> merged, kanban "x"
ResolveAlreadyMergedFromNeedsResolve ==
    /\ state = "needs_resolve"
    /\ state' = "merged"
    /\ kanban' = "x"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* resolve.already_merged: needs_multi_resolve -> merged, kanban "x"
ResolveAlreadyMergedFromNeedsMulti ==
    /\ state = "needs_multi_resolve"
    /\ state' = "merged"
    /\ kanban' = "x"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* resolve.max_exceeded: needs_resolve -> failed
\* Effect: check_permanent
ResolveMaxExceededFromNeedsResolve ==
    /\ state = "needs_resolve"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* resolve.max_exceeded: needs_multi_resolve -> failed
\* Effect: check_permanent
ResolveMaxExceededFromNeedsMulti ==
    /\ state = "needs_multi_resolve"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* resolve.batch_failed: needs_multi_resolve -> needs_resolve
ResolveBatchFailedFromNeedsMulti ==
    /\ state = "needs_multi_resolve"
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* resolve.batch_failed: needs_resolve -> needs_resolve (no-op on state)
ResolveBatchFailedFromNeedsResolve ==
    /\ state = "needs_resolve"
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* =========================================================================
\* Actions - PR Events
\* =========================================================================

\* pr.conflict_detected: none -> needs_resolve
PrConflictFromNone ==
    /\ state = "none"
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* pr.conflict_detected: needs_merge -> needs_resolve
PrConflictFromNeedsMerge ==
    /\ state = "needs_merge"
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* pr.conflict_detected: needs_fix -> needs_resolve
PrConflictFromNeedsFix ==
    /\ state = "needs_fix"
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* pr.conflict_detected: failed -> needs_resolve (guarded: recovery_attempts_lt_max)
\* Effects: inc_recovery, reset_merge
PrConflictFromFailed ==
    /\ state = "failed"
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "needs_resolve"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ mergeAttempts' = 0
    /\ UNCHANGED kanban

\* pr.multi_conflict_detected: none -> needs_multi_resolve
PrMultiConflictFromNone ==
    /\ state = "none"
    /\ state' = "needs_multi_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* pr.multi_conflict_detected: needs_merge -> needs_multi_resolve
PrMultiConflictFromNeedsMerge ==
    /\ state = "needs_merge"
    /\ state' = "needs_multi_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* pr.multi_conflict_detected: needs_fix -> needs_multi_resolve
PrMultiConflictFromNeedsFix ==
    /\ state = "needs_fix"
    /\ state' = "needs_multi_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* pr.multi_conflict_detected: failed -> needs_multi_resolve (guarded)
\* Effects: inc_recovery, reset_merge
PrMultiConflictFromFailed ==
    /\ state = "failed"
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "needs_multi_resolve"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ mergeAttempts' = 0
    /\ UNCHANGED kanban

\* pr.comments_detected: none -> needs_fix
PrCommentsFromNone ==
    /\ state = "none"
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* pr.comments_detected: needs_merge -> needs_fix
PrCommentsFromNeedsMerge ==
    /\ state = "needs_merge"
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* pr.comments_detected: failed -> needs_fix (guarded: recovery_attempts_lt_max)
\* Effect: inc_recovery
PrCommentsFromFailed ==
    /\ state = "failed"
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "needs_fix"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ UNCHANGED <<mergeAttempts, kanban>>

\* pr.retrack: none -> needs_merge
PrRetrack ==
    /\ state = "none"
    /\ state' = "needs_merge"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* =========================================================================
\* Actions - Recovery
\* =========================================================================

\* recovery.to_resolve: failed -> needs_resolve (guarded)
\* Effects: inc_recovery, reset_merge
RecoveryToResolveGuarded ==
    /\ state = "failed"
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "needs_resolve"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ mergeAttempts' = 0
    /\ UNCHANGED kanban

\* recovery.to_resolve: failed -> failed (fallback), kanban "*"
\* Effect: check_permanent
RecoveryToResolveFallback ==
    /\ state = "failed"
    /\ recoveryAttempts >= MAX_RECOVERY_ATTEMPTS
    /\ state' = "failed"
    /\ kanban' = "*"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* recovery.to_fix: failed -> needs_fix (guarded)
\* Effect: inc_recovery
RecoveryToFixGuarded ==
    /\ state = "failed"
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "needs_fix"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ UNCHANGED <<mergeAttempts, kanban>>

\* recovery.to_fix: failed -> failed (fallback), kanban "*"
\* Effect: check_permanent
RecoveryToFixFallback ==
    /\ state = "failed"
    /\ recoveryAttempts >= MAX_RECOVERY_ATTEMPTS
    /\ state' = "failed"
    /\ kanban' = "*"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* user.resume: failed -> needs_merge, kanban "="
UserResume ==
    /\ state = "failed"
    /\ state' = "needs_merge"
    /\ kanban' = "="
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* permanent_failure: failed -> failed, kanban "*"
PermanentFailure ==
    /\ state = "failed"
    /\ state' = "failed"
    /\ kanban' = "*"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* =========================================================================
\* Actions - Startup Reset
\* =========================================================================

\* startup.reset: fixing -> needs_fix
StartupResetFixing ==
    /\ state = "fixing"
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>

\* startup.reset: merging -> needs_merge, effect: reset_merge
StartupResetMerging ==
    /\ state = "merging"
    /\ state' = "needs_merge"
    /\ mergeAttempts' = 0
    /\ UNCHANGED <<recoveryAttempts, kanban>>

\* =========================================================================
\* Actions - Resume Abort (wildcard)
\* =========================================================================

\* resume.abort: * -> failed, kanban "*"
ResumeAbort ==
    /\ state \notin {"failed"}
    /\ state' = "failed"
    /\ kanban' = "*"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* Also allow from failed (wildcard includes all states)
ResumeAbortFromFailed ==
    /\ state = "failed"
    /\ state' = "failed"
    /\ kanban' = "*"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>

\* =========================================================================
\* Next-state relation
\* =========================================================================

Next ==
    \* Worker spawn
    \/ WorkerSpawned
    \* Fix cycle
    \/ FixDetectedFromNone
    \/ FixDetectedFromNeedsMerge
    \/ FixDetectedFromFailed
    \/ FixStarted
    \/ FixPass
    \/ FixSkip
    \/ FixPartial
    \/ FixFail
    \/ FixTimeout
    \/ FixAlreadyMerged
    \* Merge cycle
    \/ MergeStartGuarded
    \/ MergeStartFallback
    \/ MergeSucceeded
    \/ MergeAlreadyMerged
    \/ MergeConflict
    \/ MergeOutOfDateRebaseOk
    \/ MergeOutOfDateRebaseFail
    \/ MergeTransientFailRetry
    \/ MergeTransientFailAbort
    \/ MergeHardFail
    \/ MergePrMerged
    \* Conflict resolution
    \/ ConflictNeedsResolveGuarded
    \/ ConflictNeedsResolveFallback
    \/ ConflictNeedsMulti
    \* Resolve cycle
    \/ ResolveStartupResetFromResolving
    \/ ResolveStartupResetFromNone
    \/ ResolveStartedFromNeedsResolve
    \/ ResolveStartedFromNeedsMulti
    \/ ResolveSucceeded
    \/ ResolveFailFromResolving
    \/ ResolveFailFromNeedsResolve
    \/ ResolveFailFromNeedsMulti
    \/ ResolveTimeout
    \/ ResolveStuckReset
    \/ ResolveAlreadyMergedFromNeedsResolve
    \/ ResolveAlreadyMergedFromNeedsMulti
    \/ ResolveMaxExceededFromNeedsResolve
    \/ ResolveMaxExceededFromNeedsMulti
    \/ ResolveBatchFailedFromNeedsMulti
    \/ ResolveBatchFailedFromNeedsResolve
    \* PR events
    \/ PrConflictFromNone
    \/ PrConflictFromNeedsMerge
    \/ PrConflictFromNeedsFix
    \/ PrConflictFromFailed
    \/ PrMultiConflictFromNone
    \/ PrMultiConflictFromNeedsMerge
    \/ PrMultiConflictFromNeedsFix
    \/ PrMultiConflictFromFailed
    \/ PrCommentsFromNone
    \/ PrCommentsFromNeedsMerge
    \/ PrCommentsFromFailed
    \/ PrRetrack
    \* Recovery
    \/ RecoveryToResolveGuarded
    \/ RecoveryToResolveFallback
    \/ RecoveryToFixGuarded
    \/ RecoveryToFixFallback
    \/ UserResume
    \/ PermanentFailure
    \* Startup reset
    \/ StartupResetFixing
    \/ StartupResetMerging
    \* Resume abort
    \/ ResumeAbort
    \/ ResumeAbortFromFailed

\* =========================================================================
\* Fairness (for liveness properties)
\* =========================================================================

Fairness ==
    /\ WF_vars(WorkerSpawned)
    /\ WF_vars(FixStarted)
    /\ WF_vars(MergeStartGuarded \/ MergeStartFallback)
    /\ WF_vars(MergeSucceeded \/ MergeHardFail \/ MergeConflict
               \/ MergeOutOfDateRebaseOk \/ MergeOutOfDateRebaseFail)
    /\ WF_vars(ConflictNeedsResolveGuarded \/ ConflictNeedsResolveFallback
               \/ ConflictNeedsMulti)
    /\ WF_vars(ResolveStartedFromNeedsResolve \/ ResolveStartedFromNeedsMulti)
    /\ WF_vars(ResolveSucceeded \/ ResolveFailFromResolving)
    /\ WF_vars(FixPass \/ FixFail \/ FixSkip \/ FixPartial \/ FixTimeout)

Spec == Init /\ [][Next]_vars /\ Fairness

\* =========================================================================
\* Safety Invariants
\* =========================================================================

\* TypeInvariant: all variables within declared domains
TypeInvariant ==
    /\ state \in AllStates
    /\ mergeAttempts \in 0..MAX_MERGE_ATTEMPTS + 1
    /\ recoveryAttempts \in 0..MAX_RECOVERY_ATTEMPTS + 1
    /\ kanban \in KanbanValues

\* BoundedCounters: counters never exceed their maximums by more than 1
\* (they can reach max and then a transition fires before the guard blocks)
BoundedCounters ==
    /\ mergeAttempts <= MAX_MERGE_ATTEMPTS + 1
    /\ recoveryAttempts <= MAX_RECOVERY_ATTEMPTS + 1

\* TransientStateInvariant: transient states are never observable
\* (fix_completed and resolved are skipped atomically via chains)
TransientStateInvariant ==
    /\ state /= "fix_completed"
    /\ state /= "resolved"

\* MergeConflictReachability: merge_conflict is only reachable from merging
\* (This is not an invariant per se, but validates the lifecycle structure.
\*  The only action that sets state to merge_conflict is MergeConflict,
\*  which requires state = "merging".)

\* KanbanConsistency: if merged, kanban must be "x"
KanbanMergedConsistency ==
    state = "merged" => kanban = "x"

\* KanbanFailedConsistency: if permanently failed (kanban "*"), state is failed
KanbanFailedConsistency ==
    kanban = "*" => state = "failed"

\* =========================================================================
\* Liveness Properties (require fairness)
\* =========================================================================

\* EventualTermination: every worker eventually reaches merged or failed
EventualTermination == <>(state \in TerminalStates)

=============================================================================
