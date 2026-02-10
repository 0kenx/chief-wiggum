--------------------------- MODULE WorkerLifecycle ---------------------------
(*
 * TLA+ formal model of Chief Wiggum's worker lifecycle state machine.
 *
 * Faithfully encodes every transition from config/worker-lifecycle.json.
 * Transient states (fix_completed, resolved) are skipped atomically --
 * chains collapse into a single transition. merge_conflict is modeled
 * as a real state since it persists until a conflict.* event fires.
 *
 * EFFECT-STATE MODELING (Quick Win #1):
 * Models side effects as explicit state variables to catch partial-effect
 * and crash-recovery bugs:
 *   - inConflictQueue: whether task is queued for conflict resolution
 *   - worktreeState: worktree lifecycle (absent/present/cleaning)
 *   - lastError: error category from last failure
 *
 * CRASH/RESTART MODELING (Quick Win #2):
 * Includes Crash action that can interrupt running states, leaving effects
 * partially applied. StartupReset actions model orchestrator restart recovery.
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
    kanban,
    \* === EFFECT-STATE VARIABLES (Quick Win #1) ===
    \* @type: Bool;
    inConflictQueue,       \* TRUE if task is in conflict resolution queue
    \* @type: Str;
    worktreeState,         \* "absent", "present", "cleaning"
    \* @type: Str;
    lastError,             \* "", "merge_conflict", "rebase_failed", "hard_fail"
    \* @type: Bool;
    githubSynced,          \* TRUE if GitHub issue status matches kanban
    \* === ENVIRONMENT STATE (Medium Term #1: Structured Nondeterminism) ===
    \* @type: Bool;
    baseMoved,             \* TRUE if upstream base has moved (causes out-of-date)
    \* @type: Bool;
    hasConflict            \* TRUE if merge would conflict (rebase cannot succeed)

\* @type: <<Str, Int, Int, Str, Bool, Str, Str, Bool, Bool, Bool>>;
vars == <<state, mergeAttempts, recoveryAttempts, kanban, inConflictQueue, worktreeState, lastError, githubSynced, baseMoved, hasConflict>>

\* =========================================================================
\* Type and state definitions
\* =========================================================================

AllStates == {
    "none", "needs_fix", "fixing", "needs_merge", "merging",
    "merge_conflict", "needs_resolve", "needs_multi_resolve",
    "resolving", "merged", "failed"
}

RunningStates == {"fixing", "merging", "resolving"}

TerminalStates == {"merged", "failed"}

KanbanValues == {" ", "=", "x", "*"}

WorktreeValues == {"absent", "present", "cleaning"}

ErrorValues == {"", "merge_conflict", "rebase_failed", "hard_fail"}

\* =========================================================================
\* Init and CInit
\* =========================================================================

Init ==
    /\ state = "none"
    /\ mergeAttempts = 0
    /\ recoveryAttempts = 0
    /\ kanban = " "
    /\ inConflictQueue = FALSE
    /\ worktreeState = "absent"
    /\ lastError = ""
    /\ githubSynced = TRUE
    /\ baseMoved = FALSE
    /\ hasConflict = FALSE

\* Apalache constant initialization (replaces .cfg)
CInit ==
    /\ MAX_MERGE_ATTEMPTS = 2
    /\ MAX_RECOVERY_ATTEMPTS = 1

\* Helper: unchanged environment variables
EnvVarsUnchanged == UNCHANGED <<baseMoved, hasConflict>>

\* Helper: unchanged effect-state variables
EffectVarsUnchanged == UNCHANGED <<inConflictQueue, worktreeState, lastError, githubSynced>>

\* Helper: unchanged effect-state AND environment variables
AllAuxUnchanged == EffectVarsUnchanged /\ EnvVarsUnchanged

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
\* Effect: creates worktree, marks github out of sync
WorkerSpawned ==
    /\ state = "none"
    /\ state' = "needs_merge"
    /\ kanban' = "="
    /\ worktreeState' = "present"
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, lastError>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Actions - Fix Cycle
\* =========================================================================

\* fix.detected: none -> needs_fix
FixDetectedFromNone ==
    /\ state = "none"
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* fix.detected: needs_merge -> needs_fix
FixDetectedFromNeedsMerge ==
    /\ state = "needs_merge"
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* fix.detected: failed -> needs_fix (guarded: recovery_attempts_lt_max)
\* kanban "=" (clear permanent failure marker on recovery)
FixDetectedFromFailed ==
    /\ state = "failed"
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "needs_fix"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ kanban' = "="
    /\ lastError' = ""
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* fix.started: needs_fix -> fixing
FixStarted ==
    /\ state = "needs_fix"
    /\ state' = "fixing"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* fix.pass: fixing -> needs_merge (guarded: merge_attempts_lt_max)
\* Chains through fix_completed, atomic. Effects: inc_merge_attempts, rm_conflict_queue
FixPassGuarded ==
    /\ state = "fixing"
    /\ mergeAttempts < MAX_MERGE_ATTEMPTS
    /\ state' = "needs_merge"
    /\ mergeAttempts' = mergeAttempts + 1
    /\ inConflictQueue' = FALSE
    /\ UNCHANGED <<recoveryAttempts, kanban, worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* fix.pass: fixing -> failed (fallback when merge budget exhausted)
\* Effect: check_permanent
FixPassFallback ==
    /\ state = "fixing"
    /\ mergeAttempts >= MAX_MERGE_ATTEMPTS
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* fix.skip: fixing -> needs_merge (chains through fix_completed, atomic)
\* Effect: rm_conflict_queue
FixSkip ==
    /\ state = "fixing"
    /\ state' = "needs_merge"
    /\ inConflictQueue' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* fix.partial: fixing -> needs_fix (retry)
FixPartial ==
    /\ state = "fixing"
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* fix.fail: fixing -> failed, effect: check_permanent
FixFail ==
    /\ state = "fixing"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* fix.timeout: fixing -> needs_fix
FixTimeout ==
    /\ state = "fixing"
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* fix.already_merged: needs_fix -> merged, kanban "x"
\* Effects: sync_github, cleanup_worktree
\* Clears error state since merge succeeded externally
FixAlreadyMerged ==
    /\ state = "needs_fix"
    /\ state' = "merged"
    /\ kanban' = "x"
    /\ githubSynced' = TRUE
    /\ worktreeState' = "cleaning"
    /\ inConflictQueue' = FALSE
    /\ lastError' = ""
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged

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
    /\ AllAuxUnchanged

\* merge.start: needs_merge -> failed (fallback when guard fails)
\* Effect: check_permanent
MergeStartFallback ==
    /\ state = "needs_merge"
    /\ mergeAttempts >= MAX_MERGE_ATTEMPTS
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* merge.succeeded: merging -> merged, kanban "x"
\* Effects: sync_github, cleanup_batch, cleanup_worktree, release_claim
MergeSucceeded ==
    /\ state = "merging"
    /\ state' = "merged"
    /\ kanban' = "x"
    /\ githubSynced' = TRUE
    /\ worktreeState' = "cleaning"
    /\ inConflictQueue' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, lastError>>
    /\ EnvVarsUnchanged

\* merge.already_merged: merging -> merged, kanban "x"
\* Effects: sync_github, cleanup_batch, cleanup_worktree, release_claim
MergeAlreadyMerged ==
    /\ state = "merging"
    /\ state' = "merged"
    /\ kanban' = "x"
    /\ githubSynced' = TRUE
    /\ worktreeState' = "cleaning"
    /\ inConflictQueue' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, lastError>>
    /\ EnvVarsUnchanged

\* merge.conflict: merging -> merge_conflict
\* Effects: set_error, add_conflict_queue
\* Structured nondeterminism: only fires when hasConflict is TRUE
MergeConflict ==
    /\ state = "merging"
    /\ hasConflict = TRUE
    /\ state' = "merge_conflict"
    /\ lastError' = "merge_conflict"
    /\ inConflictQueue' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, worktreeState, githubSynced>>
    /\ EnvVarsUnchanged

\* merge.out_of_date: merging -> needs_merge (guarded: rebase_succeeded)
\* Structured nondeterminism: requires baseMoved AND ~hasConflict (rebase can succeed)
MergeOutOfDateRebaseOk ==
    /\ state = "merging"
    /\ baseMoved = TRUE
    /\ hasConflict = FALSE
    /\ state' = "needs_merge"
    /\ baseMoved' = FALSE  \* rebase brings us up to date
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, hasConflict>>
    /\ EffectVarsUnchanged

\* merge.out_of_date: merging -> failed (fallback: rebase failed due to conflict)
\* Effects: set_error, check_permanent
\* Structured nondeterminism: requires baseMoved AND hasConflict
MergeOutOfDateRebaseFail ==
    /\ state = "merging"
    /\ baseMoved = TRUE
    /\ hasConflict = TRUE
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ lastError' = "rebase_failed"
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* merge.transient_fail: merging -> needs_merge (guarded: merge_attempts_lt_max)
MergeTransientFailRetry ==
    /\ state = "merging"
    /\ mergeAttempts < MAX_MERGE_ATTEMPTS
    /\ state' = "needs_merge"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* merge.transient_fail: merging -> failed (fallback)
\* Effects: set_error, check_permanent
MergeTransientFailAbort ==
    /\ state = "merging"
    /\ mergeAttempts >= MAX_MERGE_ATTEMPTS
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* merge.hard_fail: merging -> failed
\* Effects: set_error, check_permanent
MergeHardFail ==
    /\ state = "merging"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ lastError' = "hard_fail"
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* merge.pr_merged: * -> merged, kanban "x" (wildcard from)
\* Effects: sync_github, cleanup_batch, cleanup_worktree, release_claim
\* Clears error state since merge succeeded externally
MergePrMerged ==
    /\ state \notin {"merged"}
    /\ state' = "merged"
    /\ kanban' = "x"
    /\ githubSynced' = TRUE
    /\ worktreeState' = "cleaning"
    /\ inConflictQueue' = FALSE
    /\ lastError' = ""
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Actions - Conflict Resolution
\* =========================================================================

\* conflict.needs_resolve: merge_conflict -> needs_resolve (guarded)
ConflictNeedsResolveGuarded ==
    /\ state = "merge_conflict"
    /\ mergeAttempts < MAX_MERGE_ATTEMPTS
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* conflict.needs_resolve: merge_conflict -> failed (fallback)
\* Effect: check_permanent
ConflictNeedsResolveFallback ==
    /\ state = "merge_conflict"
    /\ mergeAttempts >= MAX_MERGE_ATTEMPTS
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* conflict.needs_multi: merge_conflict -> needs_multi_resolve
ConflictNeedsMulti ==
    /\ state = "merge_conflict"
    /\ state' = "needs_multi_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* =========================================================================
\* Actions - Resolve Cycle
\* =========================================================================

\* resolve.startup_reset: resolving -> needs_resolve (effect: reset_merge)
ResolveStartupResetFromResolving ==
    /\ state = "resolving"
    /\ state' = "needs_resolve"
    /\ mergeAttempts' = 0
    /\ UNCHANGED <<recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* resolve.startup_reset: none -> needs_resolve
ResolveStartupResetFromNone ==
    /\ state = "none"
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* resolve.startup_reset: resolved is transient and skipped, but this
\* transition is from a state that in the JSON exists. Since we skip
\* "resolved" as transient, this transition is unreachable in our model.
\* Included for documentation completeness but guarded to be unreachable.

\* resolve.started: needs_resolve -> resolving
ResolveStartedFromNeedsResolve ==
    /\ state = "needs_resolve"
    /\ state' = "resolving"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* resolve.started: needs_multi_resolve -> resolving
ResolveStartedFromNeedsMulti ==
    /\ state = "needs_multi_resolve"
    /\ state' = "resolving"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* resolve.started: resolving -> null (idempotent re-entry, no state change)
ResolveStartedFromResolving ==
    /\ state = "resolving"
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* resolve.succeeded: resolving -> needs_merge (chains through resolved, atomic)
\* Effects: rm_conflict_queue, clear_error
ResolveSucceeded ==
    /\ state = "resolving"
    /\ state' = "needs_merge"
    /\ inConflictQueue' = FALSE
    /\ lastError' = ""
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, worktreeState, githubSynced>>
    /\ EnvVarsUnchanged

\* resolve.fail: resolving -> failed
\* Effect: check_permanent
ResolveFailFromResolving ==
    /\ state = "resolving"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* resolve.fail: needs_resolve -> failed
\* Effect: check_permanent
ResolveFailFromNeedsResolve ==
    /\ state = "needs_resolve"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* resolve.fail: needs_multi_resolve -> failed
\* Effect: check_permanent
ResolveFailFromNeedsMulti ==
    /\ state = "needs_multi_resolve"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* resolve.timeout: resolving -> needs_resolve
ResolveTimeout ==
    /\ state = "resolving"
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* resolve.stuck_reset: resolving -> needs_resolve (guarded: merge_attempts_lt_max)
\* Effect: inc_merge_attempts
ResolveStuckResetGuarded ==
    /\ state = "resolving"
    /\ mergeAttempts < MAX_MERGE_ATTEMPTS
    /\ state' = "needs_resolve"
    /\ mergeAttempts' = mergeAttempts + 1
    /\ UNCHANGED <<recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* resolve.stuck_reset: resolving -> failed (fallback)
\* Effect: check_permanent
ResolveStuckResetFallback ==
    /\ state = "resolving"
    /\ mergeAttempts >= MAX_MERGE_ATTEMPTS
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* resolve.already_merged: needs_resolve -> merged, kanban "x"
\* Effects: sync_github, cleanup_worktree
\* Clears error state since merge succeeded externally
ResolveAlreadyMergedFromNeedsResolve ==
    /\ state = "needs_resolve"
    /\ state' = "merged"
    /\ kanban' = "x"
    /\ githubSynced' = TRUE
    /\ worktreeState' = "cleaning"
    /\ inConflictQueue' = FALSE
    /\ lastError' = ""
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged

\* resolve.already_merged: needs_multi_resolve -> merged, kanban "x"
\* Effects: sync_github, cleanup_worktree
\* Clears error state since merge succeeded externally
ResolveAlreadyMergedFromNeedsMulti ==
    /\ state = "needs_multi_resolve"
    /\ state' = "merged"
    /\ kanban' = "x"
    /\ githubSynced' = TRUE
    /\ worktreeState' = "cleaning"
    /\ inConflictQueue' = FALSE
    /\ lastError' = ""
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts>>
    /\ EnvVarsUnchanged

\* resolve.max_exceeded: needs_resolve -> failed
\* Effect: check_permanent
ResolveMaxExceededFromNeedsResolve ==
    /\ state = "needs_resolve"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* resolve.max_exceeded: needs_multi_resolve -> failed
\* Effect: check_permanent
ResolveMaxExceededFromNeedsMulti ==
    /\ state = "needs_multi_resolve"
    /\ state' = "failed"
    /\ kanban' = KanbanAfterCheckPermanent(kanban)
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* resolve.batch_failed: needs_multi_resolve -> needs_resolve
ResolveBatchFailedFromNeedsMulti ==
    /\ state = "needs_multi_resolve"
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* resolve.batch_failed: needs_resolve -> needs_resolve (no-op on state)
ResolveBatchFailedFromNeedsResolve ==
    /\ state = "needs_resolve"
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* =========================================================================
\* Actions - PR Events
\* =========================================================================

\* pr.conflict_detected: merge_conflict -> needs_resolve (redundant detection, no effects)
PrConflictFromMergeConflict ==
    /\ state = "merge_conflict"
    /\ state' = "needs_resolve"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* pr.conflict_detected: none -> needs_resolve
\* Effect: add_conflict_queue
PrConflictFromNone ==
    /\ state = "none"
    /\ state' = "needs_resolve"
    /\ inConflictQueue' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* pr.conflict_detected: needs_merge -> needs_resolve
\* Effect: add_conflict_queue
PrConflictFromNeedsMerge ==
    /\ state = "needs_merge"
    /\ state' = "needs_resolve"
    /\ inConflictQueue' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* pr.conflict_detected: needs_fix -> needs_resolve
\* Effect: add_conflict_queue
PrConflictFromNeedsFix ==
    /\ state = "needs_fix"
    /\ state' = "needs_resolve"
    /\ inConflictQueue' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* pr.conflict_detected: failed -> needs_resolve (guarded: recovery_attempts_lt_max)
\* Effects: inc_recovery, reset_merge, add_conflict_queue. kanban "="
PrConflictFromFailed ==
    /\ state = "failed"
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "needs_resolve"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ mergeAttempts' = 0
    /\ kanban' = "="
    /\ inConflictQueue' = TRUE
    /\ lastError' = ""
    /\ githubSynced' = FALSE
    /\ UNCHANGED worktreeState
    /\ EnvVarsUnchanged

\* pr.multi_conflict_detected: none -> needs_multi_resolve
\* Effect: add_conflict_queue
PrMultiConflictFromNone ==
    /\ state = "none"
    /\ state' = "needs_multi_resolve"
    /\ inConflictQueue' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* pr.multi_conflict_detected: needs_merge -> needs_multi_resolve
\* Effect: add_conflict_queue
PrMultiConflictFromNeedsMerge ==
    /\ state = "needs_merge"
    /\ state' = "needs_multi_resolve"
    /\ inConflictQueue' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* pr.multi_conflict_detected: needs_fix -> needs_multi_resolve
\* Effect: add_conflict_queue
PrMultiConflictFromNeedsFix ==
    /\ state = "needs_fix"
    /\ state' = "needs_multi_resolve"
    /\ inConflictQueue' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban, worktreeState, lastError, githubSynced>>
    /\ EnvVarsUnchanged

\* pr.multi_conflict_detected: failed -> needs_multi_resolve (guarded)
\* Effects: inc_recovery, reset_merge, add_conflict_queue. kanban "="
PrMultiConflictFromFailed ==
    /\ state = "failed"
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "needs_multi_resolve"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ mergeAttempts' = 0
    /\ kanban' = "="
    /\ inConflictQueue' = TRUE
    /\ lastError' = ""
    /\ githubSynced' = FALSE
    /\ UNCHANGED worktreeState
    /\ EnvVarsUnchanged

\* pr.comments_detected: none -> needs_fix
PrCommentsFromNone ==
    /\ state = "none"
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* pr.comments_detected: needs_merge -> needs_fix
PrCommentsFromNeedsMerge ==
    /\ state = "needs_merge"
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* pr.comments_detected: failed -> needs_fix (guarded: recovery_attempts_lt_max)
\* Effect: inc_recovery. kanban "="
PrCommentsFromFailed ==
    /\ state = "failed"
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "needs_fix"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ kanban' = "="
    /\ lastError' = ""
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* pr.retrack: none -> needs_merge
PrRetrack ==
    /\ state = "none"
    /\ state' = "needs_merge"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* =========================================================================
\* Actions - Recovery
\* =========================================================================

\* recovery.to_resolve: failed -> needs_resolve (guarded)
\* Effects: inc_recovery, reset_merge. kanban "="
RecoveryToResolveGuarded ==
    /\ state = "failed"
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "needs_resolve"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ mergeAttempts' = 0
    /\ kanban' = "="
    /\ lastError' = ""
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* recovery.to_resolve: failed -> failed (fallback), kanban "*"
\* Effect: check_permanent
RecoveryToResolveFallback ==
    /\ state = "failed"
    /\ recoveryAttempts >= MAX_RECOVERY_ATTEMPTS
    /\ state' = "failed"
    /\ kanban' = "*"
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* recovery.to_fix: failed -> needs_fix (guarded)
\* Effect: inc_recovery. kanban "="
RecoveryToFixGuarded ==
    /\ state = "failed"
    /\ recoveryAttempts < MAX_RECOVERY_ATTEMPTS
    /\ state' = "needs_fix"
    /\ recoveryAttempts' = recoveryAttempts + 1
    /\ kanban' = "="
    /\ lastError' = ""
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, inConflictQueue, worktreeState>>
    /\ EnvVarsUnchanged

\* recovery.to_fix: failed -> failed (fallback), kanban "*"
\* Effect: check_permanent
RecoveryToFixFallback ==
    /\ state = "failed"
    /\ recoveryAttempts >= MAX_RECOVERY_ATTEMPTS
    /\ state' = "failed"
    /\ kanban' = "*"
    /\ githubSynced' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* user.resume: failed -> needs_merge, kanban "="
\* Effect: rm_conflict_queue
UserResume ==
    /\ state = "failed"
    /\ state' = "needs_merge"
    /\ kanban' = "="
    /\ lastError' = ""
    /\ githubSynced' = FALSE
    /\ inConflictQueue' = FALSE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, worktreeState>>
    /\ EnvVarsUnchanged

\* permanent_failure: failed -> failed, kanban "*"
\* Effect: sync_github
PermanentFailure ==
    /\ state = "failed"
    /\ state' = "failed"
    /\ kanban' = "*"
    /\ githubSynced' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Actions - Startup Reset (Quick Win #2: Crash Recovery)
\* =========================================================================

\* startup.reset: fixing -> needs_fix
StartupResetFixing ==
    /\ state = "fixing"
    /\ state' = "needs_fix"
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* startup.reset: merging -> needs_merge, effect: reset_merge
StartupResetMerging ==
    /\ state = "merging"
    /\ state' = "needs_merge"
    /\ mergeAttempts' = 0
    /\ UNCHANGED <<recoveryAttempts, kanban>>
    /\ AllAuxUnchanged

\* =========================================================================
\* Actions - Crash (Quick Win #2)
\* Models process crash during a running state, leaving effects partial.
\* After crash, orchestrator restart will trigger startup.reset events.
\* =========================================================================

\* Crash while fixing: state unchanged, but effects may be partial
\* (e.g., git changes applied but not committed)
CrashWhileFixing ==
    /\ state = "fixing"
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban>>
    /\ EnvVarsUnchanged
    \* Effects can be partially applied - nondeterministic effect-state
    /\ githubSynced' \in {TRUE, FALSE}
    /\ UNCHANGED <<inConflictQueue, worktreeState, lastError>>

\* Crash while merging: state unchanged, effects may be partial
\* (e.g., merge attempt counted but merge not completed)
CrashWhileMerging ==
    /\ state = "merging"
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban>>
    /\ EnvVarsUnchanged
    /\ githubSynced' \in {TRUE, FALSE}
    /\ UNCHANGED <<inConflictQueue, worktreeState, lastError>>

\* Crash while resolving: state unchanged, effects may be partial
CrashWhileResolving ==
    /\ state = "resolving"
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban>>
    /\ EnvVarsUnchanged
    /\ githubSynced' \in {TRUE, FALSE}
    /\ inConflictQueue' \in {TRUE, FALSE}
    /\ UNCHANGED <<worktreeState, lastError>>

\* =========================================================================
\* Actions - Resume Abort (wildcard)
\* =========================================================================

\* resume.abort: * -> failed, kanban "*"
\* Effect: sync_github
ResumeAbort ==
    /\ state \notin {"failed"}
    /\ state' = "failed"
    /\ kanban' = "*"
    /\ githubSynced' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* Also allow from failed (wildcard includes all states)
ResumeAbortFromFailed ==
    /\ state = "failed"
    /\ state' = "failed"
    /\ kanban' = "*"
    /\ githubSynced' = TRUE
    /\ UNCHANGED <<mergeAttempts, recoveryAttempts, inConflictQueue, worktreeState, lastError>>
    /\ EnvVarsUnchanged

\* =========================================================================
\* Actions - Environment Changes (Medium Term #1: Structured Nondeterminism)
\* Models external events that change the merge environment
\* =========================================================================

\* Upstream base moves (e.g., another PR merged to main)
EnvBaseMoved ==
    /\ baseMoved = FALSE
    /\ baseMoved' = TRUE
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban, inConflictQueue, 
                   worktreeState, lastError, githubSynced, hasConflict>>

\* A conflict appears (e.g., concurrent changes to same files)
EnvConflictAppears ==
    /\ hasConflict = FALSE
    /\ hasConflict' = TRUE
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban, inConflictQueue,
                   worktreeState, lastError, githubSynced, baseMoved>>

\* Conflict is resolved externally (e.g., blocking PR merged, files no longer overlap)
EnvConflictResolved ==
    /\ hasConflict = TRUE
    /\ hasConflict' = FALSE
    /\ UNCHANGED <<state, mergeAttempts, recoveryAttempts, kanban, inConflictQueue,
                   worktreeState, lastError, githubSynced, baseMoved>>

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
    \/ FixPassGuarded
    \/ FixPassFallback
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
    \/ ResolveStuckResetGuarded
    \/ ResolveStuckResetFallback
    \/ ResolveAlreadyMergedFromNeedsResolve
    \/ ResolveAlreadyMergedFromNeedsMulti
    \/ ResolveMaxExceededFromNeedsResolve
    \/ ResolveMaxExceededFromNeedsMulti
    \/ ResolveBatchFailedFromNeedsMulti
    \/ ResolveBatchFailedFromNeedsResolve
    \/ ResolveStartedFromResolving
    \* PR events
    \/ PrConflictFromMergeConflict
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
    \* Crash (Quick Win #2)
    \/ CrashWhileFixing
    \/ CrashWhileMerging
    \/ CrashWhileResolving
    \* Resume abort
    \/ ResumeAbort
    \/ ResumeAbortFromFailed
    \* Environment changes (Medium Term #1: Structured Nondeterminism)
    \/ EnvBaseMoved
    \/ EnvConflictAppears
    \/ EnvConflictResolved

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
    /\ WF_vars(FixPassGuarded \/ FixPassFallback \/ FixFail \/ FixSkip \/ FixPartial \/ FixTimeout)

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
    /\ inConflictQueue \in BOOLEAN
    /\ worktreeState \in WorktreeValues
    /\ lastError \in ErrorValues
    /\ githubSynced \in BOOLEAN
    /\ baseMoved \in BOOLEAN
    /\ hasConflict \in BOOLEAN

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
\* Cross-Module Invariants (Quick Win #4)
\* These validate consistency between effect-state and lifecycle state
\* =========================================================================

\* ConflictQueueConsistency: if in conflict queue, state must be conflict-related
\* Exception: crash can leave inConflictQueue TRUE with state unchanged
\* Also, recovery from failed while in conflict queue can go to needs_fix
ConflictQueueConsistency ==
    inConflictQueue => state \in {"merge_conflict", "needs_resolve",
                                   "needs_multi_resolve", "resolving",
                                   "fixing", "merging", "failed", "needs_fix"}

\* WorktreeStateConsistency: worktree should be present when worker is active
WorktreeStateConsistency ==
    /\ (state = "none" /\ worktreeState = "absent") \/
       (state \in {"merged"} /\ worktreeState \in {"absent", "cleaning"}) \/
       (state \notin {"none", "merged"})

\* ErrorStateConsistency: lastError reflects the failure mode
ErrorStateConsistency ==
    /\ (lastError = "merge_conflict" => 
        state \in {"merge_conflict", "needs_resolve", "needs_multi_resolve", 
                   "resolving", "failed", "merging"})
    /\ (lastError = "rebase_failed" => state = "failed")
    /\ (lastError = "hard_fail" => state = "failed")

\* MergedCleanupConsistency: merged state should trigger cleanup
\* (worktree should be cleaning or absent when merged)
MergedCleanupConsistency ==
    state = "merged" => worktreeState \in {"absent", "cleaning"}

\* ConflictQueueClearedOnResolve: after successful resolution, queue is cleared
\* (This is enforced by ResolveSucceeded setting inConflictQueue = FALSE)
\* Invariant: if state returned to needs_merge from resolving, queue should be empty
\* Note: Not a strict invariant due to crash semantics, but useful for checking.

\* =========================================================================
\* Liveness Properties (require fairness)
\* =========================================================================

\* EventualTermination: every worker eventually reaches merged or failed
\* NOTE: Requires fairness (WF) to hold. Apalache --temporal does not enforce
\* fairness ("Handling fairness is not supported yet!"), so this property
\* can only be verified with TLC. Kept here for documentation and TLC use.
EventualTermination == <>(state \in TerminalStates)

=============================================================================
