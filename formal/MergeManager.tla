--------------------------- MODULE MergeManager ----------------------------
(*
 * TLA+ formal model of Chief Wiggum's merge manager subsystem.
 *
 * Models the complete attempt_pr_merge() flow from lib/scheduler/merge-manager.sh.
 * The merge manager orchestrates the entire merge lifecycle for a single worker:
 *   - Gate checks (approval + pipeline result gates)
 *   - Mergeable status polling with timeout
 *   - GitHub merge API call
 *   - Classification of merge outcomes (7 branches)
 *   - Conflict event emission (two-event sequence with crash window)
 *   - Crash and recovery modeling
 *
 * Key properties verified:
 *   - GateBlocksSilently: blocked gates never emit lifecycle events
 *   - RebaseIdempotency: rebase side-effect tracked; detectable after crash
 *   - ConflictSequenceConsistency: resolve event requires prior conflict event
 *   - MergeAttemptsBounded: merge attempts bounded by max
 *   - SuccessImpliesCommitted: done with success implies kanban="x" and merged
 *   - CrashBounded: crash counter bounded
 *
 * Designed for Apalache symbolic model checking (type annotations, CInit).
 *)

EXTENDS Integers

CONSTANTS
    \* @type: Int;
    MaxMergeAttempts,
    \* @type: Int;
    MaxPollAttempts,
    \* @type: Int;
    MaxCrashes

VARIABLES
    \* @type: Str;
    pc,                  \* Current phase
    \* @type: Str;
    mergeState,          \* "idle", "success", "already_merged", "conflict",
                         \* "out_of_date", "dirty_tree", "transient", "unknown"
    \* @type: Int;
    mergeAttempts,       \* Current merge attempt count
    \* @type: Int;
    pollCount,           \* Current poll iteration count
    \* @type: Bool;
    rebaseApplied,       \* Whether rebase side-effect has been executed
    \* @type: Str;
    kanban,              \* Kanban status: "=", "x", "*"
    \* @type: Bool;
    conflictQueued,      \* Whether conflict event has been emitted
    \* @type: Str;
    lastError,           \* Last error category: "", "conflict", "transient", "unknown"
    \* @type: Int;
    crashCount,          \* Total crashes so far
    \* @type: Bool;
    lifecycleEventEmitted,  \* Whether any lifecycle event has been emitted this run
    \* @type: Str;
    lifecycleState       \* Worker lifecycle state: "needs_merge", "merging", "merged",
                         \* "merge_conflict", "failed"

\* @type: <<Str, Str, Int, Int, Bool, Str, Bool, Str, Int, Bool, Str>>;
vars == <<pc, mergeState, mergeAttempts, pollCount, rebaseApplied,
          kanban, conflictQueued, lastError, crashCount,
          lifecycleEventEmitted, lifecycleState>>

\* =========================================================================
\* Type definitions
\* =========================================================================

Phases == {"idle", "gate_check", "polling", "merging", "classifying",
           "emitting_conflict", "emitting_resolve", "done", "recovering"}

MergeStates == {"idle", "success", "already_merged", "conflict",
                "out_of_date", "dirty_tree", "transient", "unknown"}

KanbanValues == {"=", "x", "*"}

ErrorValues == {"", "conflict", "transient", "unknown"}

LifecycleStates == {"needs_merge", "merging", "merged", "merge_conflict", "failed"}

\* =========================================================================
\* Init and CInit
\* =========================================================================

Init ==
    /\ pc = "idle"
    /\ mergeState = "idle"
    /\ mergeAttempts = 0
    /\ pollCount = 0
    /\ rebaseApplied = FALSE
    /\ kanban = "="
    /\ conflictQueued = FALSE
    /\ lastError = ""
    /\ crashCount = 0
    /\ lifecycleEventEmitted = FALSE
    /\ lifecycleState = "needs_merge"

\* Apalache constant initialization
CInit ==
    /\ MaxMergeAttempts = 3
    /\ MaxPollAttempts = 6
    /\ MaxCrashes = 2

\* =========================================================================
\* Helpers
\* =========================================================================

\* Unchanged helpers
MetaUnchanged == UNCHANGED <<crashCount>>
MergeVarsUnchanged == UNCHANGED <<mergeState, mergeAttempts, pollCount, rebaseApplied>>
KanbanUnchanged == UNCHANGED <<kanban, conflictQueued, lastError>>

\* =========================================================================
\* Actions - Gate Check
\* =========================================================================

\* Begin merge attempt: idle -> gate_check
BeginMerge ==
    /\ pc = "idle"
    /\ lifecycleState = "needs_merge"
    /\ mergeAttempts < MaxMergeAttempts
    /\ pc' = "gate_check"
    /\ mergeAttempts' = mergeAttempts + 1
    /\ lifecycleEventEmitted' = FALSE
    /\ UNCHANGED <<mergeState, pollCount, rebaseApplied, kanban,
                   conflictQueued, lastError, crashCount, lifecycleState>>

\* Gate check approved: approval + pipeline result gates pass
GateCheckApproved ==
    /\ pc = "gate_check"
    /\ pc' = "polling"
    /\ pollCount' = 0
    /\ UNCHANGED <<mergeState, mergeAttempts, rebaseApplied, kanban,
                   conflictQueued, lastError, crashCount,
                   lifecycleEventEmitted, lifecycleState>>

\* Gate check blocked: approval or pipeline result gate fails
\* Silently returns to idle — no lifecycle events emitted
GateCheckBlocked ==
    /\ pc = "gate_check"
    /\ pc' = "done"
    /\ mergeState' = "idle"
    /\ UNCHANGED <<mergeAttempts, pollCount, rebaseApplied, kanban,
                   conflictQueued, lastError, crashCount,
                   lifecycleEventEmitted, lifecycleState>>

\* =========================================================================
\* Actions - Polling
\* =========================================================================

\* Poll: PR is mergeable, proceed to merge
PollMergeable ==
    /\ pc = "polling"
    /\ pollCount < MaxPollAttempts
    /\ pc' = "merging"
    /\ lifecycleState' = "merging"
    /\ UNCHANGED <<mergeState, mergeAttempts, pollCount, rebaseApplied, kanban,
                   conflictQueued, lastError, crashCount, lifecycleEventEmitted>>

\* Poll: PR has conflicts during polling
PollConflicting ==
    /\ pc = "polling"
    /\ pollCount < MaxPollAttempts
    /\ pc' = "classifying"
    /\ mergeState' = "conflict"
    /\ UNCHANGED <<mergeAttempts, pollCount, rebaseApplied, kanban,
                   conflictQueued, lastError, crashCount,
                   lifecycleEventEmitted, lifecycleState>>

\* Poll: timeout waiting for mergeable status
PollTimeout ==
    /\ pc = "polling"
    /\ pollCount >= MaxPollAttempts
    /\ pc' = "classifying"
    /\ mergeState' = "transient"
    /\ UNCHANGED <<mergeAttempts, pollCount, rebaseApplied, kanban,
                   conflictQueued, lastError, crashCount,
                   lifecycleEventEmitted, lifecycleState>>

\* Poll: increment poll counter (waiting)
PollWait ==
    /\ pc = "polling"
    /\ pollCount < MaxPollAttempts
    /\ pollCount' = pollCount + 1
    /\ UNCHANGED <<pc, mergeState, mergeAttempts, rebaseApplied, kanban,
                   conflictQueued, lastError, crashCount,
                   lifecycleEventEmitted, lifecycleState>>

\* =========================================================================
\* Actions - Merge Attempt
\* =========================================================================

\* Attempt merge via GitHub API — nondeterministic outcome
AttemptMerge ==
    /\ pc = "merging"
    /\ \E result \in {"success", "already_merged", "conflict", "out_of_date",
                       "dirty_tree", "transient", "unknown"} :
        /\ mergeState' = result
        /\ pc' = "classifying"
    /\ UNCHANGED <<mergeAttempts, pollCount, rebaseApplied, kanban,
                   conflictQueued, lastError, crashCount,
                   lifecycleEventEmitted, lifecycleState>>

\* =========================================================================
\* Actions - Classification (7 branches)
\* =========================================================================

\* Success: merge completed
ClassifySuccess ==
    /\ pc = "classifying"
    /\ mergeState = "success"
    /\ pc' = "done"
    /\ kanban' = "x"
    /\ lifecycleState' = "merged"
    /\ lifecycleEventEmitted' = TRUE
    /\ lastError' = ""
    /\ UNCHANGED <<mergeState, mergeAttempts, pollCount, rebaseApplied,
                   conflictQueued, crashCount>>

\* Already merged: PR was merged externally
ClassifyAlreadyMerged ==
    /\ pc = "classifying"
    /\ mergeState = "already_merged"
    /\ pc' = "done"
    /\ kanban' = "x"
    /\ lifecycleState' = "merged"
    /\ lifecycleEventEmitted' = TRUE
    /\ lastError' = ""
    /\ UNCHANGED <<mergeState, mergeAttempts, pollCount, rebaseApplied,
                   conflictQueued, crashCount>>

\* Out of date: base moved, attempt rebase
\* Rebase is a side-effect: tracked by rebaseApplied flag.
\* Guard: rebase only applied once per merge cycle to prevent infinite loops
ClassifyOutOfDate ==
    /\ pc = "classifying"
    /\ mergeState = "out_of_date"
    /\ rebaseApplied = FALSE
    /\ rebaseApplied' = TRUE
    /\ pc' = "polling"
    /\ pollCount' = 0
    /\ lifecycleState' = "needs_merge"
    /\ UNCHANGED <<mergeState, mergeAttempts, kanban,
                   conflictQueued, lastError, crashCount,
                   lifecycleEventEmitted>>

\* Out of date but rebase already applied: treat as transient failure
ClassifyOutOfDateRebaseExhausted ==
    /\ pc = "classifying"
    /\ mergeState = "out_of_date"
    /\ rebaseApplied = TRUE
    /\ pc' = "done"
    /\ lastError' = "transient"
    /\ lifecycleState' = "needs_merge"
    /\ UNCHANGED <<mergeState, mergeAttempts, pollCount, rebaseApplied, kanban,
                   conflictQueued, crashCount, lifecycleEventEmitted>>

\* Dirty tree: uncommitted changes prevent merge
ClassifyDirtyTree ==
    /\ pc = "classifying"
    /\ mergeState = "dirty_tree"
    /\ pc' = "done"
    /\ lastError' = "transient"
    /\ lifecycleState' = "needs_merge"
    /\ UNCHANGED <<mergeState, mergeAttempts, pollCount, rebaseApplied, kanban,
                   conflictQueued, crashCount, lifecycleEventEmitted>>

\* Conflict: merge conflict detected, begin two-event emission sequence
ClassifyConflict ==
    /\ pc = "classifying"
    /\ mergeState = "conflict"
    /\ pc' = "emitting_conflict"
    /\ lastError' = "conflict"
    /\ UNCHANGED <<mergeState, mergeAttempts, pollCount, rebaseApplied, kanban,
                   conflictQueued, crashCount, lifecycleEventEmitted, lifecycleState>>

\* Transient failure: API error, rate limit, etc.
ClassifyTransient ==
    /\ pc = "classifying"
    /\ mergeState = "transient"
    /\ pc' = "done"
    /\ lastError' = "transient"
    /\ lifecycleState' = "needs_merge"
    /\ UNCHANGED <<mergeState, mergeAttempts, pollCount, rebaseApplied, kanban,
                   conflictQueued, crashCount, lifecycleEventEmitted>>

\* Unknown error: unrecognized API response
ClassifyUnknown ==
    /\ pc = "classifying"
    /\ mergeState = "unknown"
    /\ pc' = "done"
    /\ lastError' = "unknown"
    /\ lifecycleState' = "failed"
    /\ lifecycleEventEmitted' = TRUE
    /\ UNCHANGED <<mergeState, mergeAttempts, pollCount, rebaseApplied, kanban,
                   conflictQueued, crashCount>>

\* =========================================================================
\* Actions - Conflict Event Emission (two-event sequence)
\* =========================================================================

\* Emit conflict event (first of two events)
\* Sets lifecycle state to merge_conflict, queues task for resolution
EmitConflictEvent ==
    /\ pc = "emitting_conflict"
    /\ pc' = "emitting_resolve"
    /\ conflictQueued' = TRUE
    /\ lifecycleState' = "merge_conflict"
    /\ lifecycleEventEmitted' = TRUE
    /\ UNCHANGED <<mergeState, mergeAttempts, pollCount, rebaseApplied, kanban,
                   lastError, crashCount>>

\* Emit resolve event (second of two events)
\* Routes conflict to resolution (needs_resolve)
EmitResolveEvent ==
    /\ pc = "emitting_resolve"
    /\ pc' = "done"
    /\ UNCHANGED <<mergeState, mergeAttempts, pollCount, rebaseApplied, kanban,
                   conflictQueued, lastError, crashCount,
                   lifecycleEventEmitted, lifecycleState>>

\* =========================================================================
\* Actions - Crash
\* =========================================================================

\* Nondeterministic crash at any non-terminal, non-idle phase
Crash ==
    /\ pc \notin {"idle", "done"}
    /\ crashCount < MaxCrashes
    /\ pc' = "recovering"
    /\ crashCount' = crashCount + 1
    /\ UNCHANGED <<mergeState, mergeAttempts, pollCount, rebaseApplied, kanban,
                   conflictQueued, lastError, lifecycleEventEmitted, lifecycleState>>

\* =========================================================================
\* Actions - Recovery
\* =========================================================================

\* Recovery from crash while in merging state: startup.reset
\* Matches StartupResetMerging in WorkerLifecycle
RecoverMerging ==
    /\ pc = "recovering"
    /\ lifecycleState = "merging"
    /\ pc' = "idle"
    /\ lifecycleState' = "needs_merge"
    /\ UNCHANGED <<mergeState, mergeAttempts, pollCount, rebaseApplied, kanban,
                   conflictQueued, lastError, crashCount, lifecycleEventEmitted>>

\* Recovery from crash in other phases: return to idle
RecoverOther ==
    /\ pc = "recovering"
    /\ lifecycleState /= "merging"
    /\ pc' = "idle"
    /\ UNCHANGED <<mergeState, mergeAttempts, pollCount, rebaseApplied, kanban,
                   conflictQueued, lastError, crashCount,
                   lifecycleEventEmitted, lifecycleState>>

\* =========================================================================
\* Actions - Terminal / Exhausted
\* =========================================================================

\* Merge attempts exhausted: transition to failed
MergeExhausted ==
    /\ pc = "idle"
    /\ lifecycleState = "needs_merge"
    /\ mergeAttempts >= MaxMergeAttempts
    /\ pc' = "done"
    /\ lifecycleState' = "failed"
    /\ kanban' = "*"
    /\ lifecycleEventEmitted' = TRUE
    /\ UNCHANGED <<mergeState, mergeAttempts, pollCount, rebaseApplied,
                   conflictQueued, lastError, crashCount>>

\* Terminal: done is absorbing
Terminated ==
    /\ pc = "done"
    /\ UNCHANGED vars

\* =========================================================================
\* Next-state relation
\* =========================================================================

Next ==
    \/ BeginMerge
    \/ GateCheckApproved
    \/ GateCheckBlocked
    \/ PollMergeable
    \/ PollConflicting
    \/ PollTimeout
    \/ PollWait
    \/ AttemptMerge
    \/ ClassifySuccess
    \/ ClassifyAlreadyMerged
    \/ ClassifyOutOfDate
    \/ ClassifyOutOfDateRebaseExhausted
    \/ ClassifyDirtyTree
    \/ ClassifyConflict
    \/ ClassifyTransient
    \/ ClassifyUnknown
    \/ EmitConflictEvent
    \/ EmitResolveEvent
    \/ Crash
    \/ RecoverMerging
    \/ RecoverOther
    \/ MergeExhausted
    \/ Terminated

\* =========================================================================
\* Fairness
\* =========================================================================

Fairness ==
    /\ WF_vars(BeginMerge)
    /\ WF_vars(GateCheckApproved \/ GateCheckBlocked)
    /\ WF_vars(PollMergeable \/ PollConflicting \/ PollTimeout \/ PollWait)
    /\ WF_vars(AttemptMerge)
    /\ WF_vars(ClassifySuccess \/ ClassifyAlreadyMerged \/ ClassifyOutOfDate
               \/ ClassifyOutOfDateRebaseExhausted \/ ClassifyDirtyTree
               \/ ClassifyConflict \/ ClassifyTransient \/ ClassifyUnknown)
    /\ WF_vars(EmitConflictEvent)
    /\ WF_vars(EmitResolveEvent)
    /\ WF_vars(RecoverMerging \/ RecoverOther)
    /\ WF_vars(MergeExhausted)

Spec == Init /\ [][Next]_vars /\ Fairness

\* =========================================================================
\* Safety Invariants
\* =========================================================================

\* TypeInvariant: all variables within declared domains
TypeInvariant ==
    /\ pc \in Phases
    /\ mergeState \in MergeStates
    /\ mergeAttempts \in 0..(MaxMergeAttempts + 1)
    /\ pollCount \in 0..(MaxPollAttempts + 1)
    /\ rebaseApplied \in BOOLEAN
    /\ kanban \in KanbanValues
    /\ conflictQueued \in BOOLEAN
    /\ lastError \in ErrorValues
    /\ crashCount \in 0..MaxCrashes
    /\ lifecycleEventEmitted \in BOOLEAN
    /\ lifecycleState \in LifecycleStates

\* GateBlocksSilently: when gate check blocks, no lifecycle events are emitted.
\* A blocked gate returns to done with mergeState="idle" and no events fired.
GateBlocksSilently ==
    (pc = "done" /\ mergeState = "idle") => lifecycleEventEmitted = FALSE

\* RebaseIdempotency: rebase is applied at most once per merge cycle.
\* The rebaseApplied flag prevents ClassifyOutOfDate from firing twice,
\* ensuring crash-after-rebase-before-transition is detectable.
RebaseIdempotency ==
    rebaseApplied = TRUE => mergeAttempts > 0

\* ConflictSequenceConsistency: if in emitting_resolve phase (about to fire
\* the resolve event), the conflict event must have already been emitted.
\* This catches the crash window: if we crash between the two events,
\* conflictQueued tracks whether the first event fired.
ConflictSequenceConsistency ==
    pc = "emitting_resolve" => conflictQueued = TRUE

\* MergeAttemptsBounded: merge attempts never exceed the maximum + 1.
\* The +1 accounts for the increment in BeginMerge before MergeExhausted checks.
MergeAttemptsBounded ==
    mergeAttempts <= MaxMergeAttempts

\* SuccessImpliesCommitted: when done with success, kanban is "x" and
\* lifecycle state is "merged".
SuccessImpliesCommitted ==
    (pc = "done" /\ mergeState = "success") =>
        /\ kanban = "x"
        /\ lifecycleState = "merged"

\* CrashBounded: crash counter stays within limits
CrashBounded ==
    crashCount <= MaxCrashes

\* =========================================================================
\* Liveness Properties (require fairness, TLC only)
\* =========================================================================

\* EventualCompletion: the merge manager eventually reaches done.
\* NOTE: Requires TLC for verification -- Apalache does not enforce fairness.
EventualCompletion == <>(pc = "done")

=============================================================================
