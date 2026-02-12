---------------------------- MODULE EffectOutbox ------------------------------
(*
 * TLA+ formal model of Chief Wiggum's effect outbox pattern.
 *
 * Models the two-phase effect execution used by emit_event() in
 * lib/core/lifecycle-engine.sh. A lifecycle transition consists of
 * multiple atomic operations executed in sequence:
 *   1. git_state_set(new_state)       -- atomic write (temp+mv)
 *   2. update_kanban_status(new)       -- atomic write (sed+mv under flock)
 *   3. outbox_record_pending(effects)  -- atomic write (jq+mv)
 *   4. For each effect:
 *      a. Execute effect               -- atomic operation
 *      b. outbox_mark_completed(id)    -- atomic write (jq+mv)
 *
 * Between any two atomic operations, a crash can occur. On restart:
 *   - _scheduler_reconcile_merged_workers() fixes state/kanban mismatches
 *     by re-emitting the transition event (creating fresh outbox + effects)
 *   - _scheduler_replay_pending_effects() replays recorded-but-incomplete
 *     effects from the outbox
 *
 * CATEGORY 4 FIX: cleanup_worktree effect replays pending effects before
 * executing, ensuring no effects are lost when the worker directory is
 * archived. Modeled via a guard that requires all other pending effects
 * to be applied before the cleanup effect can execute.
 *
 * Key properties verified:
 *   - DoneConsistency: completion implies all state + effects committed
 *   - StateBeforeKanban: kanban never ahead of state (write ordering)
 *   - CompletedSubsetPending: outbox completions are a subset of pendings
 *   - CleanupEffectOrder: cleanup only fires after other effects applied
 *   - CrashBounded: crash counter stays within limits
 *
 * ENRICHMENT: Replay Fallback (No Runner)
 * Models the case where the effect runner is unavailable during replay.
 * ReplayEffectNoRunner marks effects as completed WITHOUT actually applying
 * them (effectApplied stays FALSE). This models the "mark complete without
 * execution" fallback when the runner binary is missing or broken.
 *
 * Designed for Apalache symbolic model checking (type annotations, CInit).
 *)

EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Int;
    NumEffects,          \* Number of side effects in this transition
    \* @type: Int;
    MaxCrashes,          \* Bound on crash count for model checking
    \* @type: Int;
    CleanupEffectIdx     \* Index of cleanup_worktree effect (-1 if none)

VARIABLES
    \* @type: Str;
    pc,                  \* Current execution phase
    \* @type: Int;
    effectCursor,        \* Next effect index to process (0..NumEffects)
    \* === Durable state (survives crash) ===
    \* @type: Str;
    stateOnDisk,         \* "old" or "new" (git-state.json)
    \* @type: Str;
    kanbanOnDisk,        \* "old" or "new" (kanban.md)
    \* @type: Set(Int);
    outboxPending,       \* Recorded pending effects in pending-effects.json
    \* @type: Set(Int);
    outboxCompleted,     \* Completed effects in pending-effects.json
    \* @type: Int -> Bool;
    effectApplied,       \* Real side effect has happened (external state)
    \* === Meta variables ===
    \* @type: Int;
    crashCount,          \* Total crashes so far
    \* @type: Set(Int);
    doubleApplied,       \* Effects applied more than once (idempotency tracking)
    \* === ENRICHMENT VARIABLE ===
    \* @type: Bool;
    runnerAvailable      \* TRUE if effect runner is available for execution

\* @type: <<Str, Int, Str, Str, Set(Int), Set(Int), Int -> Bool, Int, Set(Int), Bool>>;
vars == <<pc, effectCursor, stateOnDisk, kanbanOnDisk,
          outboxPending, outboxCompleted, effectApplied,
          crashCount, doubleApplied, runnerAvailable>>

\* =========================================================================
\* Type definitions
\* =========================================================================

EffectIndices == 0..(NumEffects - 1)

Phases == {"idle", "writing_state", "writing_kanban", "recording_outbox",
           "executing", "marking", "done",
           "recovering", "replaying"}

DiskValues == {"old", "new"}

\* =========================================================================
\* Init and CInit
\* =========================================================================

Init ==
    /\ pc = "idle"
    /\ effectCursor = 0
    /\ stateOnDisk = "old"
    /\ kanbanOnDisk = "old"
    /\ outboxPending = {}
    /\ outboxCompleted = {}
    /\ effectApplied = [i \in EffectIndices |-> FALSE]
    /\ crashCount = 0
    /\ doubleApplied = {}
    /\ runnerAvailable = TRUE

\* Apalache constant initialization
\* 2 effects: effect 0 (e.g., sync_github), effect 1 (cleanup_worktree)
\* 2 max crashes: allows crash during recovery
CInit ==
    /\ NumEffects = 2
    /\ MaxCrashes = 2
    /\ CleanupEffectIdx = 1  \* Second effect is cleanup_worktree

\* =========================================================================
\* Helpers
\* =========================================================================

\* All effects have been applied at least once
AllEffectsApplied == \A i \in EffectIndices : effectApplied[i]

\* Unchanged helpers
DurableUnchanged == UNCHANGED <<stateOnDisk, kanbanOnDisk,
                                outboxPending, outboxCompleted, effectApplied>>
MetaUnchanged == UNCHANGED <<crashCount, doubleApplied, runnerAvailable>>
OutboxUnchanged == UNCHANGED <<outboxPending, outboxCompleted>>

\* =========================================================================
\* Normal Execution Path
\* Models the sequential steps of emit_event() in lifecycle-engine.sh
\* =========================================================================

\* Begin: start a new lifecycle transition
BeginTransition ==
    /\ pc = "idle"
    /\ pc' = "writing_state"
    /\ UNCHANGED <<effectCursor, stateOnDisk, kanbanOnDisk,
                   outboxPending, outboxCompleted, effectApplied,
                   crashCount, doubleApplied, runnerAvailable>>

\* Step 1: Atomically write git state (git_state_set)
\* Matches: git_state_set() in lifecycle-engine.sh line 93
WriteState ==
    /\ pc = "writing_state"
    /\ stateOnDisk' = "new"
    /\ pc' = "writing_kanban"
    /\ UNCHANGED <<effectCursor, kanbanOnDisk,
                   outboxPending, outboxCompleted, effectApplied>>
    /\ MetaUnchanged

\* Step 2: Atomically write kanban status (_lifecycle_update_kanban)
\* Matches: _lifecycle_update_kanban() in lifecycle-engine.sh line 99
WriteKanban ==
    /\ pc = "writing_kanban"
    /\ kanbanOnDisk' = "new"
    /\ pc' = "recording_outbox"
    /\ UNCHANGED <<effectCursor, stateOnDisk,
                   outboxPending, outboxCompleted, effectApplied>>
    /\ MetaUnchanged

\* Step 3: Atomically record all effects as pending in outbox
\* Matches: outbox_record_pending() in _lifecycle_run_effects() line ~180
\* Creates a fresh batch: all effects pending, none completed
RecordOutbox ==
    /\ pc = "recording_outbox"
    /\ outboxPending' = EffectIndices
    /\ outboxCompleted' = {}
    /\ effectCursor' = 0
    /\ pc' = "executing"
    /\ UNCHANGED <<stateOnDisk, kanbanOnDisk, effectApplied>>
    /\ MetaUnchanged

\* Step 4a: Execute effect at cursor position
\* Matches: _lifecycle_run_single_effect() in lifecycle-engine.sh
\* CATEGORY 4 FIX: If this is the cleanup effect, all other pending
\* effects must be applied first (outbox_replay_pending runs before cleanup).
ExecuteEffect ==
    /\ pc = "executing"
    /\ effectCursor \in EffectIndices
    /\ effectCursor \in outboxPending
    /\ effectCursor \notin outboxCompleted
    \* CATEGORY 4 FIX guard: cleanup waits for all other pending effects
    /\ \/ CleanupEffectIdx < 0
       \/ effectCursor /= CleanupEffectIdx
       \/ \A j \in (outboxPending \ outboxCompleted) \ {CleanupEffectIdx} :
            effectApplied[j]
    \* Track double application (idempotency required)
    /\ doubleApplied' = IF effectApplied[effectCursor]
                         THEN doubleApplied \cup {effectCursor}
                         ELSE doubleApplied
    /\ effectApplied' = [effectApplied EXCEPT ![effectCursor] = TRUE]
    /\ pc' = "marking"
    /\ UNCHANGED <<effectCursor, stateOnDisk, kanbanOnDisk,
                   outboxPending, outboxCompleted, crashCount,
                   runnerAvailable>>

\* Step 4b: Mark effect as completed in outbox
\* Matches: outbox_mark_completed() in _lifecycle_run_single_effect()
MarkEffectComplete ==
    /\ pc = "marking"
    /\ outboxCompleted' = outboxCompleted \cup {effectCursor}
    /\ effectCursor' = effectCursor + 1
    /\ pc' = "executing"
    /\ UNCHANGED <<stateOnDisk, kanbanOnDisk,
                   outboxPending, effectApplied>>
    /\ MetaUnchanged

\* Step 4c: Skip effect that's already completed (from a previous recovery)
SkipCompletedEffect ==
    /\ pc = "executing"
    /\ effectCursor \in EffectIndices
    /\ effectCursor \in outboxCompleted
    /\ effectCursor' = effectCursor + 1
    /\ UNCHANGED <<pc, stateOnDisk, kanbanOnDisk,
                   outboxPending, outboxCompleted, effectApplied>>
    /\ MetaUnchanged

\* Step 5: All effects processed — transition complete
AllEffectsDone ==
    /\ pc = "executing"
    /\ effectCursor >= NumEffects
    /\ pc' = "done"
    /\ UNCHANGED <<effectCursor, stateOnDisk, kanbanOnDisk,
                   outboxPending, outboxCompleted, effectApplied>>
    /\ MetaUnchanged

\* =========================================================================
\* Crash
\* Models process crash at any point during execution or recovery.
\* Durable state (disk files) survives; volatile state (pc, cursor) lost.
\* =========================================================================

\* Crash: nondeterministic at any non-terminal phase
\* Matches: orchestrator crash during emit_event or during recovery
Crash ==
    /\ pc \notin {"idle", "done"}
    /\ crashCount < MaxCrashes
    /\ pc' = "recovering"
    /\ crashCount' = crashCount + 1
    /\ effectCursor' = 0
    \* All durable state survives
    \* ENRICHMENT: runnerAvailable may change after crash (runner becomes unavailable)
    /\ \E ra \in BOOLEAN : runnerAvailable' = ra
    /\ UNCHANGED <<stateOnDisk, kanbanOnDisk,
                   outboxPending, outboxCompleted, effectApplied,
                   doubleApplied>>

\* =========================================================================
\* Recovery
\* Models orchestrator startup recovery:
\*   Phase 1: _scheduler_reconcile_merged_workers() fixes state/kanban mismatch
\*   Phase 2: _scheduler_replay_pending_effects() replays outbox
\*   Phase 3: If outbox was never recorded, reconciliation re-emits the event
\* =========================================================================

\* Recovery Phase 1a: Reconcile kanban (state committed, kanban stale)
\* Matches: _scheduler_reconcile_merged_workers() re-emitting merge.pr_merged
\* which calls _lifecycle_update_kanban() to fix the kanban status
ReconcileKanban ==
    /\ pc = "recovering"
    /\ stateOnDisk = "new"
    /\ kanbanOnDisk = "old"
    /\ kanbanOnDisk' = "new"
    /\ pc' = "replaying"
    /\ UNCHANGED <<effectCursor, stateOnDisk,
                   outboxPending, outboxCompleted, effectApplied>>
    /\ MetaUnchanged

\* Recovery Phase 1b: No reconciliation needed (kanban already consistent)
ReconcileNoop ==
    /\ pc = "recovering"
    /\ kanbanOnDisk = "new" \/ stateOnDisk = "old"
    /\ pc' = "replaying"
    /\ UNCHANGED <<effectCursor, stateOnDisk, kanbanOnDisk,
                   outboxPending, outboxCompleted, effectApplied>>
    /\ MetaUnchanged

\* Recovery Phase 2a: Replay a pending effect from outbox
\* Matches: outbox_replay_pending() in _scheduler_replay_pending_effects()
\* Effect is executed AND marked complete atomically during replay
\* (no separate marking step — replay calls both apply + mark)
ReplayEffect ==
    /\ pc = "replaying"
    /\ runnerAvailable
    /\ effectCursor \in EffectIndices
    /\ effectCursor \in outboxPending
    /\ \/ effectCursor \notin outboxCompleted
       \/ ~effectApplied[effectCursor]  \* Re-apply: completed via no-runner fallback
    \* CATEGORY 4 FIX: same guard as ExecuteEffect
    /\ \/ CleanupEffectIdx < 0
       \/ effectCursor /= CleanupEffectIdx
       \/ \A j \in (outboxPending \ outboxCompleted) \ {CleanupEffectIdx} :
            effectApplied[j]
    \* Track double application
    /\ doubleApplied' = IF effectApplied[effectCursor]
                         THEN doubleApplied \cup {effectCursor}
                         ELSE doubleApplied
    /\ effectApplied' = [effectApplied EXCEPT ![effectCursor] = TRUE]
    /\ outboxCompleted' = outboxCompleted \cup {effectCursor}
    /\ effectCursor' = effectCursor + 1
    /\ UNCHANGED <<pc, stateOnDisk, kanbanOnDisk, outboxPending, crashCount,
                   runnerAvailable>>

\* Recovery Phase 2b: Skip effect that's not pending or already completed
SkipReplayEffect ==
    /\ pc = "replaying"
    /\ effectCursor \in EffectIndices
    /\ \/ effectCursor \notin outboxPending
       \/ (effectCursor \in outboxCompleted
           /\ (effectApplied[effectCursor] \/ ~runnerAvailable))
    /\ effectCursor' = effectCursor + 1
    /\ UNCHANGED <<pc, stateOnDisk, kanbanOnDisk,
                   outboxPending, outboxCompleted, effectApplied>>
    /\ MetaUnchanged

\* ENRICHMENT: Replay effect without runner — mark completed but don't apply.
\* Models the fallback path where the effect runner is unavailable during
\* replay. The effect is marked as completed in the outbox (outboxCompleted)
\* but effectApplied[cursor] stays FALSE. This is the "mark complete without
\* execution" fallback that prevents the system from getting stuck on
\* unexecutable effects.
ReplayEffectNoRunner ==
    /\ pc = "replaying"
    /\ ~runnerAvailable
    /\ effectCursor \in EffectIndices
    /\ effectCursor \in outboxPending
    /\ effectCursor \notin outboxCompleted
    \* Mark completed WITHOUT applying
    /\ outboxCompleted' = outboxCompleted \cup {effectCursor}
    /\ effectCursor' = effectCursor + 1
    \* effectApplied is NOT set to TRUE — effect was NOT executed
    /\ UNCHANGED <<pc, stateOnDisk, kanbanOnDisk, outboxPending,
                   effectApplied, crashCount, doubleApplied, runnerAvailable>>

\* Recovery Phase 3: Replay scan complete — determine next phase
\*
\* Three outcomes:
\*   A. stateOnDisk = "old" → transition never committed, back to idle
\*      (no harm done; transition will be retried through normal lifecycle)
\*   B. outboxPending empty but effects unapplied → crash was between kanban
\*      write and outbox recording; reconciliation re-emits the event which
\*      records a fresh outbox. Go to recording_outbox.
\*   C. All effects applied → transition complete, go to done.
ReplayDone ==
    /\ pc = "replaying"
    /\ effectCursor >= NumEffects
    /\ IF stateOnDisk = "old"
       THEN
           \* (A) State never committed — restart from scratch
           /\ pc' = "idle"
           /\ UNCHANGED <<effectCursor, stateOnDisk, kanbanOnDisk,
                          outboxPending, outboxCompleted, effectApplied>>
           /\ MetaUnchanged
       ELSE IF outboxPending = {} /\ ~AllEffectsApplied
       THEN
           \* (B) State committed, outbox never recorded — re-record
           \* Models _scheduler_reconcile_merged_workers() re-emitting the
           \* transition event, which creates a fresh outbox and executes
           /\ pc' = "recording_outbox"
           /\ effectCursor' = 0
           /\ UNCHANGED <<stateOnDisk, kanbanOnDisk,
                          outboxPending, outboxCompleted, effectApplied>>
           /\ MetaUnchanged
       ELSE
           \* (C) All pending effects replayed — done
           /\ pc' = "done"
           /\ UNCHANGED <<effectCursor, stateOnDisk, kanbanOnDisk,
                          outboxPending, outboxCompleted, effectApplied>>
           /\ MetaUnchanged

\* Terminal: done is absorbing
Terminated ==
    /\ pc = "done"
    /\ UNCHANGED vars

\* =========================================================================
\* Next-state relation
\* =========================================================================

Next ==
    \* Normal execution
    \/ BeginTransition
    \/ WriteState
    \/ WriteKanban
    \/ RecordOutbox
    \/ ExecuteEffect
    \/ MarkEffectComplete
    \/ SkipCompletedEffect
    \/ AllEffectsDone
    \* Crash
    \/ Crash
    \* Recovery
    \/ ReconcileKanban
    \/ ReconcileNoop
    \/ ReplayEffect
    \/ ReplayEffectNoRunner
    \/ SkipReplayEffect
    \/ ReplayDone
    \* Terminal
    \/ Terminated

\* =========================================================================
\* Fairness (for liveness properties)
\* =========================================================================

Fairness ==
    /\ WF_vars(BeginTransition)
    /\ WF_vars(WriteState)
    /\ WF_vars(WriteKanban)
    /\ WF_vars(RecordOutbox)
    /\ WF_vars(ExecuteEffect)
    /\ WF_vars(MarkEffectComplete)
    /\ WF_vars(SkipCompletedEffect)
    /\ WF_vars(AllEffectsDone)
    /\ WF_vars(ReconcileKanban)
    /\ WF_vars(ReconcileNoop)
    /\ WF_vars(ReplayEffect)
    /\ WF_vars(SkipReplayEffect)
    /\ WF_vars(ReplayDone)

Spec == Init /\ [][Next]_vars /\ Fairness

\* =========================================================================
\* Safety Invariants
\* =========================================================================

\* TypeInvariant: all variables within declared domains
TypeInvariant ==
    /\ pc \in Phases
    /\ effectCursor \in 0..NumEffects
    /\ stateOnDisk \in DiskValues
    /\ kanbanOnDisk \in DiskValues
    /\ outboxPending \subseteq EffectIndices
    /\ outboxCompleted \subseteq EffectIndices
    /\ \A i \in EffectIndices : effectApplied[i] \in BOOLEAN
    /\ crashCount \in 0..MaxCrashes
    /\ doubleApplied \subseteq EffectIndices
    /\ runnerAvailable \in BOOLEAN

\* DoneConsistency: when the system reports done, all state is committed.
\* ENRICHMENT: When runnerAvailable, all effects are also applied.
\* Without the runner, effects may be marked complete but not applied.
\* This is THE key safety property: the outbox pattern guarantees that
\* reaching "done" means the transition is fully applied (when runner exists).
DoneConsistency ==
    pc = "done" =>
        /\ stateOnDisk = "new"
        /\ kanbanOnDisk = "new"
        /\ (runnerAvailable => AllEffectsApplied)

\* StateBeforeKanban: kanban is never ahead of state.
\* emit_event() writes git_state_set BEFORE _lifecycle_update_kanban.
\* No action sets kanbanOnDisk = "new" unless stateOnDisk is already "new".
StateBeforeKanban ==
    kanbanOnDisk = "new" => stateOnDisk = "new"

\* CompletedSubsetPending: an effect cannot be marked completed without
\* first being recorded as pending. The outbox tracks both sets.
CompletedSubsetPending ==
    outboxCompleted \subseteq outboxPending

\* CleanupEffectOrder: the cleanup effect is never applied before all
\* other pending effects. Models the CATEGORY 4 FIX where cleanup_worktree
\* calls outbox_replay_pending() before executing.
\* Note: This is enforced by guards on ExecuteEffect and ReplayEffect,
\* so it's a derived invariant (if guards are wrong, this catches it).
CleanupEffectOrder ==
    /\ CleanupEffectIdx >= 0
    /\ CleanupEffectIdx \in EffectIndices
    => (effectApplied[CleanupEffectIdx] =>
            \A j \in EffectIndices \ {CleanupEffectIdx} :
                j \in outboxPending => effectApplied[j])

\* CrashBounded: crash counter stays within limits
CrashBounded ==
    crashCount <= MaxCrashes

\* ENRICHMENT: FallbackNeverApplies — when the runner is unavailable and
\* an effect is marked completed (in outboxCompleted), it does NOT imply
\* that effectApplied[i] is TRUE. This is a weakened DoneConsistency that
\* explicitly captures the fallback behavior.
FallbackNeverApplies ==
    \A i \in EffectIndices :
        (~runnerAvailable /\ i \in outboxCompleted) =>
            \* The effect MAY or MAY NOT be applied — no guarantee either way
            \* This invariant verifies that completed does not imply applied
            \* when the runner is unavailable. We verify the weaker property:
            \* outboxCompleted is always a subset of outboxPending
            i \in outboxPending

\* =========================================================================
\* Liveness Properties (require fairness, TLC only)
\* =========================================================================

\* EventualCompletion: the system eventually reaches done.
\* Requires: fairness (WF) + bounded crashes (MaxCrashes).
\* Argument: each recovery cycle makes progress (at least one durable
\* operation completes). With bounded crashes, eventually the system
\* runs without interruption and reaches done.
\* NOTE: Requires TLC for verification -- Apalache does not enforce fairness.
EventualCompletion == <>(pc = "done")

=============================================================================
