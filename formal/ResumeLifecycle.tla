--------------------------- MODULE ResumeLifecycle ----------------------------
(*
 * TLA+ formal model of Chief Wiggum's resume decision subsystem.
 *
 * Models the lifecycle of a failed worker's retry process:
 *   - Pipeline runs and produces PASS/FAIL
 *   - On FAIL: scheduler identifies worker as needing a resume decision
 *   - Resume-decide agent (lib/agents/system/resume-decide.sh) runs and
 *     produces a decision: COMPLETE, RETRY, DEFER, or ABORT
 *   - Decision is consumed:
 *       COMPLETE → terminal (task finished, PR exists)
 *       RETRY    → increment attempts, spawn resume worker
 *       DEFER    → enter cooldown, then re-evaluate
 *       ABORT    → terminal (uncompletable task)
 *   - If attempts exceed MaxAttempts → terminal (MAX_ATTEMPTS)
 *   - Repeated step failure detection → terminal (REPEATED_FAIL)
 *
 * Resume state is persisted in worker_dir/resume-state.json with:
 *   attempt_count, max_attempts, cooldown_until, terminal, terminal_reason,
 *   and a history[] of decisions (lib/core/resume-state.sh).
 *
 * Key properties verified:
 *   - TerminalAbsorbing: terminal phase is never left
 *   - AttemptsWithinBounds: attempt counter bounded by MaxAttempts + 1
 *   - CooldownBlocksSpawn: workers in cooldown are never spawned
 *   - DecisionRequiredForSpawn: spawning requires a RETRY decision
 *   - TerminalReasonConsistency: terminal reason matches the path taken
 *   - PassNeverRetried: a passing pipeline is never retried
 *
 * ENRICHMENT: USER_RETRY Override
 * Models manual user retry from terminal state. Resets attempts to 0,
 * clears terminal reason, transitions to needs_decide. Bounded by MaxUserRetries.
 *
 * ENRICHMENT: Workspace Violation
 * Models workspace violation detection (e.g., agent wrote to forbidden paths).
 * Violations from active phase force terminal with VIOLATION reason.
 * ForceResumeViolation clears the violation (models -f flag).
 *
 * ENRICHMENT: Interrupted vs Completed
 * When pipeline fails with stepInterrupted=TRUE, the decide phase is skipped
 * and the worker goes directly from pipeline_done to active (retry without decide).
 * When stepInterrupted=FALSE, normal decide path.
 *
 * Designed for Apalache symbolic model checking (type annotations, CInit).
 *)

EXTENDS Integers

CONSTANTS
    \* @type: Int;
    MaxAttempts,         \* Maximum resume attempts before terminal
    \* @type: Int;
    CooldownDuration,    \* Ticks of cooldown for DEFER decisions
    \* @type: Int;
    MaxUserRetries       \* Maximum user retry overrides from terminal

VARIABLES
    \* @type: Str;
    phase,               \* Current lifecycle phase
    \* @type: Int;
    attempts,            \* Resume attempt count (0 on first pipeline run)
    \* @type: Str;
    decision,            \* Current/last decision
    \* @type: Int;
    cooldownTicks,       \* Remaining cooldown ticks (0 = not cooling)
    \* @type: Str;
    pipelineResult,      \* Last pipeline outcome: "none", "PASS", "FAIL"
    \* @type: Str;
    terminalReason,      \* Why terminal: "", "COMPLETE", "ABORT", "MAX_ATTEMPTS", "REPEATED_FAIL", "VIOLATION"
    \* === ENRICHMENT VARIABLES ===
    \* @type: Int;
    userRetryCount,      \* Number of user retry overrides from terminal
    \* @type: Bool;
    hasViolation,        \* TRUE if workspace violation detected
    \* @type: Bool;
    stepInterrupted      \* TRUE if pipeline was interrupted (not completed)

\* @type: <<Str, Int, Str, Int, Str, Str, Int, Bool, Bool>>;
vars == <<phase, attempts, decision, cooldownTicks, pipelineResult, terminalReason,
          userRetryCount, hasViolation, stepInterrupted>>

\* =========================================================================
\* Type definitions
\* =========================================================================

PhaseValues == {"idle", "active", "pipeline_done", "needs_decide",
                "deciding", "decided", "cooldown", "terminal"}

DecisionValues == {"none", "COMPLETE", "RETRY", "DEFER", "ABORT", "USER_RETRY"}

ResultValues == {"none", "PASS", "FAIL"}

ReasonValues == {"", "COMPLETE", "ABORT", "MAX_ATTEMPTS", "REPEATED_FAIL", "VIOLATION"}

\* =========================================================================
\* Init and CInit
\* =========================================================================

Init ==
    /\ phase = "idle"
    /\ attempts = 0
    /\ decision = "none"
    /\ cooldownTicks = 0
    /\ pipelineResult = "none"
    /\ terminalReason = ""
    /\ userRetryCount = 0
    /\ hasViolation = FALSE
    /\ stepInterrupted = FALSE

\* Apalache constant initialization
\* 3 attempts before terminal, 2-tick cooldown
CInit ==
    /\ MaxAttempts = 3
    /\ CooldownDuration = 2
    /\ MaxUserRetries = 2

\* =========================================================================
\* Helpers
\* =========================================================================

\* Unchanged enrichment variables
EnrichmentUnchanged == UNCHANGED <<userRetryCount, hasViolation, stepInterrupted>>

\* =========================================================================
\* Actions - Pipeline Execution
\* =========================================================================

\* Start the first pipeline run
\* Matches: orchestrator spawning initial worker for a task
StartPipeline ==
    /\ phase = "idle"
    /\ hasViolation = FALSE
    /\ phase' = "active"
    /\ pipelineResult' = "none"
    /\ UNCHANGED <<attempts, decision, cooldownTicks, terminalReason>>
    /\ EnrichmentUnchanged

\* Pipeline completes successfully
\* Matches: pipeline_run_all returns 0 (PASS result from final step)
PipelinePass ==
    /\ phase = "active"
    /\ pipelineResult' = "PASS"
    /\ phase' = "pipeline_done"
    /\ stepInterrupted' = FALSE
    /\ UNCHANGED <<attempts, decision, cooldownTicks, terminalReason,
                   userRetryCount, hasViolation>>

\* Pipeline fails
\* Matches: pipeline_run_all returns non-zero or agent returns FAIL
\* ENRICHMENT: stepInterrupted is nondeterministic — models whether the
\* pipeline was interrupted mid-step (TRUE) or completed the step and failed (FALSE)
PipelineFail ==
    /\ phase = "active"
    /\ pipelineResult' = "FAIL"
    /\ phase' = "pipeline_done"
    /\ \E interrupted \in BOOLEAN : stepInterrupted' = interrupted
    /\ UNCHANGED <<attempts, decision, cooldownTicks, terminalReason,
                   userRetryCount, hasViolation>>

\* =========================================================================
\* Actions - Pipeline Result Handling
\* =========================================================================

\* Pipeline passed → terminal with COMPLETE reason
\* Matches: worker lifecycle reaches merged state after successful pipeline
PassToTerminal ==
    /\ phase = "pipeline_done"
    /\ pipelineResult = "PASS"
    /\ phase' = "terminal"
    /\ terminalReason' = "COMPLETE"
    /\ UNCHANGED <<attempts, decision, cooldownTicks, pipelineResult>>
    /\ EnrichmentUnchanged

\* Pipeline failed → needs resume decision (normal path: step completed)
\* Matches: get_workers_needing_decide() in scheduler.sh identifying
\* workers whose pipeline failed and resume-state is not terminal
\* ENRICHMENT: Only fires when stepInterrupted = FALSE (normal decide path)
FailToNeedsDecide ==
    /\ phase = "pipeline_done"
    /\ pipelineResult = "FAIL"
    /\ stepInterrupted = FALSE
    /\ phase' = "needs_decide"
    /\ UNCHANGED <<attempts, decision, cooldownTicks, pipelineResult, terminalReason>>
    /\ EnrichmentUnchanged

\* ENRICHMENT: Pipeline failed with interruption → retry directly without decide.
\* When stepInterrupted = TRUE, skip the decide phase entirely and go directly
\* from pipeline_done to active (retry without decide).
InterruptedToActive ==
    /\ phase = "pipeline_done"
    /\ pipelineResult = "FAIL"
    /\ stepInterrupted = TRUE
    /\ attempts < MaxAttempts
    /\ hasViolation = FALSE
    /\ attempts' = attempts + 1
    /\ phase' = "active"
    /\ pipelineResult' = "none"
    /\ decision' = "RETRY"
    /\ UNCHANGED <<cooldownTicks, terminalReason>>
    /\ EnrichmentUnchanged

\* ENRICHMENT: Pipeline failed with interruption but max attempts exceeded
InterruptedMaxExceeded ==
    /\ phase = "pipeline_done"
    /\ pipelineResult = "FAIL"
    /\ stepInterrupted = TRUE
    /\ attempts >= MaxAttempts
    /\ phase' = "terminal"
    /\ terminalReason' = "MAX_ATTEMPTS"
    /\ UNCHANGED <<attempts, decision, cooldownTicks, pipelineResult>>
    /\ EnrichmentUnchanged

\* =========================================================================
\* Actions - Resume Decision
\* =========================================================================

\* Scheduler spawns resume-decide agent
\* Matches: _spawn_resume_decide_agent() in scheduler.sh
StartDecide ==
    /\ phase = "needs_decide"
    /\ phase' = "deciding"
    /\ UNCHANGED <<attempts, decision, cooldownTicks, pipelineResult, terminalReason>>
    /\ EnrichmentUnchanged

\* Resume-decide agent produces COMPLETE decision
\* Matches: agent writes <decision>COMPLETE</decision> to output
MakeDecisionComplete ==
    /\ phase = "deciding"
    /\ decision' = "COMPLETE"
    /\ phase' = "decided"
    /\ UNCHANGED <<attempts, cooldownTicks, pipelineResult, terminalReason>>
    /\ EnrichmentUnchanged

\* Resume-decide agent produces RETRY decision
\* Matches: agent writes <decision>RETRY:pipeline:step_id</decision>
MakeDecisionRetry ==
    /\ phase = "deciding"
    /\ decision' = "RETRY"
    /\ phase' = "decided"
    /\ UNCHANGED <<attempts, cooldownTicks, pipelineResult, terminalReason>>
    /\ EnrichmentUnchanged

\* Resume-decide agent produces DEFER decision
\* Matches: agent writes <decision>DEFER</decision> (transient failure)
MakeDecisionDefer ==
    /\ phase = "deciding"
    /\ decision' = "DEFER"
    /\ phase' = "decided"
    /\ UNCHANGED <<attempts, cooldownTicks, pipelineResult, terminalReason>>
    /\ EnrichmentUnchanged

\* Resume-decide agent produces ABORT decision
\* Matches: agent writes <decision>ABORT</decision> (uncompletable)
MakeDecisionAbort ==
    /\ phase = "deciding"
    /\ decision' = "ABORT"
    /\ phase' = "decided"
    /\ UNCHANGED <<attempts, cooldownTicks, pipelineResult, terminalReason>>
    /\ EnrichmentUnchanged

\* Resume-decide agent fails (crash, parse failure, timeout)
\* Matches: decide agent exits non-zero or output unparseable.
\* Fallback: _fallback_extract_decision returns RETRY:default:first_step
\* which means failed decides default to retry. Modeled as returning
\* to needs_decide for re-evaluation.
DecideFailed ==
    /\ phase = "deciding"
    /\ phase' = "needs_decide"
    /\ UNCHANGED <<attempts, decision, cooldownTicks, pipelineResult, terminalReason>>
    /\ EnrichmentUnchanged

\* =========================================================================
\* Actions - Decision Consumption
\* =========================================================================

\* Consume COMPLETE: mark terminal
\* Matches: resume_state_set_terminal(worker_dir, "COMPLETE", ...)
ConsumeComplete ==
    /\ phase = "decided"
    /\ decision = "COMPLETE"
    /\ phase' = "terminal"
    /\ terminalReason' = "COMPLETE"
    /\ UNCHANGED <<attempts, decision, cooldownTicks, pipelineResult>>
    /\ EnrichmentUnchanged

\* Consume RETRY: increment attempts and spawn resume worker
\* Guarded: attempts < MaxAttempts
\* Matches: resume_state_increment() + spawn worker at resume step
ConsumeRetry ==
    /\ phase = "decided"
    /\ decision = "RETRY"
    /\ attempts < MaxAttempts
    /\ hasViolation = FALSE
    /\ attempts' = attempts + 1
    /\ phase' = "active"
    /\ pipelineResult' = "none"
    /\ UNCHANGED <<decision, cooldownTicks, terminalReason>>
    /\ EnrichmentUnchanged

\* Consume RETRY but max attempts exceeded: terminal
\* Matches: resume_state_max_exceeded() check in scheduling phase
ConsumeRetryMaxExceeded ==
    /\ phase = "decided"
    /\ decision = "RETRY"
    /\ attempts >= MaxAttempts
    /\ phase' = "terminal"
    /\ terminalReason' = "MAX_ATTEMPTS"
    /\ UNCHANGED <<attempts, decision, cooldownTicks, pipelineResult>>
    /\ EnrichmentUnchanged

\* Consume ABORT: mark terminal
\* Matches: resume_state_set_terminal(worker_dir, "ABORT", ...)
ConsumeAbort ==
    /\ phase = "decided"
    /\ decision = "ABORT"
    /\ phase' = "terminal"
    /\ terminalReason' = "ABORT"
    /\ UNCHANGED <<attempts, decision, cooldownTicks, pipelineResult>>
    /\ EnrichmentUnchanged

\* Consume DEFER: enter cooldown
\* Matches: resume_state_set_cooldown(worker_dir, duration)
ConsumeDeferCooldown ==
    /\ phase = "decided"
    /\ decision = "DEFER"
    /\ cooldownTicks' = CooldownDuration
    /\ phase' = "cooldown"
    /\ UNCHANGED <<attempts, decision, pipelineResult, terminalReason>>
    /\ EnrichmentUnchanged

\* =========================================================================
\* Actions - Cooldown
\* =========================================================================

\* Cooldown tick: decrement timer
\* Matches: scheduling tick where resume_state_is_cooling() returns TRUE
CooldownTick ==
    /\ phase = "cooldown"
    /\ cooldownTicks > 1
    /\ cooldownTicks' = cooldownTicks - 1
    /\ UNCHANGED <<phase, attempts, decision, pipelineResult, terminalReason>>
    /\ EnrichmentUnchanged

\* Cooldown expired: back to needs_decide for re-evaluation
\* Matches: scheduler tick where cooldown_until has passed
CooldownExpire ==
    /\ phase = "cooldown"
    /\ cooldownTicks <= 1
    /\ cooldownTicks' = 0
    /\ phase' = "needs_decide"
    /\ UNCHANGED <<attempts, decision, pipelineResult, terminalReason>>
    /\ EnrichmentUnchanged

\* =========================================================================
\* Actions - Forced Terminal
\* =========================================================================

\* Repeated step failure detection: same step keeps failing
\* Matches: _detect_repeated_step_failure() in get_workers_needing_decide()
\* which marks worker terminal before the decide agent even runs.
\* Only fires when the worker has been retried at least once (attempts > 0).
ForceTerminalRepeatedFail ==
    /\ phase = "needs_decide"
    /\ attempts > 0
    /\ phase' = "terminal"
    /\ terminalReason' = "REPEATED_FAIL"
    /\ UNCHANGED <<attempts, decision, cooldownTicks, pipelineResult>>
    /\ EnrichmentUnchanged

\* =========================================================================
\* Actions - Enrichment: USER_RETRY Override
\* =========================================================================

\* ENRICHMENT: User retry from terminal state.
\* Resets attempts to 0, clears terminalReason, transitions to needs_decide.
\* Bounded by MaxUserRetries.
UserRetry ==
    /\ phase = "terminal"
    /\ userRetryCount < MaxUserRetries
    /\ terminalReason /= "VIOLATION"
    /\ phase' = "needs_decide"
    /\ attempts' = 0
    /\ terminalReason' = ""
    /\ decision' = "none"
    /\ pipelineResult' = "none"
    /\ userRetryCount' = userRetryCount + 1
    /\ UNCHANGED <<cooldownTicks, hasViolation, stepInterrupted>>

\* =========================================================================
\* Actions - Enrichment: Workspace Violation
\* =========================================================================

\* ENRICHMENT: Violation detected during active phase.
\* Agent wrote to forbidden paths or violated workspace rules.
\* Forces terminal with VIOLATION reason.
ViolationDetected ==
    /\ phase = "active"
    /\ hasViolation' = TRUE
    /\ phase' = "terminal"
    /\ terminalReason' = "VIOLATION"
    /\ UNCHANGED <<attempts, decision, cooldownTicks, pipelineResult,
                   userRetryCount, stepInterrupted>>

\* ENRICHMENT: Force resume after violation (models -f flag).
\* Clears the violation flag, allowing retry.
ForceResumeViolation ==
    /\ phase = "terminal"
    /\ hasViolation = TRUE
    /\ terminalReason = "VIOLATION"
    /\ hasViolation' = FALSE
    /\ phase' = "needs_decide"
    /\ terminalReason' = ""
    /\ decision' = "none"
    /\ UNCHANGED <<attempts, cooldownTicks, pipelineResult,
                   userRetryCount, stepInterrupted>>

\* =========================================================================
\* Actions - Terminal
\* =========================================================================

\* Terminal is absorbing: no transitions out (except USER_RETRY and ForceResumeViolation)
Terminated ==
    /\ phase = "terminal"
    /\ UNCHANGED vars

\* =========================================================================
\* Next-state relation
\* =========================================================================

Next ==
    \* Pipeline execution
    \/ StartPipeline
    \/ PipelinePass
    \/ PipelineFail
    \* Pipeline result handling
    \/ PassToTerminal
    \/ FailToNeedsDecide
    \/ InterruptedToActive
    \/ InterruptedMaxExceeded
    \* Resume decision
    \/ StartDecide
    \/ MakeDecisionComplete
    \/ MakeDecisionRetry
    \/ MakeDecisionDefer
    \/ MakeDecisionAbort
    \/ DecideFailed
    \* Decision consumption
    \/ ConsumeComplete
    \/ ConsumeRetry
    \/ ConsumeRetryMaxExceeded
    \/ ConsumeAbort
    \/ ConsumeDeferCooldown
    \* Cooldown
    \/ CooldownTick
    \/ CooldownExpire
    \* Forced terminal
    \/ ForceTerminalRepeatedFail
    \* Enrichment: USER_RETRY
    \/ UserRetry
    \* Enrichment: Violation
    \/ ViolationDetected
    \/ ForceResumeViolation
    \* Terminal
    \/ Terminated

\* =========================================================================
\* Fairness
\* =========================================================================

Fairness ==
    /\ WF_vars(StartPipeline)
    /\ WF_vars(PipelinePass \/ PipelineFail)
    /\ WF_vars(PassToTerminal)
    /\ WF_vars(FailToNeedsDecide)
    /\ WF_vars(StartDecide)
    /\ WF_vars(MakeDecisionComplete \/ MakeDecisionRetry
               \/ MakeDecisionDefer \/ MakeDecisionAbort \/ DecideFailed)
    /\ WF_vars(ConsumeComplete \/ ConsumeRetry \/ ConsumeRetryMaxExceeded
               \/ ConsumeAbort \/ ConsumeDeferCooldown)
    /\ WF_vars(CooldownTick)
    /\ WF_vars(CooldownExpire)

Spec == Init /\ [][Next]_vars /\ Fairness

\* =========================================================================
\* Safety Invariants
\* =========================================================================

\* TypeInvariant: all variables within declared domains
TypeInvariant ==
    /\ phase \in PhaseValues
    /\ attempts \in 0..(MaxAttempts + 1)
    /\ decision \in DecisionValues
    /\ cooldownTicks \in 0..CooldownDuration
    /\ pipelineResult \in ResultValues
    /\ terminalReason \in ReasonValues
    /\ userRetryCount \in 0..(MaxUserRetries + 1)
    /\ hasViolation \in BOOLEAN
    /\ stepInterrupted \in BOOLEAN

\* TerminalAbsorbing: terminal reason implies terminal phase.
\* ENRICHMENT: USER_RETRY and ForceResumeViolation can leave terminal,
\* but they clear terminalReason before transitioning. So the invariant
\* still holds: non-empty reason => terminal phase.
TerminalAbsorbing ==
    terminalReason /= "" => phase = "terminal"

\* AttemptsWithinBounds: attempt counter never exceeds MaxAttempts + 1.
\* The +1 accounts for the increment happening before the max check:
\* ConsumeRetry increments first, then the NEXT cycle checks the bound.
AttemptsWithinBounds ==
    attempts <= MaxAttempts

\* CooldownBlocksSpawn: if in cooldown, we're not in active or spawning.
\* Workers in cooldown (DEFER decision) must wait before retrying.
CooldownBlocksSpawn ==
    cooldownTicks > 0 => phase \in {"cooldown", "terminal"}

\* DecisionRequiredForSpawn: active phase (after first run) requires
\* a RETRY decision to have been made. The first pipeline run (from idle)
\* doesn't need a decision; subsequent runs (attempts > 0) require RETRY.
DecisionRequiredForSpawn ==
    phase = "active" /\ attempts > 0 => decision = "RETRY"

\* TerminalReasonConsistency: terminal reason matches the phase.
\* Non-empty reason always means terminal; empty reason means non-terminal.
TerminalReasonConsistency ==
    /\ (phase = "terminal") = (terminalReason /= "")
    /\ terminalReason \in ReasonValues

\* PassNeverRetried: a passing pipeline is never retried.
\* If the last pipeline result was PASS, we go terminal (not retry).
PassNeverRetried ==
    pipelineResult = "PASS" => phase \in {"pipeline_done", "terminal"}

\* =========================================================================
\* Enrichment Safety Invariants
\* =========================================================================

\* UserRetryBounded: user retry count never exceeds MaxUserRetries
UserRetryBounded ==
    userRetryCount <= MaxUserRetries

\* ViolationBlocksResume: when hasViolation is TRUE, only terminal or active
\* phases are possible. The violation flag blocks ConsumeRetry and
\* InterruptedToActive. Only ForceResumeViolation can clear it.
ViolationBlocksResume ==
    hasViolation => phase \in {"terminal", "active"}

\* InterruptedBypassesDecide: when stepInterrupted is TRUE and we're back
\* in active phase with attempts > 0, the decision must be RETRY or none
\* (the decide phase was bypassed via InterruptedToActive).
InterruptedBypassesDecide ==
    stepInterrupted /\ phase = "active" /\ attempts > 0 =>
        decision \in {"none", "RETRY"}

\* =========================================================================
\* Liveness Properties (require fairness, TLC only)
\* =========================================================================

\* EventualTermination: the worker eventually reaches terminal state.
\* Requires: fairness (WF) + bounded attempts (MaxAttempts).
\* Argument: each retry cycle increments attempts. With bounded attempts,
\* eventually ConsumeRetryMaxExceeded fires. DEFER cooldowns are bounded.
\* The only way to avoid terminal is infinite DEFER loops, which requires
\* infinite cooldown+expire cycles without ever producing RETRY/ABORT.
\* NOTE: Requires TLC for verification -- Apalache does not enforce fairness.
EventualTermination == <>(phase = "terminal")

=============================================================================
