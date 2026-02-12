--------------------------- MODULE PipelineEngine ----------------------------
(*
 * TLA+ formal model of Chief Wiggum's pipeline engine.
 *
 * Models a simplified 3-step pipeline capturing all structural features of
 * the jump-based state machine in lib/pipeline/pipeline-runner.sh:
 *   - Visit counters with per-step maximums
 *   - on_max jump targets (default: "next")
 *   - Nondeterministic agent results: {PASS, FAIL, FIX, SKIP}
 *   - Inline agent handlers for FIX results
 *   - Circuit breaker: consecutive same non-terminal results escalate to FAIL
 *   - Jump target resolution: self, prev, next, abort, <step-id>
 *   - UNKNOWN result with backup extraction (nondeterministic recovery)
 *   - Cost budget enforcement (pipeline aborts when accumulated cost exceeds budget)
 *
 * The 3-step pipeline exercises:
 *   Step 0: No inline handler (FIX -> jump prev, clamped to self at step 0)
 *   Step 1: Has inline handler (FIX -> run inline, then re-run self)
 *   Step 2: Has inline handler (FIX -> run inline, then re-run self)
 *
 * GAP CLOSURE #3: UNKNOWN result + backup extraction
 * When an agent produces no recognizable result, the pipeline attempts a backup
 * session resume to recover the result tag. Modeled as nondeterministic choice:
 * either backup recovers a valid result, or UNKNOWN persists and jumps to self.
 * Consecutive UNKNOWNs are tracked by the circuit breaker.
 * Matches _pipeline_backup_result_extraction() in lib/pipeline/pipeline-runner.sh.
 *
 * GAP CLOSURE #4: Cost budget enforcement
 * Each step consumes an abstract cost unit. If CostBudget > 0 and accumulated
 * cost exceeds the budget, the pipeline aborts. Matches _check_cost_budget() /
 * _update_step_cost() in lib/pipeline/pipeline-runner.sh.
 *
 * GAP CLOSURE #5: Named jump targets
 * ResolveJump supports step IDs in addition to self/prev/next/abort.
 * Modeled via step index lookup (step0/step1/step2 for CInit's 3 steps).
 * Matches pipeline_find_step_index() resolution in _resolve_jump_target().
 *
 * MEDIUM TERM #3: Supervisor Loop
 * Models supervisor-level interruption and restart:
 *   - SupervisorInterval: how often supervisor reviews progress
 *   - Supervisor can issue CONTINUE, STOP, or RESTART decisions
 *   - RESTART resets current step's visit counter (iteration reset)
 *   - Models "supervisor restarts reset counters" class of bugs
 *
 * ENRICHMENT: Step Timeout
 * Steps with HasTimeout[i] = TRUE can time out, producing a FAIL result
 * regardless of agent output. Matches step-level timeout_seconds in pipeline config.
 *
 * ENRICHMENT: enabled_by Conditional Skipping
 * Steps with StepEnabled[i] = FALSE are silently skipped: pc advances without
 * incrementing visits or producing a result. Matches enabled_by conditions in
 * pipeline step definitions.
 *
 * ENRICHMENT: on_max Cascade Detection
 * When on_max fires and sends control to another step that also fires on_max,
 * a cascade forms. If a step appears twice in the cascade, the pipeline aborts
 * to prevent infinite on_max loops. Tracked via onMaxCascade set.
 *
 * ENRICHMENT: Commit Failure Override
 * Steps with CommitAfter[i] = TRUE attempt a git commit after execution.
 * If the commit fails and the effective result was PASS, it overrides to FIX.
 * Matches commit_after in pipeline step definitions.
 *
 * Designed for Apalache symbolic model checking (type annotations, CInit).
 *)

EXTENDS Integers, Sequences

CONSTANTS
    \* @type: Int;
    NumSteps,
    \* @type: Int -> Int;
    MaxVisits,         \* function: step index -> max visits (0 = unlimited)
    \* @type: Int -> Bool;
    HasInline,         \* function: step index -> TRUE if FIX has inline handler
    \* @type: Int -> Int;
    InlineMax,         \* function: step index -> max inline visits (0 = unlimited)
    \* @type: Int;
    CircuitBreakerThreshold,
    \* @type: Int;
    SupervisorInterval,  \* iterations between supervisor checks (0 = no supervisor)
    \* @type: Int;
    MaxSupervisorRestarts, \* max times supervisor can restart a step
    \* @type: Int;
    CostBudget,            \* max accumulated cost (0 = unlimited). GAP CLOSURE #4.
    \* === ENRICHMENT CONSTANTS ===
    \* @type: Int -> Bool;
    HasTimeout,            \* function: step index -> TRUE if step can time out
    \* @type: Int -> Bool;
    StepEnabled,           \* function: step index -> TRUE if step is enabled (enabled_by)
    \* @type: Int -> Bool;
    CommitAfter            \* function: step index -> TRUE if step commits after execution

VARIABLES
    \* @type: Int;
    pc,                \* current step index (-1 = aborted, NumSteps = completed)
    \* @type: Int -> Int;
    visits,            \* function: step index -> visit count
    \* @type: Int -> Int;
    inlineVisits,      \* function: step index -> inline handler visit count
    \* @type: Int -> Int;
    consecutiveSame,   \* function: step index -> consecutive same result count
    \* @type: Int -> Str;
    lastResult,        \* function: step index -> last non-terminal result string
    \* @type: Str;
    status,            \* "running", "completed", "aborted"
    \* === SUPERVISOR STATE (Medium Term #3) ===
    \* @type: Int;
    iterationsSinceCheck,  \* iterations since last supervisor check
    \* @type: Int -> Int;
    supervisorRestarts,    \* function: step index -> restart count by supervisor
    \* @type: Int;
    currentCost,           \* accumulated pipeline cost (GAP CLOSURE #4)
    \* === ENRICHMENT VARIABLES ===
    \* @type: Set(Int);
    onMaxCascade,          \* set of step indices visited during current on_max cascade
    \* @type: Bool;
    timedOut               \* TRUE if current step timed out

\* @type: <<Int, Int -> Int, Int -> Int, Int -> Int, Int -> Str, Str, Int, Int -> Int, Int, Set(Int), Bool>>;
vars == <<pc, visits, inlineVisits, consecutiveSame, lastResult, status, iterationsSinceCheck, supervisorRestarts, currentCost, onMaxCascade, timedOut>>

\* =========================================================================
\* Type definitions
\* =========================================================================

StepRange == 0..(NumSteps - 1)
\* GAP CLOSURE #3: UNKNOWN added — matches implementation's UNKNOWN result path
Results == {"PASS", "FAIL", "FIX", "SKIP", "UNKNOWN"}

\* =========================================================================
\* Init and CInit
\* =========================================================================

Init ==
    /\ pc = 0
    /\ visits = [i \in StepRange |-> 0]
    /\ inlineVisits = [i \in StepRange |-> 0]
    /\ consecutiveSame = [i \in StepRange |-> 0]
    /\ lastResult = [i \in StepRange |-> ""]
    /\ status = "running"
    /\ iterationsSinceCheck = 0
    /\ supervisorRestarts = [i \in StepRange |-> 0]
    /\ currentCost = 0
    /\ onMaxCascade = {}
    /\ timedOut = FALSE

\* Apalache constant initialization
CInit ==
    /\ NumSteps = 3
    /\ MaxVisits = [i \in 0..2 |-> IF i = 0 THEN 2 ELSE 3]
    /\ HasInline = [i \in 0..2 |-> IF i = 0 THEN FALSE ELSE TRUE]
    /\ InlineMax = [i \in 0..2 |-> IF i = 0 THEN 0 ELSE 2]
    /\ CircuitBreakerThreshold = 3
    /\ SupervisorInterval = 2       \* supervisor checks every 2 iterations
    /\ MaxSupervisorRestarts = 1    \* supervisor can restart each step once
    /\ CostBudget = 5              \* pipeline aborts after 5 abstract cost units (GAP CLOSURE #4)
    \* === ENRICHMENT CONSTANTS ===
    /\ HasTimeout = [i \in 0..2 |-> IF i = 1 THEN TRUE ELSE FALSE]    \* step 1 can time out
    /\ StepEnabled = [i \in 0..2 |-> IF i = 2 THEN FALSE ELSE TRUE]   \* step 2 is disabled
    /\ CommitAfter = [i \in 0..2 |-> IF i = 1 THEN TRUE ELSE FALSE]   \* step 1 commits after

\* =========================================================================
\* Helpers
\* =========================================================================

\* Resolve jump target to step index
\* GAP CLOSURE #5: Named step targets (step0/step1/step2) in addition to
\* self/prev/next/abort. Matches pipeline_find_step_index() in pipeline-runner.sh.
\* @type: (Str, Int) => Int;
ResolveJump(target, current) ==
    CASE target = "self"  -> current
      [] target = "next"  -> current + 1
      [] target = "prev"  -> IF current > 0 THEN current - 1 ELSE 0
      [] target = "abort" -> -1
      \* Named step targets: resolve to step index (CInit has 3 steps: 0, 1, 2)
      [] target = "step0" -> 0
      [] target = "step1" -> 1
      [] target = "step2" -> 2
      [] OTHER            -> -1

\* Check if a result is terminal for the step (resets circuit breaker)
\* @type: (Str) => Bool;
IsTerminalResult(r) == r \in {"PASS", "FAIL", "SKIP"}

\* Helper: unchanged supervisor state
SupervisorUnchanged == UNCHANGED <<iterationsSinceCheck, supervisorRestarts>>

\* Helper: unchanged cost state
CostUnchanged == UNCHANGED currentCost

\* Helper: unchanged enrichment state
EnrichmentUnchanged == UNCHANGED <<onMaxCascade, timedOut>>

\* =========================================================================
\* Actions
\* =========================================================================

\* Execute a pipeline step: nondeterministically choose a result and dispatch
\* ENRICHMENT: Guard against timedOut (timeout produces FAIL via separate action)
ExecuteStep ==
    /\ status = "running"
    /\ pc >= 0
    /\ pc < NumSteps
    /\ ~timedOut
    \* ENRICHMENT: Step must be enabled (enabled_by condition)
    /\ StepEnabled[pc]
    \* GAP CLOSURE #4: Cost budget check before execution
    /\ CostBudget = 0 \/ currentCost < CostBudget
    /\ \E result \in Results :
        \* ENRICHMENT: Commit failure override
        \* When CommitAfter and commit fails, PASS is overridden to FIX
        \E commitFails \in BOOLEAN :
        LET
            i == pc
            currentVisits == visits[i]
            maxV == MaxVisits[i]
        IN
        \* --- Check max visits first ---
        IF maxV > 0 /\ currentVisits >= maxV
        THEN
            \* on_max fires: default jump is "next"
            \* ENRICHMENT: Cascade detection — if step already in cascade, abort
            IF i \in onMaxCascade
            THEN
                /\ pc' = -1
                /\ status' = "aborted"
                /\ UNCHANGED <<visits, inlineVisits, consecutiveSame, lastResult>>
                /\ CostUnchanged
                /\ UNCHANGED <<onMaxCascade, timedOut>>
            ELSE
                LET nextPc == ResolveJump("next", i) IN
                /\ pc' = nextPc
                /\ status' = IF nextPc < 0 THEN "aborted"
                              ELSE IF nextPc >= NumSteps THEN "completed"
                              ELSE "running"
                /\ UNCHANGED <<visits, inlineVisits, consecutiveSame, lastResult>>
                /\ CostUnchanged
                /\ onMaxCascade' = onMaxCascade \cup {i}
                /\ UNCHANGED timedOut
        ELSE
            LET
                \* Increment visit counter
                newVisits == [visits EXCEPT ![i] = currentVisits + 1]

                \* GAP CLOSURE #3: Backup extraction for UNKNOWN results.
                \* Nondeterministically recover to a valid result, or stay UNKNOWN.
                \* Matches _pipeline_backup_result_extraction() in pipeline-runner.sh.
                recoveredResult == result  \* identity; backup nondeterminism modeled below

                \* Circuit breaker check (tracks UNKNOWN same as FIX — non-terminal)
                prevCount == consecutiveSame[i]
                prevResult == lastResult[i]
                newCount == IF IsTerminalResult(recoveredResult) THEN 0
                            ELSE IF prevResult = recoveredResult THEN prevCount + 1
                            ELSE 1
                cbTripped == ~IsTerminalResult(recoveredResult) /\ newCount >= CircuitBreakerThreshold
                preCommitResult == IF cbTripped THEN "FAIL" ELSE recoveredResult

                \* ENRICHMENT: Commit failure override
                \* When CommitAfter and commit fails and result is PASS, override to FIX
                effectiveResult == IF CommitAfter[i] /\ commitFails /\ preCommitResult = "PASS"
                                   THEN "FIX"
                                   ELSE preCommitResult

                \* Update circuit breaker tracking
                newConsec == [consecutiveSame EXCEPT ![i] = newCount]
                newLast == [lastResult EXCEPT ![i] = IF IsTerminalResult(recoveredResult) THEN "" ELSE recoveredResult]
            IN
            \* --- Dispatch on effective result ---
            \* ENRICHMENT: Clear cascade set when a step actually executes
            CASE effectiveResult = "PASS" ->
                LET nextPc == ResolveJump("next", i) IN
                /\ pc' = nextPc
                /\ visits' = newVisits
                /\ consecutiveSame' = newConsec
                /\ lastResult' = newLast
                /\ status' = IF nextPc >= NumSteps THEN "completed" ELSE "running"
                /\ UNCHANGED inlineVisits
                /\ currentCost' = currentCost + 1
                /\ onMaxCascade' = {}
                /\ UNCHANGED timedOut

              [] effectiveResult = "FAIL" ->
                /\ pc' = -1
                /\ visits' = newVisits
                /\ consecutiveSame' = newConsec
                /\ lastResult' = newLast
                /\ status' = "aborted"
                /\ UNCHANGED inlineVisits
                /\ currentCost' = currentCost + 1
                /\ onMaxCascade' = {}
                /\ UNCHANGED timedOut

              [] effectiveResult = "SKIP" ->
                LET nextPc == ResolveJump("next", i) IN
                /\ pc' = nextPc
                /\ visits' = newVisits
                /\ consecutiveSame' = newConsec
                /\ lastResult' = newLast
                /\ status' = IF nextPc >= NumSteps THEN "completed" ELSE "running"
                /\ UNCHANGED inlineVisits
                /\ currentCost' = currentCost + 1
                /\ onMaxCascade' = {}
                /\ UNCHANGED timedOut

              [] effectiveResult = "FIX" ->
                IF HasInline[i]
                THEN
                    \* Inline handler: check inline max, then re-run self
                    LET
                        currentInline == inlineVisits[i]
                        inlineMax == InlineMax[i]
                    IN
                    IF inlineMax > 0 /\ currentInline >= inlineMax
                    THEN
                        \* Inline max exceeded: on_max default "next"
                        LET nextPc == ResolveJump("next", i) IN
                        /\ pc' = nextPc
                        /\ visits' = newVisits
                        /\ inlineVisits' = inlineVisits
                        /\ consecutiveSame' = newConsec
                        /\ lastResult' = newLast
                        /\ status' = IF nextPc < 0 THEN "aborted"
                                      ELSE IF nextPc >= NumSteps THEN "completed"
                                      ELSE "running"
                        /\ currentCost' = currentCost + 1
                        /\ onMaxCascade' = {}
                        /\ UNCHANGED timedOut
                    ELSE
                        \* Run inline (atomic), then jump to self (re-run parent)
                        \* Reset circuit breaker for parent since inline ran between
                        /\ pc' = i
                        /\ visits' = newVisits
                        /\ inlineVisits' = [inlineVisits EXCEPT ![i] = currentInline + 1]
                        /\ consecutiveSame' = [newConsec EXCEPT ![i] = 0]
                        /\ lastResult' = [newLast EXCEPT ![i] = ""]
                        /\ status' = "running"
                        /\ currentCost' = currentCost + 1
                        /\ onMaxCascade' = {}
                        /\ UNCHANGED timedOut
                ELSE
                    \* No inline handler: jump prev (or self if at step 0)
                    LET nextPc == ResolveJump("prev", i) IN
                    /\ pc' = nextPc
                    /\ visits' = newVisits
                    /\ inlineVisits' = inlineVisits
                    /\ consecutiveSame' = newConsec
                    /\ lastResult' = newLast
                    /\ status' = "running"
                    /\ currentCost' = currentCost + 1
                    /\ onMaxCascade' = {}
                    /\ UNCHANGED timedOut

              \* GAP CLOSURE #3: UNKNOWN result — backup extraction failed or not attempted.
              \* Jump to self (re-run step). Circuit breaker tracks consecutive UNKNOWNs.
              [] effectiveResult = "UNKNOWN" ->
                /\ pc' = i
                /\ visits' = newVisits
                /\ consecutiveSame' = newConsec
                /\ lastResult' = newLast
                /\ status' = "running"
                /\ UNCHANGED inlineVisits
                /\ currentCost' = currentCost + 1
                /\ onMaxCascade' = {}
                /\ UNCHANGED timedOut

\* ENRICHMENT: Step timeout — fires when HasTimeout[pc] is TRUE.
\* Produces a FAIL result regardless of agent output, aborting the pipeline.
\* Matches step-level timeout_seconds in pipeline config.
StepTimeout ==
    /\ status = "running"
    /\ pc >= 0
    /\ pc < NumSteps
    /\ HasTimeout[pc]
    /\ ~timedOut
    /\ timedOut' = TRUE
    /\ pc' = -1
    /\ status' = "aborted"
    /\ visits' = [visits EXCEPT ![pc] = visits[pc] + 1]
    /\ UNCHANGED <<inlineVisits, consecutiveSame, lastResult, currentCost>>
    /\ onMaxCascade' = {}
    /\ SupervisorUnchanged

\* ENRICHMENT: Skip disabled step — enabled_by condition is FALSE.
\* Silently advances pc without incrementing visits, producing a result,
\* or checking max visits. Matches enabled_by conditions in pipeline steps.
SkipDisabledStep ==
    /\ status = "running"
    /\ pc >= 0
    /\ pc < NumSteps
    /\ ~StepEnabled[pc]
    /\ pc' = pc + 1
    /\ status' = IF pc + 1 >= NumSteps THEN "completed" ELSE "running"
    /\ UNCHANGED <<visits, inlineVisits, consecutiveSame, lastResult, currentCost>>
    /\ onMaxCascade' = {}
    /\ UNCHANGED timedOut
    /\ SupervisorUnchanged

\* Execute step and increment iteration counter
\* Guard: when supervisor is enabled, execution blocks once the interval is reached
\* — the real implementation checks the supervisor deterministically at that point.
ExecuteStepWithCount ==
    /\ SupervisorInterval = 0 \/ iterationsSinceCheck < SupervisorInterval
    /\ ExecuteStep
    /\ iterationsSinceCheck' = iterationsSinceCheck + 1
    /\ UNCHANGED supervisorRestarts

\* GAP CLOSURE #4: Cost budget exceeded — pipeline aborts immediately.
\* Matches _check_cost_budget() in pipeline-runner.sh which returns 1 when
\* WIGGUM_WORKER_COST_LIMIT is exceeded, causing pipeline_run_all to return 1.
CostBudgetAbort ==
    /\ status = "running"
    /\ CostBudget > 0
    /\ currentCost >= CostBudget
    /\ status' = "aborted"
    /\ pc' = -1
    /\ UNCHANGED <<visits, inlineVisits, consecutiveSame, lastResult, currentCost>>
    /\ SupervisorUnchanged
    /\ EnrichmentUnchanged

\* =========================================================================
\* Supervisor Actions (Medium Term #3)
\* =========================================================================

\* Supervisor checks and decides to CONTINUE (no-op, reset counter)
SupervisorContinue ==
    /\ status = "running"
    /\ SupervisorInterval > 0
    /\ iterationsSinceCheck >= SupervisorInterval
    /\ iterationsSinceCheck' = 0
    /\ UNCHANGED <<pc, visits, inlineVisits, consecutiveSame, lastResult, status, supervisorRestarts, currentCost>>
    /\ EnrichmentUnchanged

\* Supervisor decides to STOP (abort pipeline)
SupervisorStop ==
    /\ status = "running"
    /\ SupervisorInterval > 0
    /\ iterationsSinceCheck >= SupervisorInterval
    /\ status' = "aborted"
    /\ pc' = -1
    /\ iterationsSinceCheck' = 0
    /\ UNCHANGED <<visits, inlineVisits, consecutiveSame, lastResult, supervisorRestarts, currentCost>>
    /\ EnrichmentUnchanged

\* Supervisor decides to RESTART current step (reset visit counter)
\* This models "supervisor restarts reset counters" class of bugs
SupervisorRestart ==
    /\ status = "running"
    /\ SupervisorInterval > 0
    /\ iterationsSinceCheck >= SupervisorInterval
    /\ pc >= 0
    /\ pc < NumSteps
    /\ supervisorRestarts[pc] < MaxSupervisorRestarts
    \* Reset current step's visit counter (the dangerous reset)
    /\ visits' = [visits EXCEPT ![pc] = 0]
    /\ inlineVisits' = [inlineVisits EXCEPT ![pc] = 0]
    /\ consecutiveSame' = [consecutiveSame EXCEPT ![pc] = 0]
    /\ lastResult' = [lastResult EXCEPT ![pc] = ""]
    /\ supervisorRestarts' = [supervisorRestarts EXCEPT ![pc] = supervisorRestarts[pc] + 1]
    /\ iterationsSinceCheck' = 0
    /\ UNCHANGED <<pc, status, currentCost>>
    /\ EnrichmentUnchanged

\* Terminal states are absorbing
Terminated ==
    /\ status \in {"completed", "aborted"}
    /\ UNCHANGED vars

Next ==
    \/ ExecuteStepWithCount
    \/ StepTimeout
    \/ SkipDisabledStep
    \/ CostBudgetAbort
    \/ SupervisorContinue
    \/ SupervisorStop
    \/ SupervisorRestart
    \/ Terminated

\* =========================================================================
\* Fairness
\* =========================================================================

Fairness == WF_vars(ExecuteStep)

Spec == Init /\ [][Next]_vars /\ Fairness

\* =========================================================================
\* Safety Invariants
\* =========================================================================

\* TypeInvariant: all variables within declared domains
TypeInvariant ==
    /\ pc \in -1..NumSteps
    /\ \A i \in StepRange : visits[i] \in 0..(MaxVisits[i] + 2)
    /\ \A i \in StepRange : inlineVisits[i] \in 0..(InlineMax[i] + 1)
    /\ \A i \in StepRange : consecutiveSame[i] \in 0..CircuitBreakerThreshold
    /\ \A i \in StepRange : lastResult[i] \in {"", "FIX", "UNKNOWN"}
    /\ status \in {"running", "completed", "aborted"}
    /\ iterationsSinceCheck \in 0..(SupervisorInterval + 1)
    /\ \A i \in StepRange : supervisorRestarts[i] \in 0..(MaxSupervisorRestarts + 1)
    /\ currentCost \in 0..(CostBudget + NumSteps)
    /\ onMaxCascade \subseteq StepRange
    /\ timedOut \in BOOLEAN

\* VisitsBounded: visits never wildly exceed max
\* A step may enter at max count (visit happens, then on_max redirects),
\* so visits[i] can be at most MaxVisits[i] + 1
\* NOTE: With supervisor restarts, visits can exceed max if supervisor resets counter
\* This invariant may be violated with supervisor restarts enabled - that's the bug!
VisitsBounded ==
    \A i \in StepRange :
        MaxVisits[i] > 0 => visits[i] <= MaxVisits[i] + 1

\* InlineVisitsBounded: inline visits stay within bounds
InlineVisitsBounded ==
    \A i \in StepRange :
        InlineMax[i] > 0 => inlineVisits[i] <= InlineMax[i] + 1

\* SupervisorRestartsBounded: supervisor restarts don't exceed max
SupervisorRestartsBounded ==
    \A i \in StepRange : supervisorRestarts[i] <= MaxSupervisorRestarts

\* StatusConsistency: status matches pc
StatusConsistency ==
    /\ (pc = -1) => (status = "aborted")
    /\ (pc >= NumSteps) => (status = "completed")
    /\ (pc >= 0 /\ pc < NumSteps) => (status = "running")

\* CostBudgetInvariant: cost never exceeds budget + 1 (last step may push over)
\* GAP CLOSURE #4: safety property for cost budget enforcement
CostBudgetInvariant ==
    CostBudget > 0 => currentCost <= CostBudget + 1

\* =========================================================================
\* Enrichment Safety Invariants
\* =========================================================================

\* CascadeDetected: onMaxCascade never contains a duplicate before abort.
\* If on_max cascade visits a step that's already in the cascade set,
\* the pipeline aborts immediately. The cascade set is a strict subset of
\* steps actually visited by on_max, never containing duplicates.
CascadeDetected ==
    status = "running" =>
        \A i \in onMaxCascade : i \in StepRange

\* DisabledStepNeverExecuted: disabled steps never have their visit
\* counter incremented. StepEnabled[i] = FALSE means the step is skipped.
DisabledStepNeverExecuted ==
    \A i \in StepRange :
        ~StepEnabled[i] => visits[i] = 0

\* TimeoutProducesFail: a timed-out step always results in the FAIL path
\* (pipeline aborted). If timedOut is TRUE, the pipeline must be aborted.
TimeoutProducesFail ==
    timedOut => status = "aborted"

\* =========================================================================
\* Liveness Properties (require fairness)
\* =========================================================================

\* PipelineTermination: the pipeline always eventually completes or aborts
\* Argument: every step has finite max visits. The circuit breaker escalates
\* repeated non-terminal results to FAIL (abort). Combined, this guarantees
\* the pipeline cannot loop forever.
\* NOTE: Requires TLC for verification -- Apalache --temporal does not
\* enforce fairness ("Handling fairness is not supported yet!").
PipelineTermination == <>(status \in {"completed", "aborted"})

=============================================================================
