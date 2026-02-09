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
 *   - Jump target resolution: self, prev, next, abort
 *
 * The 3-step pipeline exercises:
 *   Step 0: No inline handler (FIX -> jump prev, clamped to self at step 0)
 *   Step 1: Has inline handler (FIX -> run inline, then re-run self)
 *   Step 2: Has inline handler (FIX -> run inline, then re-run self)
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
    CircuitBreakerThreshold

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
    status             \* "running", "completed", "aborted"

\* @type: <<Int, Int -> Int, Int -> Int, Int -> Int, Int -> Str, Str>>;
vars == <<pc, visits, inlineVisits, consecutiveSame, lastResult, status>>

\* =========================================================================
\* Type definitions
\* =========================================================================

StepRange == 0..(NumSteps - 1)
Results == {"PASS", "FAIL", "FIX", "SKIP"}

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

\* Apalache constant initialization
CInit ==
    /\ NumSteps = 3
    /\ MaxVisits = [i \in 0..2 |-> IF i = 0 THEN 2 ELSE 3]
    /\ HasInline = [i \in 0..2 |-> IF i = 0 THEN FALSE ELSE TRUE]
    /\ InlineMax = [i \in 0..2 |-> IF i = 0 THEN 0 ELSE 2]
    /\ CircuitBreakerThreshold = 3

\* =========================================================================
\* Helpers
\* =========================================================================

\* Resolve jump target to step index
\* @type: (Str, Int) => Int;
ResolveJump(target, current) ==
    CASE target = "self"  -> current
      [] target = "next"  -> current + 1
      [] target = "prev"  -> IF current > 0 THEN current - 1 ELSE 0
      [] target = "abort" -> -1
      [] OTHER            -> -1

\* Check if a result is terminal for the step (resets circuit breaker)
\* @type: (Str) => Bool;
IsTerminalResult(r) == r \in {"PASS", "FAIL", "SKIP"}

\* =========================================================================
\* Actions
\* =========================================================================

\* Execute a pipeline step: nondeterministically choose a result and dispatch
ExecuteStep ==
    /\ status = "running"
    /\ pc >= 0
    /\ pc < NumSteps
    /\ \E result \in Results :
        LET
            i == pc
            currentVisits == visits[i]
            maxV == MaxVisits[i]
        IN
        \* --- Check max visits first ---
        IF maxV > 0 /\ currentVisits >= maxV
        THEN
            \* on_max fires: default jump is "next"
            LET nextPc == ResolveJump("next", i) IN
            /\ pc' = nextPc
            /\ status' = IF nextPc < 0 THEN "aborted"
                          ELSE IF nextPc >= NumSteps THEN "completed"
                          ELSE "running"
            /\ UNCHANGED <<visits, inlineVisits, consecutiveSame, lastResult>>
        ELSE
            LET
                \* Increment visit counter
                newVisits == [visits EXCEPT ![i] = currentVisits + 1]

                \* Circuit breaker check
                prevCount == consecutiveSame[i]
                prevResult == lastResult[i]
                newCount == IF IsTerminalResult(result) THEN 0
                            ELSE IF prevResult = result THEN prevCount + 1
                            ELSE 1
                cbTripped == ~IsTerminalResult(result) /\ newCount >= CircuitBreakerThreshold
                effectiveResult == IF cbTripped THEN "FAIL" ELSE result

                \* Update circuit breaker tracking
                newConsec == [consecutiveSame EXCEPT ![i] = newCount]
                newLast == [lastResult EXCEPT ![i] = IF IsTerminalResult(result) THEN "" ELSE result]
            IN
            \* --- Dispatch on effective result ---
            CASE effectiveResult = "PASS" ->
                LET nextPc == ResolveJump("next", i) IN
                /\ pc' = nextPc
                /\ visits' = newVisits
                /\ consecutiveSame' = newConsec
                /\ lastResult' = newLast
                /\ status' = IF nextPc >= NumSteps THEN "completed" ELSE "running"
                /\ UNCHANGED inlineVisits

              [] effectiveResult = "FAIL" ->
                /\ pc' = -1
                /\ visits' = newVisits
                /\ consecutiveSame' = newConsec
                /\ lastResult' = newLast
                /\ status' = "aborted"
                /\ UNCHANGED inlineVisits

              [] effectiveResult = "SKIP" ->
                LET nextPc == ResolveJump("next", i) IN
                /\ pc' = nextPc
                /\ visits' = newVisits
                /\ consecutiveSame' = newConsec
                /\ lastResult' = newLast
                /\ status' = IF nextPc >= NumSteps THEN "completed" ELSE "running"
                /\ UNCHANGED inlineVisits

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
                    ELSE
                        \* Run inline (atomic), then jump to self (re-run parent)
                        \* Reset circuit breaker for parent since inline ran between
                        /\ pc' = i
                        /\ visits' = newVisits
                        /\ inlineVisits' = [inlineVisits EXCEPT ![i] = currentInline + 1]
                        /\ consecutiveSame' = [newConsec EXCEPT ![i] = 0]
                        /\ lastResult' = [newLast EXCEPT ![i] = ""]
                        /\ status' = "running"
                ELSE
                    \* No inline handler: jump prev (or self if at step 0)
                    LET nextPc == ResolveJump("prev", i) IN
                    /\ pc' = nextPc
                    /\ visits' = newVisits
                    /\ inlineVisits' = inlineVisits
                    /\ consecutiveSame' = newConsec
                    /\ lastResult' = newLast
                    /\ status' = "running"

\* Terminal states are absorbing
Terminated ==
    /\ status \in {"completed", "aborted"}
    /\ UNCHANGED vars

Next == ExecuteStep \/ Terminated

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
    /\ \A i \in StepRange : lastResult[i] \in {"", "FIX"}
    /\ status \in {"running", "completed", "aborted"}

\* VisitsBounded: visits never wildly exceed max
\* A step may enter at max count (visit happens, then on_max redirects),
\* so visits[i] can be at most MaxVisits[i] + 1
VisitsBounded ==
    \A i \in StepRange :
        MaxVisits[i] > 0 => visits[i] <= MaxVisits[i] + 1

\* InlineVisitsBounded: inline visits stay within bounds
InlineVisitsBounded ==
    \A i \in StepRange :
        InlineMax[i] > 0 => inlineVisits[i] <= InlineMax[i] + 1

\* StatusConsistency: status matches pc
StatusConsistency ==
    /\ (pc = -1) => (status = "aborted")
    /\ (pc >= NumSteps) => (status = "completed")
    /\ (pc >= 0 /\ pc < NumSteps) => (status = "running")

\* =========================================================================
\* Liveness Properties (require fairness)
\* =========================================================================

\* PipelineTermination: the pipeline always eventually completes or aborts
\* Argument: every step has finite max visits. The circuit breaker escalates
\* repeated non-terminal results to FAIL (abort). Combined, this guarantees
\* the pipeline cannot loop forever.
PipelineTermination == <>(status \in {"completed", "aborted"})

=============================================================================
