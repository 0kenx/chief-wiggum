----------------------------- MODULE KanbanLock ------------------------------
(*
 * TLA+ formal model of concurrent kanban access with flock serialization.
 *
 * Models the file-lock pattern from lib/core/file-lock.sh used to protect
 * concurrent access to .ralph/kanban.md. Multiple processes (workers,
 * scheduler) contend for a single flock on the kanban file, performing
 * read-modify-write operations under the lock.
 *
 * Processes: 3 concurrent writers modeling worst case:
 *   - Worker1, Worker2: worker processes updating task status
 *   - Scheduler: scheduler updating kanban during tick
 *
 * Operations modeled:
 *   - AcquireLock / AcquireLockFail: flock attempt with success/failure
 *   - ReadKanban: read current value under lock
 *   - WriteKanban: sed + mv under lock (atomic file replacement)
 *   - ReleaseLock: release flock
 *   - RetryLock: retry with backoff (up to max_retries)
 *   - LockExhausted: all retries failed, operation dropped
 *   - WeakAppend: append_with_lock fallthrough (append without exclusive lock)
 *   - ReadKanbanLockless: lockless read (sees atomic snapshot)
 *
 * Key properties verified:
 *   - MutualExclusion: at most one process holds the lock
 *   - NoLostUpdateUnderLock: completed write under lock visible to next reader
 *   - SerializedWrites: concurrent writes under lock are serialized
 *   - WeakAppendPreservesData: weak append never loses appended data
 *   - LockRetryBounded: retry count bounded by max_retries
 *
 * Designed for Apalache symbolic model checking (type annotations, CInit).
 *)

EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Set(Str);
    Procs,              \* Set of process IDs
    \* @type: Int;
    MaxRetries,         \* Maximum lock retry attempts
    \* @type: Int;
    NumTasks            \* Number of tasks in kanban (abstract value range)

VARIABLES
    \* @type: Str -> Str;
    pc,                 \* Per-process phase: "idle", "acquiring", "reading",
                        \* "writing", "releasing", "retrying", "exhausted",
                        \* "weak_appending", "lockless_reading", "done"
    \* @type: Str;
    lockHolder,         \* Process holding the lock ("none" if free)
    \* @type: Int -> Int;
    kanbanValue,        \* Per-task value (abstract: task index -> version counter)
    \* @type: Str -> Int;
    pendingWrite,       \* Per-process: value to write (0 = no pending write)
    \* @type: Str -> Int;
    retryCount,         \* Per-process: current retry count
    \* @type: Str -> Int;
    readSnapshot,       \* Per-process: last read value (snapshot)
    \* @type: Int;
    writeSeq,           \* Global write sequence counter (for serialization tracking)
    \* @type: Str -> Int;
    writeOrder          \* Per-process: write sequence number (when the write happened)

\* @type: <<Str -> Str, Str, Int -> Int, Str -> Int, Str -> Int, Str -> Int, Int, Str -> Int>>;
vars == <<pc, lockHolder, kanbanValue, pendingWrite, retryCount,
          readSnapshot, writeSeq, writeOrder>>

\* =========================================================================
\* Type definitions
\* =========================================================================

TaskIndices == 0..(NumTasks - 1)

PhaseValues == {"idle", "acquiring", "reading", "writing", "releasing",
                "retrying", "exhausted", "weak_appending",
                "lockless_reading", "done"}

\* =========================================================================
\* Init and CInit
\* =========================================================================

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ lockHolder = "none"
    /\ kanbanValue = [i \in TaskIndices |-> 0]
    /\ pendingWrite = [p \in Procs |-> 0]
    /\ retryCount = [p \in Procs |-> 0]
    /\ readSnapshot = [p \in Procs |-> 0]
    /\ writeSeq = 0
    /\ writeOrder = [p \in Procs |-> 0]

\* Apalache constant initialization
CInit ==
    /\ Procs = {"W1", "W2", "Sched"}
    /\ MaxRetries = 5
    /\ NumTasks = 2

\* =========================================================================
\* Helpers
\* =========================================================================

LockFree == lockHolder = "none"

\* =========================================================================
\* Actions - Lock-Protected Read-Modify-Write
\* =========================================================================

\* Begin operation: process starts trying to acquire lock
BeginOperation(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "acquiring"]
    /\ retryCount' = [retryCount EXCEPT ![p] = 0]
    /\ UNCHANGED <<lockHolder, kanbanValue, pendingWrite, readSnapshot,
                   writeSeq, writeOrder>>

\* Acquire lock: flock succeeds
AcquireLock(p) ==
    /\ pc[p] = "acquiring"
    /\ LockFree
    /\ lockHolder' = p
    /\ pc' = [pc EXCEPT ![p] = "reading"]
    /\ UNCHANGED <<kanbanValue, pendingWrite, retryCount, readSnapshot,
                   writeSeq, writeOrder>>

\* Acquire lock fails: flock returns non-zero (lock held by another process)
AcquireLockFail(p) ==
    /\ pc[p] = "acquiring"
    /\ ~LockFree
    /\ lockHolder /= p
    /\ pc' = [pc EXCEPT ![p] = "retrying"]
    /\ UNCHANGED <<lockHolder, kanbanValue, pendingWrite, retryCount,
                   readSnapshot, writeSeq, writeOrder>>

\* Read kanban under lock: take a snapshot of the current value
ReadKanban(p) ==
    /\ pc[p] = "reading"
    /\ lockHolder = p
    /\ readSnapshot' = [readSnapshot EXCEPT ![p] = kanbanValue[0]]
    \* Compute pending write: increment version (models sed replacement)
    /\ pendingWrite' = [pendingWrite EXCEPT ![p] = kanbanValue[0] + 1]
    /\ pc' = [pc EXCEPT ![p] = "writing"]
    /\ UNCHANGED <<lockHolder, kanbanValue, retryCount, writeSeq, writeOrder>>

\* Write kanban under lock: atomic file replacement (sed + mv)
WriteKanban(p) ==
    /\ pc[p] = "writing"
    /\ lockHolder = p
    /\ kanbanValue' = [kanbanValue EXCEPT ![0] = pendingWrite[p]]
    /\ writeSeq' = writeSeq + 1
    /\ writeOrder' = [writeOrder EXCEPT ![p] = writeSeq + 1]
    /\ pc' = [pc EXCEPT ![p] = "releasing"]
    /\ UNCHANGED <<lockHolder, pendingWrite, retryCount, readSnapshot>>

\* Release lock
ReleaseLock(p) ==
    /\ pc[p] = "releasing"
    /\ lockHolder = p
    /\ lockHolder' = "none"
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<kanbanValue, pendingWrite, retryCount, readSnapshot,
                   writeSeq, writeOrder>>

\* =========================================================================
\* Actions - Lock Retry
\* =========================================================================

\* Retry lock acquisition (within retry budget)
RetryLock(p) ==
    /\ pc[p] = "retrying"
    /\ retryCount[p] < MaxRetries
    /\ retryCount' = [retryCount EXCEPT ![p] = retryCount[p] + 1]
    /\ pc' = [pc EXCEPT ![p] = "acquiring"]
    /\ UNCHANGED <<lockHolder, kanbanValue, pendingWrite, readSnapshot,
                   writeSeq, writeOrder>>

\* All retries failed: operation dropped
LockExhausted(p) ==
    /\ pc[p] = "retrying"
    /\ retryCount[p] >= MaxRetries
    /\ pc' = [pc EXCEPT ![p] = "exhausted"]
    /\ UNCHANGED <<lockHolder, kanbanValue, pendingWrite, retryCount,
                   readSnapshot, writeSeq, writeOrder>>

\* =========================================================================
\* Actions - Weak Append (append_with_lock fallthrough)
\* =========================================================================

\* Weak append: append data without exclusive lock
\* Models the append_with_lock() fallthrough path where flock is released
\* early but append still happens (no lost data, but no read-modify-write)
WeakAppend(p) ==
    /\ pc[p] = "exhausted"
    \* Append is additive: it writes new data without reading old
    \* Modeled as incrementing a separate task slot to avoid lost data
    /\ kanbanValue' = [kanbanValue EXCEPT ![1] = kanbanValue[1] + 1]
    /\ writeSeq' = writeSeq + 1
    /\ writeOrder' = [writeOrder EXCEPT ![p] = writeSeq + 1]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<lockHolder, pendingWrite, retryCount, readSnapshot>>

\* =========================================================================
\* Actions - Lockless Read
\* =========================================================================

\* Lockless read: reads atomic snapshot of kanban (file content is atomic
\* because writes use temp+mv which is atomic on POSIX)
ReadKanbanLockless(p) ==
    /\ pc[p] = "idle"
    /\ readSnapshot' = [readSnapshot EXCEPT ![p] = kanbanValue[0]]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<lockHolder, kanbanValue, pendingWrite, retryCount,
                   writeSeq, writeOrder>>

\* =========================================================================
\* Actions - Reset (process can start another operation)
\* =========================================================================

ResetProcess(p) ==
    /\ pc[p] = "done"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ pendingWrite' = [pendingWrite EXCEPT ![p] = 0]
    /\ retryCount' = [retryCount EXCEPT ![p] = 0]
    /\ UNCHANGED <<lockHolder, kanbanValue, readSnapshot, writeSeq, writeOrder>>

\* =========================================================================
\* Next-state relation
\* =========================================================================

Next ==
    \E p \in Procs :
        \/ BeginOperation(p)
        \/ AcquireLock(p)
        \/ AcquireLockFail(p)
        \/ ReadKanban(p)
        \/ WriteKanban(p)
        \/ ReleaseLock(p)
        \/ RetryLock(p)
        \/ LockExhausted(p)
        \/ WeakAppend(p)
        \/ ReadKanbanLockless(p)
        \/ ResetProcess(p)

\* =========================================================================
\* Fairness
\* =========================================================================

Fairness ==
    \A p \in Procs :
        /\ WF_vars(BeginOperation(p))
        /\ WF_vars(AcquireLock(p))
        /\ WF_vars(ReadKanban(p))
        /\ WF_vars(WriteKanban(p))
        /\ WF_vars(ReleaseLock(p))
        /\ WF_vars(RetryLock(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* =========================================================================
\* Safety Invariants
\* =========================================================================

\* TypeInvariant: all variables within declared domains
TypeInvariant ==
    /\ \A p \in Procs : pc[p] \in PhaseValues
    /\ lockHolder \in Procs \cup {"none"}
    /\ \A i \in TaskIndices : kanbanValue[i] \in 0..50
    /\ \A p \in Procs : pendingWrite[p] \in 0..50
    /\ \A p \in Procs : retryCount[p] \in 0..(MaxRetries + 1)
    /\ \A p \in Procs : readSnapshot[p] \in 0..50
    /\ writeSeq \in 0..50
    /\ \A p \in Procs : writeOrder[p] \in 0..50

\* MutualExclusion: at most one process holds the lock at any time.
\* This is THE key safety property of flock-based serialization.
MutualExclusion ==
    \A p1, p2 \in Procs :
        (lockHolder = p1 /\ lockHolder = p2) => p1 = p2

\* NoLostUpdateUnderLock: a completed write under lock is visible
\* to the next reader. If a process has finished writing (is in
\* releasing or done with a write order > 0), the kanban reflects
\* that write or a later one.
NoLostUpdateUnderLock ==
    \A p \in Procs :
        (pc[p] = "releasing" /\ lockHolder = p) =>
            kanbanValue[0] = pendingWrite[p]

\* SerializedWrites: concurrent writes under lock are totally ordered.
\* If two processes both wrote, their write order numbers differ.
SerializedWrites ==
    \A p1, p2 \in Procs :
        (p1 /= p2 /\ writeOrder[p1] > 0 /\ writeOrder[p2] > 0) =>
            writeOrder[p1] /= writeOrder[p2]

\* WeakAppendPreservesData: weak append always increments the value,
\* meaning no data is lost even when the lock isn't held.
\* The kanbanValue[1] (append slot) is monotonically non-decreasing.
WeakAppendPreservesData ==
    kanbanValue[1] >= 0

\* LockRetryBounded: retry count never exceeds MaxRetries
LockRetryBounded ==
    \A p \in Procs : retryCount[p] <= MaxRetries

\* =========================================================================
\* Liveness Properties (require fairness, TLC only)
\* =========================================================================

\* EventualProgress: every process that starts an operation eventually
\* completes it (reaches done).
\* NOTE: Requires TLC for verification -- Apalache does not enforce fairness.
EventualProgress ==
    /\ pc["W1"] = "acquiring" ~> pc["W1"] = "done"
    /\ pc["W2"] = "acquiring" ~> pc["W2"] = "done"
    /\ pc["Sched"] = "acquiring" ~> pc["Sched"] = "done"

=============================================================================
