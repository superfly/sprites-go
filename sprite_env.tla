---------------------------- MODULE sprite_env ----------------------------

EXTENDS Integers, Sequences, FiniteSets

VARIABLES 
    overallState,           \* Overall application state
    componentSetState,      \* Derived state of all storage components
    dbState,               \* Individual DB component state
    fsState,               \* Individual FS component state
    processState,          \* Supervised process state
    processExitCode,
    checkpointInProgress,
    restoreInProgress,
    errorType,
    restartAttempt,
    restartDelay,
    shutdownInProgress,
    exitRequested,
    signalReceived,
    dbShutdownTimeout,
    fsShutdownTimeout,
    dbForceKilled,
    fsForceKilled

vars == <<overallState, componentSetState, dbState, fsState, processState, processExitCode, checkpointInProgress, restoreInProgress, errorType, restartAttempt, restartDelay, shutdownInProgress, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

\* State definitions
States == {
    "Initializing",
    "Running",
    "Checkpointing",
    "Restoring",
    "Error",
    "Shutdown"
}

\* Process management states
ProcessStates == {
    "Stopped",      \* Process is not running
    "Starting",     \* Process is being started
    "Running",      \* Process is running normally
    "Stopping",     \* Process is being stopped
    "Signaling",    \* Process is being sent a signal
    "Crashed",      \* Process exited unexpectedly
    "Exited",       \* Process exited with a code
    "Killed",       \* Process was forcefully terminated
    "Error"         \* Process failed to start/stop
}

\* Error types
ErrorTypes == {
    "None",
    "DBError",
    "FSError",
    "ProcessError",
    "ProcessCrash",
    "ProcessKilled",
    "CheckpointError",
    "RestoreError",
    "StartupError",
    "ComponentSetError"
}

\* Signal definitions
Signals == {
    "None",
    "SIGTERM",  \* Graceful shutdown
    "SIGINT",   \* Graceful shutdown
    "SIGKILL"   \* Force kill
}

\* Initial state
Init == 
    /\ overallState = "Initializing"
    /\ componentSetState = "Initializing"
    /\ dbState = "Initializing"
    /\ fsState = "Initializing"
    /\ processState = "Stopped"
    /\ processExitCode = 0
    /\ checkpointInProgress = FALSE
    /\ restoreInProgress = FALSE
    /\ errorType = "None"
    /\ restartAttempt = 0
    /\ restartDelay = 0
    /\ shutdownInProgress = FALSE
    /\ exitRequested = FALSE
    /\ signalReceived = "None"
    /\ dbShutdownTimeout = 0
    /\ fsShutdownTimeout = 0
    /\ dbForceKilled = FALSE
    /\ fsForceKilled = FALSE

\* Helper predicates
IsRunning(state) == state = "Running"
IsError(state) == state = "Error"
IsInitializing(state) == state = "Initializing"
IsCheckpointing(state) == state = "Checkpointing"
IsRestoring(state) == state = "Restoring"
IsStopped(state) == state = "Stopped"
IsOperationInProgress == checkpointInProgress \/ restoreInProgress \/ IsInitializing(componentSetState)
IsGracefulSignal(signal) == signal \in {"SIGTERM", "SIGINT"}
IsForceKillSignal(signal) == signal = "SIGKILL"

\* State components
StateComponents == <<dbState, fsState>>

\* State checks using sequence operators
AllComponentsRunning == \A state \in StateComponents : IsRunning(state)
AnyComponentError == \E state \in StateComponents : IsError(state)
AnyComponentInitializing == \E state \in StateComponents : IsInitializing(state)
AnyComponentCheckpointing == \E state \in StateComponents : IsCheckpointing(state)
AnyComponentRestoring == \E state \in StateComponents : IsRestoring(state)

\* Component Set State Derivation
\* The component set state is derived from all individual component states
DetermineComponentSetState ==
    IF AnyComponentError THEN
        "Error"
    ELSE IF AnyComponentInitializing THEN
        "Initializing"
    ELSE IF AnyComponentCheckpointing THEN
        "Checkpointing"
    ELSE IF AnyComponentRestoring THEN
        "Restoring"
    ELSE IF AllComponentsRunning THEN
        "Running"
    ELSE IF shutdownInProgress /\ \A state \in StateComponents : state = "Shutdown" THEN
        "Shutdown"
    ELSE
        componentSetState

\* Concurrent operation predicates
CanOperateConcurrently ==
    /\ ~(dbState = "Error" => fsState = "Error")
    /\ ~(fsState = "Error" => dbState = "Error")
    /\ ~(dbState = "Initializing" => fsState = "Initializing")
    /\ ~(fsState = "Initializing" => dbState = "Initializing")
    /\ ~(dbState = "Checkpointing" => fsState = "Checkpointing")
    /\ ~(fsState = "Checkpointing" => dbState = "Checkpointing")
    /\ ~(dbState = "Restoring" => fsState = "Restoring")
    /\ ~(fsState = "Restoring" => dbState = "Restoring")

\* State transitions for DB and FS
StateTransition(state, component) ==
    IF state = "Initializing" THEN
        "Running"
    ELSE IF state = "Running" /\ checkpointInProgress THEN
        "Checkpointing"
    ELSE IF state = "Checkpointing" THEN
        "Running"
    ELSE IF state = "Running" /\ restoreInProgress THEN
        "Restoring"
    ELSE IF state = "Restoring" THEN
        "Running"
    ELSE IF state = "Running" /\ shutdownInProgress THEN
        "Shutdown"
    ELSE
        state

\* Process state transitions
ProcessTransition(state, exitCode) ==
    IF state = "Stopped" /\ IsRunning(componentSetState) /\ ~shutdownInProgress /\ ~restoreInProgress THEN
        "Starting"
    ELSE IF state = "Starting" THEN
        "Running"
    ELSE IF state = "Running" /\ restoreInProgress THEN
        "Stopping"
    ELSE IF state = "Stopping" THEN
        "Stopped"
    ELSE IF state = "Running" /\ exitCode # 0 THEN
        IF exitCode = -15 THEN  \* SIGTERM
            "Exited"
        ELSE IF exitCode < 0 THEN
            "Crashed"
        ELSE
            "Exited"
    ELSE IF state = "Signaling" /\ exitCode = -9 THEN  \* SIGKILL
        "Killed"
    ELSE
        state

\* Error state determination
DetermineErrorType ==
    IF componentSetState = "Error" THEN
        IF dbState = "Error" THEN
            "DBError"
        ELSE IF fsState = "Error" THEN
            "FSError"
        ELSE
            "ComponentSetError"
    ELSE IF processState = "Error" THEN
        "ProcessError"
    ELSE IF processState = "Crashed" THEN
        "ProcessCrash"
    ELSE IF processState = "Killed" THEN
        "ProcessKilled"
    ELSE IF checkpointInProgress /\ componentSetState = "Error" THEN
        "CheckpointError"
    ELSE IF restoreInProgress /\ componentSetState = "Error" THEN
        "RestoreError"
    ELSE IF componentSetState = "Initializing" /\ AnyComponentError THEN
        "StartupError"
    ELSE
        "None"

\* Calculate next restart delay (exponential backoff)
NextRestartDelay ==
    IF restartAttempt = 0 THEN
        1
    ELSE
        IF restartDelay * 2 > 60 THEN 60 ELSE restartDelay * 2  \* Cap at 60 seconds

\* Next state relation
Next ==
    \/ \* Normal operation
        /\ checkpointInProgress' = checkpointInProgress
        /\ restoreInProgress' = restoreInProgress
        /\ shutdownInProgress' = shutdownInProgress
        /\ dbState' = StateTransition(dbState, "DB")
        /\ fsState' = StateTransition(fsState, "FS")
        /\ componentSetState' = DetermineComponentSetState
        /\ processState' = ProcessTransition(processState, processExitCode)
        /\ processExitCode' = processExitCode
        /\ errorType' = DetermineErrorType
        /\ restartAttempt' = restartAttempt
        /\ restartDelay' = restartDelay
        /\ exitRequested' = exitRequested
        /\ signalReceived' = "None"
        /\ overallState' = 
            IF errorType' # "None" THEN
                "Error"
            ELSE IF componentSetState' = "Initializing" THEN
                "Initializing"
            ELSE IF componentSetState' = "Checkpointing" THEN
                "Checkpointing"
            ELSE IF componentSetState' = "Restoring" THEN
                "Restoring"
            ELSE IF componentSetState' = "Running" /\ processState = "Running" THEN
                "Running"
            ELSE IF componentSetState' = "Shutdown" /\ processState = "Stopped" THEN
                "Shutdown"
            ELSE
                overallState

    \/ \* Process exit
        /\ processState = "Running"
        /\ processExitCode' \in {0..255} \cup {-1..-255}
        /\ UNCHANGED <<overallState, componentSetState, dbState, fsState, processState, checkpointInProgress, restoreInProgress, errorType, restartAttempt, restartDelay, shutdownInProgress, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

    \/ \* Process restart after crash/exit
        /\ processState \in {"Crashed", "Exited"}
        /\ ~shutdownInProgress
        /\ restartAttempt' = restartAttempt + 1
        /\ restartDelay' = NextRestartDelay
        /\ processState' = "Starting"
        /\ UNCHANGED <<overallState, componentSetState, dbState, fsState, processExitCode, checkpointInProgress, restoreInProgress, errorType, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

    \/ \* Receive signal
        /\ signalReceived' \in {"SIGTERM", "SIGINT", "SIGKILL"}
        /\ processState = "Running"
        /\ processState' = "Signaling"
        \* Forward signal to process first
        /\ processExitCode' = 
            IF signalReceived' = "SIGTERM" THEN -15
            ELSE IF signalReceived' = "SIGINT" THEN -2
            ELSE -9
        \* After process handles signal, state components will receive it
        /\ dbState' = IF signalReceived' = "SIGKILL" THEN "Error" ELSE dbState
        /\ fsState' = IF signalReceived' = "SIGKILL" THEN "Error" ELSE fsState
        /\ componentSetState' = DetermineComponentSetState
        \* Graceful signals trigger shutdown sequence
        /\ shutdownInProgress' = IF IsGracefulSignal(signalReceived') THEN TRUE ELSE shutdownInProgress
        \* Force kill signals trigger immediate error
        /\ errorType' = IF IsForceKillSignal(signalReceived') THEN "ProcessKilled" ELSE errorType
        /\ UNCHANGED <<restartAttempt, restartDelay, checkpointInProgress, restoreInProgress, exitRequested, overallState>>

    \/ \* Start graceful shutdown (after operations complete)
        /\ exitRequested
        /\ ~shutdownInProgress
        /\ ~IsOperationInProgress
        /\ shutdownInProgress' = TRUE
        /\ processState' = "Signaling"  \* Send SIGTERM first
        /\ processExitCode' = -15
        /\ signalReceived' = "SIGTERM"
        /\ UNCHANGED <<dbState, fsState, componentSetState, restartAttempt, restartDelay, checkpointInProgress, restoreInProgress, errorType, overallState>>

    \/ \* Force kill after graceful shutdown timeout
        /\ shutdownInProgress
        /\ processState = "Signaling"
        /\ processState' = "Stopping"  \* Send SIGKILL
        /\ processExitCode' = -9
        /\ signalReceived' = "SIGKILL"
        /\ UNCHANGED <<dbState, fsState, componentSetState, restartAttempt, restartDelay, checkpointInProgress, restoreInProgress, errorType, overallState>>

    \/ \* Concurrent state component operations
        /\ dbState' = StateTransition(dbState, "DB")
        /\ fsState' = StateTransition(fsState, "FS")
        /\ componentSetState' = DetermineComponentSetState
        /\ CanOperateConcurrently
        /\ UNCHANGED <<overallState, processState, processExitCode, checkpointInProgress, restoreInProgress, errorType, restartAttempt, restartDelay, shutdownInProgress, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

    \/ \* Start checkpoint
        /\ checkpointInProgress = FALSE
        /\ checkpointInProgress' = TRUE
        /\ UNCHANGED <<restoreInProgress, dbState, fsState, componentSetState, processState, errorType, overallState>>

    \/ \* Complete checkpoint
        /\ checkpointInProgress = TRUE
        /\ checkpointInProgress' = FALSE
        /\ UNCHANGED <<restoreInProgress, dbState, fsState, componentSetState, processState, errorType, overallState>>

    \/ \* Start restore
        /\ restoreInProgress = FALSE
        /\ restoreInProgress' = TRUE
        /\ UNCHANGED <<checkpointInProgress, dbState, fsState, componentSetState, processState, errorType, overallState>>

    \/ \* Complete restore
        /\ restoreInProgress = TRUE
        /\ restoreInProgress' = FALSE
        /\ UNCHANGED <<checkpointInProgress, dbState, fsState, componentSetState, processState, errorType, overallState>>

    \/ \* Begin shutdown: start timeouts
        /\ shutdownInProgress
        /\ dbState = "Running"
        /\ fsState = "Running"
        /\ dbShutdownTimeout' = 3
        /\ fsShutdownTimeout' = 3
        /\ dbForceKilled' = FALSE
        /\ fsForceKilled' = FALSE
        /\ dbState' = "Shutdown"
        /\ fsState' = "Shutdown"
        /\ componentSetState' = DetermineComponentSetState
        /\ UNCHANGED <<overallState, processState>>

    \/ \* Decrement DB shutdown timeout if not yet zero
        /\ shutdownInProgress
        /\ dbShutdownTimeout > 0
        /\ dbState = "Shutdown"
        /\ dbShutdownTimeout' = dbShutdownTimeout - 1
        /\ UNCHANGED <<fsShutdownTimeout, dbState, fsState, componentSetState, overallState, processState, processExitCode, checkpointInProgress, restoreInProgress, errorType, restartAttempt, restartDelay, exitRequested, signalReceived, dbForceKilled, fsForceKilled>>

    \/ \* Decrement FS shutdown timeout if not yet zero
        /\ shutdownInProgress
        /\ fsShutdownTimeout > 0
        /\ fsState = "Shutdown"
        /\ fsShutdownTimeout' = fsShutdownTimeout - 1
        /\ UNCHANGED <<dbShutdownTimeout, dbState, fsState, componentSetState, overallState, processState, processExitCode, checkpointInProgress, restoreInProgress, errorType, restartAttempt, restartDelay, exitRequested, signalReceived, dbForceKilled, fsForceKilled>>

    \/ \* Force kill DB if timeout expires
        /\ shutdownInProgress
        /\ dbShutdownTimeout = 0
        /\ dbState = "Shutdown"
        /\ ~dbForceKilled
        /\ dbForceKilled' = TRUE
        /\ dbState' = "Error"
        /\ componentSetState' = DetermineComponentSetState
        /\ UNCHANGED <<overallState, fsState, processState, processExitCode, checkpointInProgress, restoreInProgress, errorType, restartAttempt, restartDelay, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, fsForceKilled>>

    \/ \* Force kill FS if timeout expires
        /\ shutdownInProgress
        /\ fsShutdownTimeout = 0
        /\ fsState = "Shutdown"
        /\ ~fsForceKilled
        /\ fsForceKilled' = TRUE
        /\ fsState' = "Error"
        /\ componentSetState' = DetermineComponentSetState
        /\ UNCHANGED <<overallState, dbState, processState, processExitCode, checkpointInProgress, restoreInProgress, errorType, restartAttempt, restartDelay, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled>>

    \/ \* Crash app after all shutdowns and any force kill
        /\ shutdownInProgress
        /\ ((dbState = "Error" /\ dbForceKilled) \/ (fsState = "Error" /\ fsForceKilled))
        /\ dbShutdownTimeout = 0
        /\ fsShutdownTimeout = 0
        /\ overallState' = "Error"
        /\ errorType' = "FSError"
        /\ UNCHANGED <<dbState, fsState, componentSetState, processState>>

\* Invariants
TypeOK ==
    /\ overallState \in States
    /\ componentSetState \in States
    /\ dbState \in States
    /\ fsState \in States
    /\ processState \in ProcessStates
    /\ processExitCode \in {0..255} \cup {-1..-255}
    /\ checkpointInProgress \in BOOLEAN
    /\ restoreInProgress \in BOOLEAN
    /\ errorType \in ErrorTypes
    /\ restartAttempt \in Nat
    /\ restartDelay \in Nat
    /\ shutdownInProgress \in BOOLEAN
    /\ exitRequested \in BOOLEAN
    /\ signalReceived \in Signals
    /\ dbShutdownTimeout \in Nat
    /\ fsShutdownTimeout \in Nat
    /\ dbForceKilled \in BOOLEAN
    /\ fsForceKilled \in BOOLEAN

\* Safety properties
Safety ==
    /\ \* Can't be checkpointing and restoring at the same time
        ~(checkpointInProgress /\ restoreInProgress)
    /\ \* Process must be stopped during restore
        (restoreInProgress => processState = "Stopped")
    /\ \* System can't be running if components aren't ready
        (overallState = "Running" => componentSetState = "Running" /\ processState = "Running")
    /\ \* Error type must match the state
        (overallState = "Error" => errorType # "None")
    /\ \* Restore errors only occur during restore
        (errorType = "RestoreError" => restoreInProgress)
    /\ \* Checkpoint errors only occur during checkpoint
        (errorType = "CheckpointError" => checkpointInProgress)
    /\ \* Process crash/exit states have appropriate error types
        (processState = "Crashed" => errorType = "ProcessCrash")
    /\ (processState = "Exited" => errorType = "ProcessError")
    /\ (processState = "Killed" => errorType = "ProcessKilled")
    /\ \* Can't restart during shutdown
        (shutdownInProgress => processState # "Starting")
    /\ \* State components don't shutdown until process is stopped
        (shutdownInProgress /\ componentSetState = "Shutdown" => 
            processState = "Stopped")
    /\ \* Exit request leads to shutdown
        (exitRequested /\ ~IsOperationInProgress => shutdownInProgress)
    /\ \* Process must be stopped before state components shutdown
        (componentSetState = "Shutdown") => IsStopped(processState)
    /\ \* State components must operate concurrently
        CanOperateConcurrently
    /\ \* No sequential operations allowed
        ~(dbState = "Initializing" /\ fsState = "Initializing")
    /\ ~(dbState = "Checkpointing" /\ fsState = "Checkpointing")
    /\ ~(dbState = "Restoring" /\ fsState = "Restoring")
    /\ ~(dbState = "Shutdown" /\ fsState = "Shutdown")
    /\ \* Signal handling safety
        (IsGracefulSignal(signalReceived) => shutdownInProgress)
    /\ (IsForceKillSignal(signalReceived) => errorType = "ProcessKilled")
    /\ (processState = "Signaling" => signalReceived # "None")
    /\ (signalReceived # "None" => processState = "Signaling" \/ processState = "Stopping")
    /\ \* If any component is force killed, app only crashes after all shutdowns complete
        ((dbForceKilled \/ fsForceKilled) /\ dbShutdownTimeout = 0 /\ fsShutdownTimeout = 0) => overallState = "Error"
    /\ \* Process can only start if all state components are ready and no restore in progress
        (processState = "Starting" => componentSetState = "Running" /\ ~restoreInProgress)
    /\ \* No startup timeouts: system waits indefinitely for readiness
        TRUE
    /\ \* Component set state consistency
        (componentSetState = "Running" => AllComponentsRunning)
    /\ (componentSetState = "Error" => AnyComponentError)
    /\ (componentSetState = "Initializing" => AnyComponentInitializing)

\* Main specification
Spec == Init /\ [][Next]_vars

============================================================================= 