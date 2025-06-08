---------------------------- MODULE sprite_env ----------------------------

EXTENDS Integers, Sequences, FiniteSets

VARIABLES 
    overallState,          \* Overall application state
    componentSetState,      \* Derived state of all storage components
    dbState,               \* Individual DB component state
    fsState,               \* Individual FS component state
    processState,          \* Supervised process state
    processExitCode,
    checkpointInProgress,
    restoreInProgress,
    currentOperation,      \* Current high-level operation: "None", "Restore", "Checkpoint", "Shutdown"
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

vars == <<overallState, componentSetState, dbState, fsState, processState, processExitCode, checkpointInProgress, restoreInProgress, currentOperation, errorType, restartAttempt, restartDelay, shutdownInProgress, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

\* Process state definitions
ProcessTransitionStates == {
    "Initializing", \* Process is being started
    "Starting",     \* Process is being started
    "Stopping",     \* Process is being gracefully stopped
    "Signaling"     \* Process is being sent a signal
}

ProcessFinalStates == {
    "Stopped",      \* Process is not running
    "Exited",       \* Process exited normally
    "Crashed",      \* Process exited unexpectedly
    "Killed"        \* Process was forcefully terminated
}

ProcessActiveStates == {
    "Running"       \* Process is running normally
}

ProcessErrorStates == {
    "Error"         \* Process failed to start/stop
}

ProcessStates == ProcessTransitionStates \cup ProcessFinalStates \cup ProcessActiveStates \cup ProcessErrorStates

\* Component state definitions (what the component is doing)
ComponentTransitionStates == {
    "Initializing",      \* Component is being started
    "Starting",          \* Component is starting managed processes  
    "Stopping",          \* Component is stopping managed processes
    "Restoring",         \* Component is performing restore operation
    "Checkpointing",     \* Component is performing checkpoint operation
    "ShuttingDown"       \* Component is shutting down permanently
}

ComponentFinalStates == {
    "Stopped",      \* Component is fully stopped
    "Shutdown"      \* Component has completed shutdown
}

ComponentActiveStates == {
    "Running"       \* Component is running normally
}

ComponentErrorStates == {
    "Error"         \* Component encountered an error
}

ComponentStates == ComponentTransitionStates \cup ComponentFinalStates \cup ComponentActiveStates \cup ComponentErrorStates

\* Operation types (why the component is doing something)
OperationTypes == {
    "None",              \* No operation in progress
    "Restore",           \* Restore operation
    "Checkpoint",        \* Checkpoint operation  
    "Shutdown"           \* Shutdown operation
}

\* System state definitions
SystemTransitionStates == {
    "Initializing",        \* System is starting up
    "ShuttingDown",        \* System is in the process of shutting down
    "Restoring",           \* System is performing restore operation
    "Checkpointing"        \* System is performing checkpoint operation
}

SystemFinalStates == {
    "Shutdown"      \* System is fully shut down
}

SystemActiveStates == {
    "Running"       \* System is running normally
}

SystemErrorStates == {
    "Error"         \* System encountered an error
}

SystemStates == SystemTransitionStates \cup SystemFinalStates \cup SystemActiveStates \cup SystemErrorStates

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
    /\ processState = "Initializing"
    /\ processExitCode = 0
    /\ checkpointInProgress = FALSE
    /\ restoreInProgress = FALSE
    /\ currentOperation = "None"
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

\* State type predicates
IsTransitionState(state) == state \in (ProcessTransitionStates \cup ComponentTransitionStates \cup SystemTransitionStates)
IsFinalState(state) == state \in (ProcessFinalStates \cup ComponentFinalStates \cup SystemFinalStates)
IsActiveState(state) == state \in (ProcessActiveStates \cup ComponentActiveStates \cup SystemActiveStates)
IsErrorState(state) == state \in (ProcessErrorStates \cup ComponentErrorStates \cup SystemErrorStates)

\* Helper predicates
IsRunning(state) == state = "Running"
IsError(state) == state = "Error"
IsInitializing(state) == state = "Initializing"
IsStopping(state) == state = "Stopping"
IsStarting(state) == state = "Starting"
IsRestoring(state) == state = "Restoring"
IsCheckpointing(state) == state = "Checkpointing"
IsStopped(state) == state = "Stopped"
IsOperationInProgress == checkpointInProgress \/ restoreInProgress \/ IsInitializing(componentSetState)
IsGracefulSignal(signal) == signal \in {"SIGTERM", "SIGINT"}
IsForceKillSignal(signal) == signal = "SIGKILL"

\* State checks for components
AllComponentsRunning == IsRunning(dbState) /\ IsRunning(fsState)
AnyComponentError == IsError(dbState) \/ IsError(fsState)
AnyComponentInitializing == IsInitializing(dbState) \/ IsInitializing(fsState)
AnyComponentStopping == IsStopping(dbState) \/ IsStopping(fsState)
AnyComponentStarting == IsStarting(dbState) \/ IsStarting(fsState)
AnyComponentRestoring == IsRestoring(dbState) \/ IsRestoring(fsState)
AnyComponentCheckpointing == IsCheckpointing(dbState) \/ IsCheckpointing(fsState)

\* Valid state transition rules
ValidStateTransition(from, to) ==
    \/ (IsActiveState(from) /\ IsTransitionState(to))  \* Active -> Transition
    \/ (IsTransitionState(from) /\ IsFinalState(to))   \* Transition -> Final
    \/ (IsTransitionState(from) /\ IsErrorState(to))   \* Transition -> Error
    \/ (IsActiveState(from) /\ IsErrorState(to))       \* Active -> Error

\* Component set state determination (from component states)
DetermineComponentSetState ==
    IF AnyComponentError THEN
        "Error"
    ELSE IF AnyComponentInitializing THEN
        "Initializing"
    ELSE IF AnyComponentRestoring THEN
        "Restoring"
    ELSE IF AnyComponentCheckpointing THEN
        "Checkpointing"
    ELSE IF AllComponentsRunning THEN
        "Running"
    ELSE IF shutdownInProgress /\ dbState = "Shutdown" /\ fsState = "Shutdown" THEN
        "Shutdown"
    ELSE IF shutdownInProgress THEN
        "ShuttingDown"
    ELSE
        "Initializing"

\* Overall state determination (from components and process)
DetermineOverallState ==
    IF errorType # "None" THEN
        "Error"
    ELSE IF componentSetState = "Initializing" THEN
        "Initializing"
    ELSE IF componentSetState = "Restoring" THEN
        "Restoring"
    ELSE IF componentSetState = "Checkpointing" THEN
        "Checkpointing"
    ELSE IF componentSetState = "Running" /\ processState = "Running" THEN
        "Running"
    ELSE IF componentSetState = "Shutdown" /\ processState \in ProcessFinalStates THEN
        "Shutdown"
    ELSE IF shutdownInProgress THEN
        "ShuttingDown"
    ELSE
        "Initializing"

\* State transitions for DB and FS (different patterns for different operations)
StateTransition(state, component) ==
    IF state = "Initializing" THEN
        "Running"
    \* Checkpoint flow: Running -> Checkpointing -> Running (no process restart)
    ELSE IF state = "Running" /\ currentOperation = "Checkpoint" THEN
        "Checkpointing"
    ELSE IF state = "Checkpointing" /\ currentOperation = "None" THEN
        "Running"
    \* Restore flow: Running -> Stopping -> Restoring -> Starting -> Running
    ELSE IF state = "Running" /\ currentOperation = "Restore" THEN
        "Stopping"
    ELSE IF state = "Stopping" /\ processState = "Stopped" /\ currentOperation = "Restore" THEN
        "Restoring"
    ELSE IF state = "Restoring" /\ currentOperation = "None" THEN
        "Starting"
    ELSE IF state = "Starting" /\ processState = "Running" THEN
        "Running"
    \* Shutdown flow (permanent shutdown, not operation)
    ELSE IF state = "Running" /\ shutdownInProgress THEN
        IF processState = "Running" THEN
            "ShuttingDown"  \* Start shutdown sequence
        ELSE IF processState \in ProcessFinalStates THEN
            "Shutdown"      \* Complete shutdown
        ELSE
            state
    ELSE IF state = "ShuttingDown" /\ processState \in ProcessFinalStates THEN
        "Shutdown"         \* Move to final state
    ELSE IF state = "Shutdown" THEN
        "Stopped"          \* Final state
    ELSE
        state

\* Process state transitions (only stops for restore, not checkpoint)
ProcessTransition(state, exitCode) ==
    IF state = "Stopped" /\ IsRunning(componentSetState) /\ ~shutdownInProgress /\ currentOperation = "None" THEN
        "Starting"
    ELSE IF state = "Starting" THEN
        "Running"
    ELSE IF state = "Running" /\ currentOperation = "Restore" THEN
        "Stopping"
    ELSE IF state = "Stopping" THEN
        "Stopped"
    ELSE IF state = "Running" /\ exitCode # 0 THEN
        IF exitCode = 143 THEN  \* 128 + 15 (SIGTERM)
            "Exited"
        ELSE IF exitCode = 130 THEN  \* Ctrl+C
            "Crashed"
        ELSE IF exitCode > 128 THEN \* Other signals
            "Crashed"
        ELSE
            "Exited"
    ELSE IF state = "Signaling" /\ exitCode = 137 THEN  \* 128 + 9 (SIGKILL)
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

\* Determine current operation from boolean flags
DetermineCurrentOperation ==
    IF restoreInProgress THEN
        "Restore"
    ELSE IF checkpointInProgress THEN
        "Checkpoint"
    ELSE IF shutdownInProgress THEN
        "Shutdown"
    ELSE
        "None"

\* Next state relation
Next ==
    \/ \* DB component transitions independently
        /\ dbState' = StateTransition(dbState, "DB")
        /\ componentSetState' = DetermineComponentSetState  \* Recompute based on new DB state
        /\ currentOperation' = DetermineCurrentOperation
        /\ overallState' = DetermineOverallState
        /\ errorType' = DetermineErrorType
        /\ UNCHANGED <<fsState, processState, processExitCode, checkpointInProgress, restoreInProgress, restartAttempt, restartDelay, shutdownInProgress, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

    \/ \* FS component transitions independently  
        /\ fsState' = StateTransition(fsState, "FS")
        /\ componentSetState' = DetermineComponentSetState  \* Recompute based on new FS state
        /\ currentOperation' = DetermineCurrentOperation
        /\ overallState' = DetermineOverallState
        /\ errorType' = DetermineErrorType
        /\ UNCHANGED <<dbState, processState, processExitCode, checkpointInProgress, restoreInProgress, restartAttempt, restartDelay, shutdownInProgress, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

    \/ \* Process transitions (when not exiting)
        /\ processState' = ProcessTransition(processState, processExitCode)
        /\ processState' # processState  \* Only if actually transitioning
        /\ componentSetState' = DetermineComponentSetState
        /\ currentOperation' = DetermineCurrentOperation
        /\ overallState' = DetermineOverallState
        /\ errorType' = DetermineErrorType
        /\ UNCHANGED <<dbState, fsState, processExitCode, checkpointInProgress, restoreInProgress, restartAttempt, restartDelay, shutdownInProgress, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

    \/ \* Process exits autonomously (only updates process state)
        /\ processState = "Running"
        /\ processExitCode' \in {0, 1, 2, 130, 137, 143}  \* All possible exit codes
        /\ processState' = IF processExitCode' = 0 THEN "Exited"
                           ELSE IF processExitCode' = 137 THEN "Killed" 
                           ELSE IF processExitCode' > 128 THEN "Crashed"
                           ELSE "Exited"
        /\ UNCHANGED <<overallState, componentSetState, dbState, fsState, checkpointInProgress, restoreInProgress, currentOperation, errorType, restartAttempt, restartDelay, shutdownInProgress, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

    \/ \* Overall state manager reacts to process exit
        /\ processState \in {"Exited", "Crashed", "Killed"}
        /\ overallState \in {"Running", "Initializing"}  \* Haven't reacted to process exit yet
        /\ overallState' = IF processExitCode = 0 THEN "Running"  \* Successful exit during normal operation
                          ELSE "Error"  \* Error exit
        /\ errorType' = IF processExitCode = 0 THEN "None"
                        ELSE IF processState = "Killed" THEN "ProcessKilled"
                        ELSE IF processState = "Crashed" THEN "ProcessCrash" 
                        ELSE "ProcessError"
        /\ UNCHANGED <<componentSetState, dbState, fsState, processState, processExitCode, checkpointInProgress, restoreInProgress, currentOperation, restartAttempt, restartDelay, shutdownInProgress, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

    \/ \* Component set reacts to overall state change
        /\ overallState = "Error"
        /\ componentSetState = "Running"  \* Haven't reacted to error yet
        /\ componentSetState' = "Error"
        /\ UNCHANGED <<overallState, dbState, fsState, processState, processExitCode, checkpointInProgress, restoreInProgress, currentOperation, errorType, restartAttempt, restartDelay, shutdownInProgress, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

    \/ \* Process restart after crash/exit
        /\ processState \in {"Crashed", "Exited", "Killed"}
        /\ restartAttempt' = restartAttempt + 1
        /\ restartDelay' = NextRestartDelay
        /\ processState' = "Starting"
        /\ UNCHANGED <<overallState, componentSetState, dbState, fsState, processExitCode, checkpointInProgress, restoreInProgress, currentOperation, errorType, shutdownInProgress, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

    \/ \* Signal handling
        /\ signalReceived' \in Signals
        /\ IF IsGracefulSignal(signalReceived') THEN
            /\ shutdownInProgress' = TRUE
            /\ processState' = "Signaling"
           ELSE
            /\ UNCHANGED <<shutdownInProgress, processState>>
        /\ UNCHANGED <<overallState, componentSetState, dbState, fsState, processExitCode, checkpointInProgress, restoreInProgress, currentOperation, errorType, restartAttempt, restartDelay, exitRequested, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

\* Invariants
TypeOK ==
    /\ overallState \in SystemStates
    /\ componentSetState \in SystemStates
    /\ dbState \in ComponentStates
    /\ fsState \in ComponentStates
    /\ processState \in ProcessStates
    /\ processExitCode \in 0..255
    /\ checkpointInProgress \in BOOLEAN
    /\ restoreInProgress \in BOOLEAN
    /\ currentOperation \in OperationTypes
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

StateTransitionInvariant ==
    /\ ValidStateTransition(dbState, StateTransition(dbState, "Component"))
    /\ ValidStateTransition(fsState, StateTransition(fsState, "Component"))

ShutdownSequenceInvariant ==
    /\ (dbState = "ShuttingDown" => processState = "Running")
    /\ (dbState = "Shutdown" => processState \in ProcessFinalStates)
    /\ (dbState = "Stopped" => processState = "Stopped")
    /\ (IsTransitionState(dbState) => ~IsFinalState(processState))
    /\ (IsFinalState(dbState) => IsFinalState(processState))
    /\ (fsState = "ShuttingDown" => processState = "Running")
    /\ (fsState = "Shutdown" => processState \in ProcessFinalStates)
    /\ (fsState = "Stopped" => processState = "Stopped")
    /\ (IsTransitionState(fsState) => ~IsFinalState(processState))
    /\ (IsFinalState(fsState) => IsFinalState(processState))

\* Temporal properties
NoStuckTransitions ==
    /\ [](IsTransitionState(dbState) => <>IsFinalState(dbState) \/ IsErrorState(dbState))
    /\ [](IsTransitionState(fsState) => <>IsFinalState(fsState) \/ IsErrorState(fsState))

ProperShutdownSequence ==
    /\ []((dbState = "ShuttingDown" /\ processState = "Running") =>
            <>(dbState = "Shutdown" /\ processState \in ProcessFinalStates))
    /\ []((fsState = "ShuttingDown" /\ processState = "Running") =>
            <>(fsState = "Shutdown" /\ processState \in ProcessFinalStates))

\* Constraint for normal operation only
NormalOperation == 
    /\ errorType = "None"
    /\ signalReceived = "None"
    /\ ~shutdownInProgress
    /\ processExitCode = 0

\* The specification
Spec == Init /\ [][Next]_vars

\* The properties to verify
Properties ==
    /\ StateTransitionInvariant
    /\ ShutdownSequenceInvariant
    /\ NoStuckTransitions
    /\ ProperShutdownSequence

overallStateOK == overallState \in SystemStates
componentSetStateOK == componentSetState \in SystemStates
dbStateOK == dbState \in ComponentStates
fsStateOK == fsState \in ComponentStates
processStateOK == processState \in ProcessStates
processExitCodeOK == processExitCode \in 0..255
checkpointInProgressOK == checkpointInProgress \in BOOLEAN
restoreInProgressOK == restoreInProgress \in BOOLEAN
errorTypeOK == errorType \in ErrorTypes
restartAttemptOK == restartAttempt \in Nat
restartDelayOK == restartDelay \in Nat
shutdownInProgressOK == shutdownInProgress \in BOOLEAN
exitRequestedOK == exitRequested \in BOOLEAN
signalReceivedOK == signalReceived \in Signals
dbShutdownTimeoutOK == dbShutdownTimeout \in Nat
fsShutdownTimeoutOK == fsShutdownTimeout \in Nat
dbForceKilledOK == dbForceKilled \in BOOLEAN
fsForceKilledOK == fsForceKilled \in BOOLEAN

============================================================================= 