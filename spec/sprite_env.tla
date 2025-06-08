---------------------------- MODULE sprite_env ----------------------------

EXTENDS Integers, Sequences, FiniteSets

VARIABLES 
    systemState,           \* Top-level system state
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

vars == <<systemState, componentSetState, dbState, fsState, processState, processExitCode, checkpointInProgress, restoreInProgress, errorType, restartAttempt, restartDelay, shutdownInProgress, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

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

\* Component state definitions
ComponentTransitionStates == {
    "Initializing", \* Component is being started
    "Starting",     \* Component is being started
    "Stopping",     \* Component is being gracefully stopped
    "ShuttingDown"  \* Component is in the process of shutting down
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

\* System state definitions
SystemTransitionStates == {
    "Initializing", \* System is starting up
    "ShuttingDown"  \* System is in the process of shutting down
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
    /\ systemState = "Initializing"
    /\ componentSetState = "Initializing"
    /\ dbState = "Initializing"
    /\ fsState = "Initializing"
    /\ processState = "Initializing"
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

\* State type predicates
IsTransitionState(state) == state \in (ProcessTransitionStates \cup ComponentTransitionStates \cup SystemTransitionStates)
IsFinalState(state) == state \in (ProcessFinalStates \cup ComponentFinalStates \cup SystemFinalStates)
IsActiveState(state) == state \in (ProcessActiveStates \cup ComponentActiveStates \cup SystemActiveStates)
IsErrorState(state) == state \in (ProcessErrorStates \cup ComponentErrorStates \cup SystemErrorStates)

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

\* State checks for components
AllComponentsRunning == IsRunning(dbState) /\ IsRunning(fsState)
AnyComponentError == IsError(dbState) \/ IsError(fsState)
AnyComponentInitializing == IsInitializing(dbState) \/ IsInitializing(fsState)
AnyComponentCheckpointing == IsCheckpointing(dbState) \/ IsCheckpointing(fsState)
AnyComponentRestoring == IsRestoring(dbState) \/ IsRestoring(fsState)

\* Valid state transition rules
ValidStateTransition(from, to) ==
    \/ (IsActiveState(from) /\ IsTransitionState(to))  \* Active -> Transition
    \/ (IsTransitionState(from) /\ IsFinalState(to))   \* Transition -> Final
    \/ (IsTransitionState(from) /\ IsErrorState(to))   \* Transition -> Error
    \/ (IsActiveState(from) /\ IsErrorState(to))       \* Active -> Error

\* Component set state determination (just from storage components)
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
    ELSE IF shutdownInProgress /\ dbState = "Shutdown" /\ fsState = "Shutdown" THEN
        "Shutdown"
    ELSE IF shutdownInProgress THEN
        "ShuttingDown"
    ELSE
        "Initializing"

\* System state determination (from both components and process)
DetermineSystemState ==
    IF errorType # "None" THEN
        "Error"
    ELSE IF componentSetState = "Initializing" THEN
        "Initializing"
    ELSE IF componentSetState = "Checkpointing" THEN
        "Checkpointing"
    ELSE IF componentSetState = "Restoring" THEN
        "Restoring"
    ELSE IF componentSetState = "Running" /\ processState = "Running" THEN
        "Running"
    ELSE IF componentSetState = "Shutdown" /\ processState \in ProcessFinalStates THEN
        "Shutdown"
    ELSE IF shutdownInProgress THEN
        "ShuttingDown"
    ELSE
        "Initializing"

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

\* Next state relation
Next ==
    \/ \* DB component transitions independently
        /\ dbState' = StateTransition(dbState, "DB")
        /\ componentSetState' = DetermineComponentSetState  \* Recompute based on new DB state
        /\ systemState' = DetermineSystemState
        /\ errorType' = DetermineErrorType
        /\ UNCHANGED <<fsState, processState, processExitCode, checkpointInProgress, restoreInProgress, restartAttempt, restartDelay, shutdownInProgress, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

    \/ \* FS component transitions independently  
        /\ fsState' = StateTransition(fsState, "FS")
        /\ componentSetState' = DetermineComponentSetState  \* Recompute based on new FS state
        /\ systemState' = DetermineSystemState
        /\ errorType' = DetermineErrorType
        /\ UNCHANGED <<dbState, processState, processExitCode, checkpointInProgress, restoreInProgress, restartAttempt, restartDelay, shutdownInProgress, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

    \/ \* Process transitions (when not exiting)
        /\ processState' = ProcessTransition(processState, processExitCode)
        /\ processState' # processState  \* Only if actually transitioning
        /\ componentSetState' = DetermineComponentSetState
        /\ systemState' = DetermineSystemState
        /\ errorType' = DetermineErrorType
        /\ UNCHANGED <<dbState, fsState, processExitCode, checkpointInProgress, restoreInProgress, restartAttempt, restartDelay, shutdownInProgress, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

    \/ \* Process exits autonomously (only updates process state)
        /\ processState = "Running"
        /\ processExitCode' \in {0, 1, 2, 130, 137, 143}  \* All possible exit codes
        /\ processState' = IF processExitCode' = 0 THEN "Exited"
                           ELSE IF processExitCode' = 137 THEN "Killed" 
                           ELSE IF processExitCode' > 128 THEN "Crashed"
                           ELSE "Exited"
        /\ UNCHANGED <<systemState, componentSetState, dbState, fsState, checkpointInProgress, restoreInProgress, errorType, restartAttempt, restartDelay, shutdownInProgress, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

    \/ \* System state manager reacts to process exit
        /\ processState \in {"Exited", "Crashed", "Killed"}
        /\ systemState \in {"Running", "Initializing"}  \* Haven't reacted to process exit yet
        /\ systemState' = IF processExitCode = 0 THEN "Running"  \* Successful exit during normal operation
                          ELSE "Error"  \* Error exit
        /\ errorType' = IF processExitCode = 0 THEN "None"
                        ELSE IF processState = "Killed" THEN "ProcessKilled"
                        ELSE IF processState = "Crashed" THEN "ProcessCrash" 
                        ELSE "ProcessError"
        /\ UNCHANGED <<componentSetState, dbState, fsState, processState, processExitCode, checkpointInProgress, restoreInProgress, restartAttempt, restartDelay, shutdownInProgress, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

    \/ \* Component set reacts to system state change
        /\ systemState = "Error"
        /\ componentSetState = "Running"  \* Haven't reacted to error yet
        /\ componentSetState' = "Error"
        /\ UNCHANGED <<systemState, dbState, fsState, processState, processExitCode, checkpointInProgress, restoreInProgress, errorType, restartAttempt, restartDelay, shutdownInProgress, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

    \/ \* Process restart after crash/exit
        /\ processState \in {"Crashed", "Exited", "Killed"}
        /\ restartAttempt' = restartAttempt + 1
        /\ restartDelay' = NextRestartDelay
        /\ processState' = "Starting"
        /\ UNCHANGED <<systemState, componentSetState, dbState, fsState, processExitCode, checkpointInProgress, restoreInProgress, errorType, shutdownInProgress, exitRequested, signalReceived, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

    \/ \* Signal handling
        /\ signalReceived' \in Signals
        /\ IF IsGracefulSignal(signalReceived') THEN
            /\ shutdownInProgress' = TRUE
            /\ processState' = "Signaling"
           ELSE
            /\ UNCHANGED <<shutdownInProgress, processState>>
        /\ UNCHANGED <<systemState, componentSetState, dbState, fsState, processExitCode, checkpointInProgress, restoreInProgress, errorType, restartAttempt, restartDelay, exitRequested, dbShutdownTimeout, fsShutdownTimeout, dbForceKilled, fsForceKilled>>

\* Invariants
TypeOK ==
    /\ systemState \in SystemStates
    /\ componentSetState \in SystemStates
    /\ dbState \in ComponentStates
    /\ fsState \in ComponentStates
    /\ processState \in ProcessStates
    /\ processExitCode \in 0..255
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

systemStateOK == systemState \in SystemStates
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