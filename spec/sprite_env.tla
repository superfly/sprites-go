---------------------------- MODULE sprite_env ----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N  \* Number of components (1..N)

VARIABLES 
    components  \* Function: 1..N -> ComponentStates

vars == <<components>>

\* Base State Categories (shared across all entities)
BaseTransitionStates == {
    "Initializing",    \* Starting up
    "Starting",        \* Transitioning to active
    "Stopping",        \* Gracefully stopping
    "ShuttingDown"     \* Permanent shutdown transition
}

BaseFinalStates == {
    "Stopped",         \* Temporarily stopped (can restart)
    "Shutdown"         \* Permanently shut down
}

BaseActiveStates == {
    "Running"          \* Normal operation
}

BaseErrorStates == {
    "Error"            \* Generic error state
}

\* Terminal states (process no longer operational)
BaseTerminalStates == {
    "Stopped",         \* Stopped gracefully
    "Shutdown",        \* Shutdown permanently  
    "Exited",          \* Exited normally
    "Crashed",         \* Crashed/failed
    "Killed"           \* Forcefully terminated
}

\* Process-specific states
ProcessSpecificStates == {
    "Signaling"        \* Process receiving signal
}

\* Component-specific states  
ComponentSpecificStates == {
    "Restoring",       \* Performing restore operation
    "Checkpointing"    \* Performing checkpoint operation
}



\* System-specific states
SystemSpecificStates == {
    "Ready",           \* Components ready but process not running
    "Restoring",       \* System-level restore operation
    "Checkpointing",   \* System-level checkpoint operation
    "ErrorRecovery"    \* System responding to component failure
}

\* Unified State Definitions (all include terminal states)
ProcessStates == BaseTransitionStates \cup BaseActiveStates \cup BaseErrorStates \cup BaseTerminalStates \cup ProcessSpecificStates

ComponentStates == BaseTransitionStates \cup BaseActiveStates \cup BaseErrorStates \cup BaseTerminalStates \cup ComponentSpecificStates

ComponentSetStates == BaseTransitionStates \cup BaseActiveStates \cup BaseErrorStates \cup BaseTerminalStates \cup {"ErrorStopping"}

SystemStates == BaseTransitionStates \cup BaseActiveStates \cup BaseErrorStates \cup BaseTerminalStates \cup SystemSpecificStates

\* Helper predicates for state types
IsTransitionState(state) == state \in BaseTransitionStates
IsActiveState(state) == state \in BaseActiveStates
IsErrorState(state) == state \in BaseErrorStates
IsTerminalState(state) == state \in BaseTerminalStates

\* Helper predicates for specific states
IsRunning(state) == state = "Running"
IsError(state) == state = "Error"
IsInitializing(state) == state = "Initializing"
IsStarting(state) == state = "Starting"
IsStopping(state) == state = "Stopping"
IsShuttingDown(state) == state = "ShuttingDown"
IsStopped(state) == state = "Stopped"
IsShutdown(state) == state = "Shutdown"
IsCheckpointing(state) == state = "Checkpointing"
IsRestoring(state) == state = "Restoring"

\* Consistent terminal state predicates (work for all state machines)
IsTerminated(state) == state \in BaseTerminalStates
IsOperational(state) == state \in BaseActiveStates

\* Component aggregate predicates
AllComponentsRunning == \A i \in 1..N : IsRunning(components[i])
AllComponentsOperational == \A i \in 1..N : components[i] \in {"Running", "Checkpointing", "Restoring"}
AllComponentsStopped == \A i \in 1..N : IsStopped(components[i])
AllComponentsShutdown == \A i \in 1..N : IsShutdown(components[i])
AnyComponentError == \E i \in 1..N : IsError(components[i])
AnyComponentInitializing == \E i \in 1..N : IsInitializing(components[i])
AnyComponentStarting == \E i \in 1..N : IsStarting(components[i])
AnyComponentStopping == \E i \in 1..N : IsStopping(components[i])
AnyComponentShuttingDown == \E i \in 1..N : IsShuttingDown(components[i])
AnyComponentCheckpointing == \E i \in 1..N : IsCheckpointing(components[i])
AnyComponentRestoring == \E i \in 1..N : IsRestoring(components[i])

\* ComponentSet State Machine (shows component collective state)
ComponentSetState ==
    IF AnyComponentError /\ AnyComponentStopping THEN
        "Stopping"  \* Component failed AND actively stopping healthy components
    ELSE IF AnyComponentError /\ (\E i \in 1..N : components[i] = "Running") THEN
        "ErrorStopping"  \* Component failed, healthy components need to be stopped
    ELSE IF AnyComponentError THEN
        "Error"  \* Component failed and all components stopped
    ELSE IF AnyComponentInitializing THEN
        "Initializing"
    ELSE IF AnyComponentStarting THEN
        "Starting"
    ELSE IF AllComponentsOperational THEN
        "Running"  \* All components operational (running/checkpointing/restoring)
    ELSE IF AnyComponentStopping THEN
        "Stopping"
    ELSE IF AnyComponentShuttingDown THEN
        "ShuttingDown"  
    ELSE IF AllComponentsStopped THEN
        "Stopped"
    ELSE IF AllComponentsShutdown THEN
        "Shutdown"
    ELSE
        "Error"  \* Undefined state combination

\* System State Machine (reacts to ComponentSet state changes)
SystemState ==
    IF ComponentSetState = "ErrorStopping" THEN
        "ErrorRecovery"  \* ComponentSet ready to stop healthy components
    ELSE IF ComponentSetState = "Error" /\ (\E i \in 1..N : components[i] = "Running") THEN
        "ErrorRecovery"  \* Component failed, still have running components to stop
    ELSE IF ComponentSetState = "Error" /\ ~(\E i \in 1..N : components[i] = "Running") THEN
        "Error"  \* Error recovery complete, system reaches terminal error state
    ELSE IF ComponentSetState = "Initializing" THEN
        "Initializing"  \* System initializing when components initializing
    ELSE IF ComponentSetState = "Starting" THEN
        "Starting"  \* System starting when components starting
    ELSE IF ComponentSetState = "Running" THEN
        "Ready"  \* Components ready, system ready to run process
    ELSE IF ComponentSetState = "Stopping" THEN
        "Stopping"  \* System stopping when components stopping
    ELSE IF ComponentSetState = "ShuttingDown" THEN
        "ShuttingDown"  \* System shutting down when components shutting down
    ELSE IF ComponentSetState = "Stopped" THEN
        "Stopped"  \* System stopped when components stopped
    ELSE IF ComponentSetState = "Shutdown" THEN
        "Shutdown"  \* System shutdown when components shutdown
    ELSE
        "Error"  \* Undefined state combination

\* Process State Machine (responds to SystemState)
ProcessState ==
    IF SystemState = "ErrorRecovery" /\ (\E i \in 1..N : components[i] = "Running") THEN
        "Stopping"  \* Process stops gracefully during error recovery
    ELSE IF SystemState = "ErrorRecovery" THEN
        "Stopped"  \* Process stopped during error recovery
    ELSE IF SystemState \in {"Initializing", "Starting"} THEN
        "Stopped"  \* Process waits for system to be ready
    ELSE IF SystemState = "Ready" THEN
        "Running"  \* Process runs when system is ready
    ELSE IF SystemState = "Stopping" THEN
        "Stopped"  \* Process MUST be stopped before components can stop
    ELSE IF SystemState = "ShuttingDown" THEN
        "Shutdown"  \* Process MUST be shutdown before components can shutdown
    ELSE IF SystemState = "Stopped" THEN
        "Stopped"  \* Process stopped when system stopped
    ELSE IF SystemState = "Shutdown" THEN
        "Shutdown"  \* Process shutdown when system shutdown
    ELSE
        "Stopped"  \* Default to stopped for safety

\* Overall System State (combination of System + Process for full picture)
OverallSystemState ==
    IF SystemState = "Ready" /\ ProcessState = "Running" THEN
        "Running"  \* Full system operational
    ELSE IF SystemState = "Ready" /\ ProcessState = "Stopped" THEN
        "Ready"  \* Components ready, process not started yet
    ELSE
        SystemState  \* Otherwise just use system state

\* Component state transitions
ComponentTransition(state) ==
    CASE state = "Initializing" -> "Starting"
      [] state = "Initializing" -> "Error"       \* Initialization can fail
      [] state = "Starting" -> "Running"
      [] state = "Starting" -> "Error"           \* Startup can fail
      [] state = "Running" -> "Checkpointing"    \* Trigger checkpoint operation
      [] state = "Running" -> "Restoring"        \* Trigger restore operation
      [] state = "Running" /\ ComponentSetState = "Stopping" -> "Stopping"
      [] state = "Running" /\ ComponentSetState = "ShuttingDown" -> "ShuttingDown"
      [] state = "Running" -> "Error"            \* Running components can fail
      [] state = "Checkpointing" -> "Running"    \* Return to running after checkpoint
      [] state = "Checkpointing" -> "Error"      \* Checkpoint can fail
      [] state = "Restoring" -> "Running"        \* Return to running after restore
      [] state = "Restoring" -> "Error"          \* Restore can fail
      [] state = "Stopping" -> "Stopped"
      [] state = "ShuttingDown" -> "Shutdown" 
      [] state = "Stopped" /\ ComponentSetState = "Starting" -> "Starting"
      [] OTHER -> state

\* Initial state
Init == 
    /\ components = [i \in 1..N |-> "Initializing"]

\* Next state relation
Next ==
    \* 1. Individual components transition (normal operation)
    \E i \in 1..N :
        /\ components' = [components EXCEPT ![i] = ComponentTransition(components[i])]
        /\ components'[i] # components[i]

    \* 2. Error recovery: stop remaining healthy components when ready
    \/ \* Stop remaining healthy components after process terminates
        /\ ComponentSetState = "ErrorStopping"  \* ComponentSet shows error + healthy components
        /\ IsTerminated(ProcessState)           \* Process must be terminated first
        /\ \E r \in 1..N : components[r] = "Running"  \* Still have healthy components
        /\ components' = [s \in 1..N |-> IF components[s] = "Running" THEN "Stopping" ELSE components[s]]

    \* 3. Normal system operations
    \/ \* Stop system: ONLY when process is terminated (stopped/crashed/killed/etc)
        /\ IsTerminated(ProcessState)  \* Process MUST be terminated first
        /\ ComponentSetState = "Running"
        /\ components' = [m \in 1..N |-> IF IsRunning(components[m]) THEN "Stopping" ELSE components[m]]

    \/ \* Shutdown system: ONLY when process is terminated
        /\ IsTerminated(ProcessState)  \* Process MUST be terminated first
        /\ SystemState \in {"Ready", "Stopping"}
        /\ components' = [p \in 1..N |-> IF components[p] \notin {"Shutdown", "ShuttingDown"} THEN "ShuttingDown" ELSE components[p]]

\* Type invariant
TypeOK ==
    /\ components \in [1..N -> ComponentStates]
    /\ SystemState \in SystemStates
    /\ ComponentSetState \in ComponentSetStates  
    /\ ProcessState \in ProcessStates

\* System hierarchy invariant (updated for clean hierarchy)
HierarchyInvariant ==
    /\ (SystemState = "Ready" => ComponentSetState = "Running")
    /\ (ProcessState = "Running" => SystemState = "Ready")
    /\ (ComponentSetState = "Running" => AllComponentsOperational)
    /\ (ComponentSetState = "Error" => AnyComponentError)
    /\ (OverallSystemState = "Running" => (SystemState = "Ready" /\ ProcessState = "Running"))

\* Process state dependency constraints (updated for consistent terminal states)
ProcessStateDependencyInvariant ==
    \* Process can only run if components are ready and system is ready
    /\ (IsOperational(ProcessState) => (ComponentSetState = "Running" /\ SystemState = "Ready"))
    \* Process must be terminated before components can stop (normal shutdown)
    /\ (ComponentSetState = "Stopping" => IsTerminated(ProcessState))
    \* Process must be terminated before components can shutdown  
    /\ (ComponentSetState = "ShuttingDown" => IsTerminated(ProcessState))
    \* During error recovery, system coordinates the sequence
    /\ (SystemState = "ErrorRecovery" /\ ComponentSetState = "Error" => (IsTransitionState(ProcessState) \/ IsTerminated(ProcessState)))
    \* Components can't be stopping if process is still operational (except during error recovery)
    /\ (AnyComponentStopping /\ ~AnyComponentError => IsTerminated(ProcessState))
    \* Components can't be shutting down if process is still operational
    /\ (AnyComponentShuttingDown => IsTerminated(ProcessState))

\* No return to Ready after error - once failed, system cannot recover
NoRecoveryAfterErrorInvariant ==
    \* If system ever reached Error state, it cannot return to Ready
    /\ (AnyComponentError => SystemState # "Ready")
    \* If any component is in Error state, system stays in Error or ErrorRecovery
    /\ (AnyComponentError => SystemState \in {"Error", "ErrorRecovery"})

\* The specification
Spec == Init /\ [][Next]_vars

============================================================================= 