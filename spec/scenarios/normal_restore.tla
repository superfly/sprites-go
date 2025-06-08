---------------------------- MODULE normal_restore ----------------------------

EXTENDS sprite_env

\* Normal restore scenario:
\* 1. Start with process and components running
\* 2. Restore operation begins
\* 3. Process stops during restore
\* 4. Components go through restore state
\* 5. Process restarts after restore completes

NormalRestoreScenario ==
    \* Initially everything is running
    /\ []((overallState = "Running" /\ processState = "Running" /\ componentSetState = "Running") =>
        \* Eventually restore begins
        <>(restoreInProgress = TRUE))
    
    \* When restore begins, components should start stopping
    /\ []((restoreInProgress = TRUE /\ componentSetState = "Running") =>
        <>(AnyComponentStopping))
    
    \* When restore begins, process should also stop
    /\ []((restoreInProgress = TRUE /\ processState = "Running") =>
        <>(processState = "Stopping"))
    
    \* Process should transition from Stopping to Stopped
    /\ []((restoreInProgress = TRUE /\ processState = "Stopping") =>
        <>(processState = "Stopped"))
    
    \* After process stops, components should move to actual restore
    /\ []((restoreInProgress = TRUE /\ processState = "Stopped" /\ AnyComponentStopping) =>
        <>(componentSetState = "Restoring"))
    
    \* After restore completes, components should start processes back up
    /\ []((~restoreInProgress /\ componentSetState = "Restoring") =>
        <>(AnyComponentStarting))
    
    \* When components are starting, process should start too
    /\ []((~restoreInProgress /\ AnyComponentStarting /\ processState = "Stopped") =>
        <>(processState = "Starting"))
    
    \* Process should eventually return to running
    /\ []((~restoreInProgress /\ processState = "Starting") =>
        <>(processState = "Running"))
    
    \* Components should return to running after process is running
    /\ []((~restoreInProgress /\ processState = "Running" /\ AnyComponentStarting) =>
        <>(componentSetState = "Running"))
    
    \* Overall system should return to running state
    /\ []((~restoreInProgress /\ processState = "Running" /\ componentSetState = "Running") =>
        <>(overallState = "Running"))

\* The complete specification with scenario
SpecWithScenario == Spec /\ NormalRestoreScenario

============================================================================= 