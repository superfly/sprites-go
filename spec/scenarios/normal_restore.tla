---------------------------- MODULE normal_restore ----------------------------

EXTENDS _sprite_env

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
    
    \* When restore begins, process should stop
    /\ []((restoreInProgress = TRUE /\ processState = "Running") =>
        <>(processState = "Stopping"))
    
    \* Process transitions from Stopping to Stopped during restore
    /\ []((restoreInProgress = TRUE /\ processState = "Stopping") =>
        <>(processState = "Stopped"))
    
    \* Components should be in restoring state during restore
    /\ []((restoreInProgress = TRUE) =>
        <>(componentSetState = "Restoring"))
    
    \* After restore completes, process should restart
    /\ []((~restoreInProgress /\ processState = "Stopped" /\ componentSetState = "Running") =>
        <>(processState = "Starting"))
    
    \* Process should eventually return to running after restore
    /\ []((~restoreInProgress /\ processState = "Starting") =>
        <>(processState = "Running"))
    
    \* Overall system should return to running state
    /\ []((~restoreInProgress /\ processState = "Running" /\ componentSetState = "Running") =>
        <>(overallState = "Running"))

\* The complete specification with scenario
SpecWithScenario == Spec /\ NormalRestoreScenario

============================================================================= 