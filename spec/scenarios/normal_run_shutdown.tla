---------------------------- MODULE normal_run_shutdown ----------------------------

EXTENDS _sprite_env

\* Hierarchical normal run and shutdown scenario:
\* 1. Start with everything initializing, process has not started, zero restarts
\* 2. Components become Running, process still not started
\* 3. Only after components are Running, process moves to Starting
\* 4. Then process becomes Running, overallState becomes Running
\* 5. Signal received → overallState becomes ShuttingDown (process still Running)
\* 6. Process reacts to top-level shutdown → processState becomes Stopping
\* 7. Process completes stop → processState becomes Stopped
\* 8. Components react to process being stopped → componentSet shuts down

NormalRunScenario ==
    /\ (componentSetState = "Initializing")
    /\ (dbState = "Initializing")
    /\ (fsState = "Initializing")
    /\ (processState = "Initializing")
    /\ (restartAttempt = 0)
    /\ (overallState = "Initializing")
    /\ (signalReceived = "None")

    /\ <> (componentSetState = "Running"
           /\ dbState = "Running"
           /\ fsState = "Running"
           /\ processState = "Initializing")

    /\ []((componentSetState = "Running" /\ processState = "Initializing")
           => <>(processState = "Starting"))

    /\ []((processState = "Starting")
           => <>(processState = "Running" /\ overallState = "Running"))

    \* Signal received - top level changes first, process still running
    /\ <> (signalReceived = "SIGTERM" 
           /\ overallState = "ShuttingDown" 
           /\ processState = "Running")

    \* Process reacts to top-level shutdown state
    /\ []((overallState = "ShuttingDown" /\ processState = "Running")
           => <>(processState = "Stopping"))

    \* Process completes stopping
    /\ []((processState = "Stopping")
           => <>(processState = "Stopped"))

    \* Components react to process being stopped
    /\ []((processState = "Stopped")
           => <>(componentSetState = "ShuttingDown"))

    \* Components complete shutdown
    /\ []((componentSetState = "ShuttingDown")
           => <>(componentSetState = "Shutdown"))

SpecWithScenario == Spec /\ NormalRunScenario

============================================================================= 