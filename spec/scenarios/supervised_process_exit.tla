---------------------------- MODULE supervised_process_exit ----------------------------

EXTENDS sprite_env

\* Supervised process exit scenario:
\* 1. Start with normal initialization 
\* 2. Components become Running
\* 3. Process starts and becomes Running  
\* 4. System reaches stable Running state
\* 5. Process exits autonomously (crash or normal exit)
\* 6. CASCADE: processState changes → overallState recomputes → components react
\* 7. System handles the exit appropriately (restart or shutdown)

SupervisedProcessExitScenario ==
    \* 1. Start with normal initialization
    /\ (componentSetState = "Initializing")
    /\ (dbState = "Initializing") 
    /\ (fsState = "Initializing")
    /\ (processState = "Initializing")
    /\ (systemState = "Initializing")
    /\ (restartAttempt = 0)
    /\ (errorType = "None")
    /\ (signalReceived = "None")
    /\ (shutdownInProgress = FALSE)

    \* 2. Components reach running state first
    /\ <> (componentSetState = "Running"
           /\ dbState = "Running" 
           /\ fsState = "Running"
           /\ processState = "Initializing")

    \* 3. Process starts after components are ready
    /\ []((componentSetState = "Running" /\ processState = "Initializing")
           => <>(processState = "Starting"))
           
    /\ []((processState = "Starting") 
           => <>(processState = "Running"))

    \* 4. System reaches stable running state  
    /\ <> (systemState = "Running"
           /\ componentSetState = "Running"
           /\ processState = "Running"
           /\ errorType = "None")

    \* 5. Process exits autonomously (not due to signal)
    /\ <> (processState = "Running" 
           /\ signalReceived = "None" 
           /\ ~shutdownInProgress
           /\ <>((processState \in {"Exited", "Crashed", "Killed"}) 
                 /\ processExitCode # 0))  \* Exit with error

    \* 6. CASCADE: When process exits, overall state must recompute immediately
    /\ [](((processState \in {"Exited", "Crashed", "Killed"}) /\ errorType = "None")
           => <>(errorType \in {"ProcessError", "ProcessCrash", "ProcessKilled"}))

    \* 7. Overall state reacts to the error  
    /\ []((errorType \in {"ProcessError", "ProcessCrash", "ProcessKilled"})
           => <>(overallState = "Error"))

    \* 8. System attempts restart (supervised behavior)
    /\ []((processState \in {"Crashed", "Exited", "Killed"})
           => <>(processState = "Starting" /\ restartAttempt > 0))

    \* 9. After restart, system can return to running
    /\ []((processState = "Starting" /\ restartAttempt > 0)
           => <>(processState = "Running"))

    \* 10. Eventually system recovers to running state  
    /\ <> (overallState = "Running" 
           /\ processState = "Running"
           /\ restartAttempt > 0)  \* Shows we recovered from exit

SpecWithProcessExitScenario == Spec /\ SupervisedProcessExitScenario

============================================================================= 