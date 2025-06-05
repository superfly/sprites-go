---------------------------- MODULE sprite_env_trace ----------------------------

EXTENDS sprite_env, Naturals, Sequences, TLC, Json, IOUtils

\* Trace validation variables
VARIABLE traceIndex

\* Load the trace from JSON file (set via environment variable)
Trace == JsonDeserialize(IOEnv.TRACE_PATH)

\* Check if current step matches expected event
IsEvent(expectedEvent) ==
    /\ traceIndex \in 1..Len(Trace)
    /\ traceIndex' = traceIndex + 1
    /\ IF "event" \in DOMAIN Trace[traceIndex]
       THEN Trace[traceIndex].event = expectedEvent
       ELSE TRUE
    /\ UpdateStateFromTrace(Trace[traceIndex])

\* Update state variables based on trace entry
UpdateStateFromTrace(entry) ==
    /\ IF "overallState" \in DOMAIN entry 
       THEN overallState' = ApplyUpdates(overallState, "overallState", entry)
       ELSE overallState' = overallState
    /\ IF "dbState" \in DOMAIN entry
       THEN dbState' = ApplyUpdates(dbState, "dbState", entry) 
       ELSE dbState' = dbState
    /\ IF "fsState" \in DOMAIN entry
       THEN fsState' = ApplyUpdates(fsState, "fsState", entry)
       ELSE fsState' = fsState
    /\ IF "processState" \in DOMAIN entry
       THEN processState' = ApplyUpdates(processState, "processState", entry)
       ELSE processState' = processState
    \* Add other variables as needed...

\* Apply JSON updates to a variable
ApplyUpdates(var, varName, entry) ==
    IF varName \in DOMAIN entry
    THEN LET updates == entry[varName]
         IN IF Len(updates) > 0
            THEN ApplyUpdate(var, updates[1])
            ELSE var
    ELSE var

\* Apply a single update operation
ApplyUpdate(var, update) ==
    CASE update.op = "Update" -> update.args[1]
      [] update.op = "Set" -> update.args[1]
      [] OTHER -> var

\* Trace-constrained actions
TraceInit ==
    /\ Init
    /\ traceIndex = 1

\* Constrained next-state relation - each action checks against trace
TraceNext ==
    \/ /\ IsEvent("StateTransition")
       /\ Next

TraceSpec == TraceInit /\ [][TraceNext]_<<vars, traceIndex>>

\* Validation property: trace should be fully consumed
TraceAccepted == TLCGet("stats").diameter - 1 = Len(Trace)

============================================================================= 