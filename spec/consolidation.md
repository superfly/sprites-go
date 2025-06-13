# State Consolidation Guide

This document explains how to consolidate the state definitions in `sprite_env.tla` to make them more consistent across system, component_set, components, and processes.

**Status: ✅ COMPLETED** - The `sprite_env.tla` specification has been updated according to these recommendations.

## Current Problems

### 1. Inconsistent State Categories
- **Process states** have unique transition states like `"Signaling"` 
- **Component states** have operation-specific states like `"Restoring"`, `"Checkpointing"`
- **System states** mix operational and readiness states
- **Final states** vary significantly between entities

### 2. Naming Inconsistencies
- Some entities use `"Stopped"` vs `"Shutdown"` inconsistently
- Transition states don't follow common patterns
- Mixed vocabulary makes the spec harder to reason about

## Recommended Solution

### 1. Base State Categories
Create shared base state categories that all entities inherit:

```tla
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
```

### 2. Entity-Specific Extensions
Each entity adds only the states it specifically needs:

```tla
\* Process-specific states
ProcessSpecificStates == {
    "Signaling",       \* Process receiving signal
    "Exited",          \* Process exited normally  
    "Crashed",         \* Process crashed
    "Killed"           \* Process was killed
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
    "Checkpointing"    \* System-level checkpoint operation
}
```

### 3. Unified Definitions
```tla
ProcessStates == BaseTransitionStates \cup BaseFinalStates \cup BaseActiveStates \cup BaseErrorStates \cup ProcessSpecificStates

ComponentStates == BaseTransitionStates \cup BaseFinalStates \cup BaseActiveStates \cup BaseErrorStates \cup ComponentSpecificStates

SystemStates == BaseTransitionStates \cup BaseFinalStates \cup BaseActiveStates \cup BaseErrorStates \cup SystemSpecificStates
```

## Migration Steps

### Step 1: Update State Definitions
Replace the current separate state definitions with the consolidated approach.

### Step 2: Update Helper Predicates
Modify helper predicates to work with the new unified state model:

```tla
\* Generic state type predicates that work across entities
IsTransitionState(state, entityType) == 
    state \in BaseTransitionStates \cup 
    (IF entityType = "Process" THEN {"Signaling"} ELSE {}) \cup
    (IF entityType \in {"Component", "System"} THEN {"Restoring", "Checkpointing"} ELSE {})

IsFinalState(state, entityType) == 
    state \in BaseFinalStates \cup 
    (IF entityType = "Process" THEN {"Exited", "Crashed", "Killed"} ELSE {})
```

### Step 3: Update State Transition Functions
Modify the state transition functions to use the new consistent state names and ensure all transitions remain valid.

### Step 4: Update Type Invariants
Update the TypeOK invariant to reference the new unified state definitions.

## Benefits

1. **Consistency**: All entities share common state vocabulary
2. **Maintainability**: Base state changes propagate to all entities  
3. **Extensibility**: Easy to add entity-specific states as needed
4. **Clarity**: Clear distinction between temporary and permanent states
5. **Reusability**: Helper functions work across all entity types

## Backward Compatibility

The changes preserve all existing behavior:
- All current state values remain valid
- State transition logic is preserved
- Only the organization and helper predicates change

## Verification

After consolidation, verify that:
1. All existing state transitions still work
2. Type invariants pass
3. Temporal properties are preserved
4. No new deadlocks are introduced 