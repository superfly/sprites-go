# Trace Validation for sprite-env

This guide explains how to validate your binary's execution traces against the TLA+ specification to ensure your implementation follows the specified behavior.

## Overview

Trace validation works by:
1. **Instrumenting your binary** to output execution traces in JSON format
2. **Running TLC** on a special "trace specification" that consumes these traces
3. **Verifying** that the trace represents valid behavior according to your specification

This is **not exhaustive testing** - it only validates specific execution paths. But it's very effective at finding bugs and ensuring your implementation stays consistent with the specification.

## Quick Start

### 1. Install Prerequisites

- **TLA+ Tools**: Download `tla2tools.jar` from [TLA+ releases](https://github.com/tlaplus/tlaplus/releases)
- **Python 3.7+**

### 2. Instrument Your Binary

Modify your binary to output JSON traces. Each trace entry should look like:

```json
{
  "clock": 1,
  "overallState": [{"op": "Update", "path": [], "args": ["Initializing"]}],
  "dbState": [{"op": "Update", "path": [], "args": ["Initializing"]}],
  "event": "SystemStart"
}
```

**Key fields:**
- `clock`: Logical timestamp (monotonically increasing)
- `<variable>`: Array of updates to specification variables
- `event`: Name of the TLA+ action (optional but helpful)

**Update operations:**
- `{"op": "Update", "path": [], "args": ["newValue"]}` - Set variable to new value
- `{"op": "Set", "path": [], "args": ["newValue"]}` - Same as Update

### 3. Run Validation

```bash
./validate_trace.py my_trace.ndjson --tla-dir /path/to/tla+/tools/
```

Or test with the included example:
```bash
./validate_trace.py trace-validation/example_trace.ndjson --tla-dir /path/to/tla+/tools/
```

## Example Binary Instrumentation

Here's a simple example of how to instrument your binary:

```c
// C example (adapt to your language)
#include <stdio.h>
#include <time.h>

FILE* trace_file;
int trace_clock = 0;

void trace_state_change(const char* variable, const char* new_value, const char* event) {
    fprintf(trace_file, 
        "{\"clock\":%d,\"%s\":[{\"op\":\"Update\",\"path\":[],\"args\":[\"%s\"]}]",
        ++trace_clock, variable, new_value);
    
    if (event) {
        fprintf(trace_file, ",\"event\":\"%s\"", event);
    }
    
    fprintf(trace_file, "}\n");
    fflush(trace_file);
}

int main() {
    trace_file = fopen("trace.ndjson", "w");
    
    // Your system initialization
    trace_state_change("overallState", "Initializing", "SystemStart");
    trace_state_change("dbState", "Initializing", NULL);
    trace_state_change("fsState", "Initializing", NULL);
    
    // ... your system logic ...
    
    trace_state_change("dbState", "Running", "DBStarted");
    trace_state_change("fsState", "Running", "FSStarted");
    trace_state_change("overallState", "Running", "SystemReady");
    
    fclose(trace_file);
    return 0;
}
```

## What Gets Validated

The trace validation checks:

1. **State transitions** are valid according to your TLA+ spec
2. **Invariants** hold in all traced states  
3. **Action preconditions** are satisfied
4. **Variable updates** are consistent with action definitions

It does **NOT** check:
- Liveness properties (since traces are finite)
- Exhaustiveness (it only validates the specific execution)
- Timing constraints (traces are logical, not real-time)

## Tips for Effective Trace Validation

### 1. Choose Good Instrumentation Points

Instrument at points where:
- Shared state changes (database updates, file operations)
- Messages are sent/received  
- Process states change
- Critical operations complete

### 2. Balance Detail vs. Performance

**More detailed traces:**
- ✅ Better bug detection
- ✅ More confident validation
- ❌ Larger trace files
- ❌ Slower validation

**Less detailed traces:**
- ✅ Faster validation
- ✅ Smaller files
- ❌ May miss bugs
- ❌ May incorrectly pass

### 3. Handle Incomplete Information

You don't need to trace every variable. TLC can infer missing values using non-determinism in your spec. But be careful - too little information might make invalid traces appear valid.

### 4. Multiple Traces

Run validation on multiple different executions:
- Different input parameters
- Different timing/interleavings  
- Different error conditions
- Different system configurations

## Debugging Failed Validation

When validation fails, TLC will show you:

1. **Where the trace diverged** from the specification
2. **Which invariant was violated** (if any)
3. **The sequence of states** leading to the problem

Common issues:
- **Wrong grain of atomicity**: Your binary logs steps at different granularity than the spec
- **Missing state updates**: You forgot to trace some variable changes
- **Implementation bugs**: Your binary actually violates the specification (this is good to find!)

## Advanced Usage

### Custom Trace Specification

The provided `trace-validation/sprite_env_trace.tla` is a template. You may need to customize it for:
- Additional variables in your spec
- Complex data structures
- Specific event handling

### Multiple Processes

If your system has multiple processes, you can:
1. Have each process write its own trace file
2. Merge traces using timestamps
3. Validate the merged trace

### Integration Testing

Add trace validation to your CI/CD:
```bash
# Run your system with instrumentation
./your_binary --trace-output=test.ndjson

# Validate the trace
./validate_trace.py test.ndjson || exit 1
```

## Performance Notes

- **Use depth-first search** for long traces (`-dfid` flag to TLC)
- **Limit trace length** for initial testing
- **Use multiple workers** (`-workers auto` flag to TLC)
- **Consider sampling** for very high-frequency operations

## Further Reading

- [Original trace validation paper (2024)](https://inria.hal.science/hal-04813639v1/file/2404.16075v2.pdf)
- [TLA+ trace validation documentation](https://docs.tlapl.us/using:tlc:trace_validation)
- [Java trace validation library](https://github.com/lbinria/trace_validation_tools) 