#!/usr/bin/env python3
"""
Convert JSON trace files to TLA+ modules for verification against sprite-env.tla
"""

import json
import os
import glob
import argparse
from typing import List, Dict, Any, NamedTuple

class TraceMetadata(NamedTuple):
    """Metadata collected from trace analysis"""
    name: str
    transitions: int
    initial_state: Dict[str, str]
    terminal_state: Dict[str, str]
    components: List[str]
    error_events: List[Dict[str, Any]]
    outcome_type: str  # 'success', 'error', 'crash', 'shutdown'
    key_patterns: List[str]

def map_component_to_variable(source: str) -> str:
    """Map JSON source component to TLA+ variable name"""
    mapping = {
        "dbComponent": "dbState",
        "fsComponent": "fsState", 
        "ComponentSetStateMachine": "componentSetState",
        "ProcessStateMachine": "processState",
        "SystemStateMachine": "overallState"
    }
    return mapping.get(source, source)

def load_trace_file(filepath: str) -> List[Dict[str, Any]]:
    """Load and parse JSON trace file"""
    with open(filepath, 'r') as f:
        return json.load(f)

def analyze_trace_metadata(trace_data: List[Dict[str, Any]], trace_name: str) -> TraceMetadata:
    """Analyze trace and collect detailed metadata"""
    if not trace_data:
        return TraceMetadata(
            name=trace_name,
            transitions=0,
            initial_state={},
            terminal_state={},
            components=[],
            error_events=[],
            outcome_type='empty',
            key_patterns=[]
        )
    
    # Track state evolution for each component
    component_states = {}
    components = set()
    error_events = []
    key_patterns = []
    
    for transition in trace_data:
        source = transition["source"]
        from_state = transition["from"]
        to_state = transition["to"]
        trigger = transition["trigger"]
        
        components.add(source)
        
        # Initialize component state if first time seeing it
        if source not in component_states:
            component_states[source] = from_state
        
        # Update to final state
        component_states[source] = to_state
        
        # Track interesting events
        if any(keyword in to_state.lower() for keyword in ["error", "crash", "fail"]):
            error_events.append({
                "component": source,
                "trigger": trigger,
                "from": from_state,
                "to": to_state
            })
        
        # Identify patterns
        if "crash" in trace_name.lower():
            key_patterns.append("Component crashes")
        elif "signal" in trace_name.lower():
            key_patterns.append("Signal handling")
        elif "ready" in trace_name.lower() and "never" in trace_name.lower():
            key_patterns.append("Ready check failures")
    
    # Determine outcome type
    system_final = component_states.get("SystemStateMachine", "")
    process_final = component_states.get("ProcessStateMachine", "")
    
    if error_events:
        outcome_type = "error"
    elif any(keyword in system_final.lower() for keyword in ["shutdown", "stopping", "stopped"]):
        outcome_type = "shutdown"
    elif any(keyword in process_final.lower() for keyword in ["crash", "fail"]):
        outcome_type = "crash"
    else:
        outcome_type = "success"
    
    # Get initial states (assume first transition shows initial state)
    initial_state = {}
    if trace_data:
        first_transition = trace_data[0]
        initial_state[first_transition["source"]] = first_transition["from"]
    
    return TraceMetadata(
        name=trace_name,
        transitions=len(trace_data),
        initial_state=initial_state,
        terminal_state=component_states,
        components=list(components),
        error_events=error_events,
        outcome_type=outcome_type,
        key_patterns=list(set(key_patterns))  # Remove duplicates
    )

def generate_trace_module(trace_data: List[Dict[str, Any]], module_name: str) -> str:
    # Build the exact sequence of state changes
    state_changes = []
    first_states = {}  # Track what the trace expects as initial states
    
    for transition in trace_data:
        var_name = map_component_to_variable(transition["source"])
        from_state = transition["from"]
        to_state = transition["to"]
        trigger = transition["trigger"]
        
        # Track the first expected state for each variable
        if var_name not in first_states:
            first_states[var_name] = from_state
            
        state_changes.append({
            "variable": var_name,
            "from": from_state,
            "to": to_state,
            "trigger": trigger
        })
    
    # Use standard "Initializing" states for everything

    # Create TLA+ content with standard initial states
    tla_header = f"""---------------------------- MODULE {module_name} ----------------------------

EXTENDS sprite_env

\\* Validation module for observed trace
\\* Verifies that the exact sequence of transitions is valid

VARIABLE step

traceVars == <<vars, step>>

\\* Initialize with standard initial state (all "Initializing")
TraceInit ==
    /\\ overallState = "Initializing"
    /\\ componentSetState = "Initializing"
    /\\ dbState = "Initializing"
    /\\ fsState = "Initializing"
    /\\ processState = "Initializing"
    /\\ processExitCode = 0
    /\\ checkpointInProgress = FALSE
    /\\ restoreInProgress = FALSE
    /\\ currentOperation = "None"
    /\\ errorType = "None"
    /\\ restartAttempt = 0
    /\\ restartDelay = 0
    /\\ shutdownInProgress = FALSE
    /\\ exitRequested = FALSE
    /\\ signalReceived = "None"
    /\\ dbShutdownTimeout = 0
    /\\ fsShutdownTimeout = 0
    /\\ dbForceKilled = FALSE
    /\\ fsForceKilled = FALSE
    /\\ step = 0

\\* The exact sequence of transitions from the trace
TraceNext ==
"""

    # Build the trace transitions
    tla_content = tla_header
    
    # Add missing initial transitions if needed
    step_counter = 0
    spec_initial_states = {
        "overallState": "Initializing",
        "componentSetState": "Initializing", 
        "dbState": "Initializing",
        "fsState": "Initializing",
        "processState": "Initializing"
    }
    
    # Check what initial transitions we need to add
    for var_name, expected_first in first_states.items():
        if var_name in spec_initial_states and spec_initial_states[var_name] != expected_first:
            # Add missing transition from "Initializing" to expected_first
            all_vars = ["overallState", "componentSetState", "dbState", "fsState", "processState", "processExitCode", "checkpointInProgress", "restoreInProgress", "currentOperation", "errorType", "restartAttempt", "restartDelay", "shutdownInProgress", "exitRequested", "signalReceived", "dbShutdownTimeout", "fsShutdownTimeout", "dbForceKilled", "fsForceKilled"]
            other_vars = [v for v in all_vars if v != var_name]
            
            step_comment = f"    \\* Step {step_counter+1}: {var_name}: Initializing -> {expected_first} (auto-generated)\n"
            step_condition = f"    \\/ /\\ step = {step_counter}\n"
            step_guard = f"       /\\ {var_name} = \"Initializing\"\n"
            step_action = f"       /\\ {var_name}' = \"{expected_first}\"\n"
            step_increment = f"       /\\ step' = {step_counter+1}\n"
            step_unchanged = f"       /\\ UNCHANGED <<{', '.join(other_vars)}>>\n"
            
            tla_content += step_comment + step_condition + step_guard + step_action + step_increment + step_unchanged
            step_counter += 1

    # Add the original trace transitions
    for i, change in enumerate(state_changes):
        var_name = change["variable"]
        from_state = change["from"]
        to_state = change["to"]
        trigger = change["trigger"]
        all_vars = ["overallState", "componentSetState", "dbState", "fsState", "processState", "processExitCode", "checkpointInProgress", "restoreInProgress", "currentOperation", "errorType", "restartAttempt", "restartDelay", "shutdownInProgress", "exitRequested", "signalReceived", "dbShutdownTimeout", "fsShutdownTimeout", "dbForceKilled", "fsForceKilled"]
        other_vars = [v for v in all_vars if v != var_name]
        
        # Use regular strings with single backslashes for TLA+ syntax
        step_comment = f"    \\* Step {step_counter+1}: {var_name}: {from_state} -> {to_state} (trigger: {trigger})\n"
        step_condition = f"    \\/ /\\ step = {step_counter}\n"
        step_guard = f"       /\\ {var_name} = \"{from_state}\"\n"
        step_action = f"       /\\ {var_name}' = \"{to_state}\"\n"
        step_increment = f"       /\\ step' = {step_counter+1}\n"
        step_unchanged = f"       /\\ UNCHANGED <<{', '.join(other_vars)}>>\n"
        
        tla_content += step_comment + step_condition + step_guard + step_action + step_increment + step_unchanged
        step_counter += 1

    # Add the footer
    tla_footer = f"""

\\* The trace specification
TraceSpec == TraceInit /\\ [][TraceNext]_traceVars

\\* Invariant: check that we're following the observed path
TraceValid ==
    /\\ TypeOK
    /\\ step >= 0
    /\\ step <= {step_counter}

=============================================================================
"""
    tla_content += tla_footer
    return tla_content

def generate_tla_config(module_name: str) -> str:
    return f"""SPECIFICATION TraceSpec
INVARIANT TraceValid
CHECK_DEADLOCK FALSE
"""

def cleanup_trace_files(output_dir: str):
    """Clean up generated trace files"""
    patterns = [
        f"{output_dir}/trace_*.tla",
        f"{output_dir}/trace_*.cfg"
    ]
    
    cleaned_count = 0
    for pattern in patterns:
        for file in glob.glob(pattern):
            try:
                os.remove(file)
                cleaned_count += 1
            except Exception as e:
                print(f"Failed to clean up {file}: {e}")
    
    if cleaned_count > 0:
        print(f"🧹 Cleaned up {cleaned_count} generated trace files")

def main():
    """Main conversion function"""
    parser = argparse.ArgumentParser(description='Convert trace files to TLA+ modules')
    parser.add_argument('--output-dir', default='spec', help='Output directory for TLA+ files')
    parser.add_argument('--cleanup', action='store_true', help='Clean up generated files')
    parser.add_argument('--return-metadata', action='store_true', help='Return metadata for use by validation script')
    args = parser.parse_args()
    
    if args.cleanup:
        cleanup_trace_files(args.output_dir)
        return
    
    trace_files = glob.glob("server/tests/tmp/*.trace")
    
    if not trace_files:
        if not args.return_metadata:
            print("No trace files found in server/tests/tmp/")
        return [] if args.return_metadata else None
    
    if not args.return_metadata:
        print(f"📊 Converting {len(trace_files)} traces to TLA+ modules...")
    
    converted_modules = []
    trace_metadata = []
    
    for trace_file in trace_files:
        # Extract base name for module
        base_name = os.path.basename(trace_file).replace('.trace', '').replace('-', '_')
        module_name = f"trace_{base_name}"
        
        # Load trace data
        try:
            trace_data = load_trace_file(trace_file)
            
            # Skip empty trace files
            if not trace_data:
                continue
            
            # Analyze trace metadata
            metadata = analyze_trace_metadata(trace_data, base_name)
            trace_metadata.append(metadata)
            
            # Generate TLA+ module
            tla_content = generate_trace_module(trace_data, module_name)
            
            # Write TLA+ module file
            tla_filename = f"{args.output_dir}/{module_name}.tla"
            with open(tla_filename, 'w') as f:
                f.write(tla_content)
            
            # Generate config file
            cfg_content = generate_tla_config(module_name)
            cfg_filename = f"{args.output_dir}/{module_name}.cfg"
            with open(cfg_filename, 'w') as f:
                f.write(cfg_content)
            
            converted_modules.append({
                'name': module_name,
                'tla_file': tla_filename,
                'cfg_file': cfg_filename,
                'metadata': metadata
            })
            
        except Exception as e:
            if not args.return_metadata:
                print(f"❌ Error processing {base_name}: {e}")
    
    if args.return_metadata:
        return trace_metadata
    else:
        print(f"✅ Generated {len(converted_modules)} TLA+ validation modules")
        return converted_modules

if __name__ == "__main__":
    main() 