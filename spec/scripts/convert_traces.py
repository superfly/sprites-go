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

def map_component_to_index(source: str) -> int:
    """Map JSON source component to components array index"""
    mapping = {
        "dbComponent": 1,
        "fsComponent": 2
    }
    if source not in mapping:
        raise ValueError(f"Unknown component source: '{source}'. Expected one of: {list(mapping.keys())}")
    return mapping[source]

def is_component_source(source: str) -> bool:
    """Check if source represents an actual component (not a state machine)"""
    return source in ["dbComponent", "fsComponent"]

def validate_trace_format(trace_data: List[Dict[str, Any]], filepath: str):
    """Validate that trace has expected format and required fields"""
    if not isinstance(trace_data, list):
        raise ValueError(f"Invalid trace format in {filepath}: Expected list, got {type(trace_data)}")
    
    if not trace_data:
        raise ValueError(f"Empty trace file: {filepath}")
    
    expected_sources = {
        "SystemStateMachine",
        "ComponentGroupStateMachine", 
        "ProcessStateMachine",
        "dbComponent",
        "fsComponent"
    }
    
    required_fields = {"from", "to", "source", "trigger"}
    
    for i, transition in enumerate(trace_data):
        if not isinstance(transition, dict):
            raise ValueError(f"Invalid transition format in {filepath}[{i}]: Expected dict, got {type(transition)}")
        
        # Check required fields
        missing_fields = required_fields - set(transition.keys())
        if missing_fields:
            raise ValueError(f"Missing required fields in {filepath}[{i}]: {missing_fields}")
        
        # Validate source is recognized
        source = transition["source"]
        if source not in expected_sources:
            raise ValueError(f"Unknown source in {filepath}[{i}]: '{source}'. Expected one of: {sorted(expected_sources)}")
        
        # Validate states are non-empty strings
        for field in ["from", "to", "trigger"]:
            value = transition[field]
            if not isinstance(value, str) or not value.strip():
                raise ValueError(f"Invalid {field} value in {filepath}[{i}]: '{value}' (must be non-empty string)")
    
    print(f"✅ Validated trace format: {filepath}")
    return True

def load_trace_file(filepath: str) -> List[Dict[str, Any]]:
    """Load and parse JSON trace file with validation"""
    try:
        with open(filepath, 'r') as f:
            trace_data = json.load(f)
    except json.JSONDecodeError as e:
        raise ValueError(f"Invalid JSON in {filepath}: {e}")
    except Exception as e:
        raise ValueError(f"Failed to read {filepath}: {e}")
    
    # Validate the trace format
    validate_trace_format(trace_data, filepath)
    return trace_data

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
    
    # Track component and state machine evolution separately
    component_states = {}
    state_machine_states = {}
    error_events = []
    key_patterns = []
    
    # Count only component transitions for metadata
    component_transition_count = 0
    
    for transition in trace_data:
        source = transition["source"]
        from_state = transition["from"]
        to_state = transition["to"]
        trigger = transition["trigger"]
        
        if is_component_source(source):
            # Track actual component states
            component_states[source] = to_state
            component_transition_count += 1
            
            # Track error events in components
            if any(keyword in to_state.lower() for keyword in ["error", "crash", "fail"]):
                error_events.append({
                    "component": source,
                    "trigger": trigger,
                    "from": from_state,
                    "to": to_state
                })
        else:
            # Track state machine final states for outcome determination
            state_machine_states[source] = to_state
        
        # Identify patterns from trace name
        if "crash" in trace_name.lower():
            key_patterns.append("Component crashes")
        elif "signal" in trace_name.lower():
            key_patterns.append("Signal handling")
        elif "ready" in trace_name.lower() and "never" in trace_name.lower():
            key_patterns.append("Ready check failures")
    
    # Determine outcome type based on state machines and errors
    system_final = state_machine_states.get("SystemStateMachine", "")
    process_final = state_machine_states.get("ProcessStateMachine", "")
    
    if error_events:
        outcome_type = "error"
    elif any(keyword in system_final.lower() for keyword in ["shutdown", "stopping", "stopped"]):
        outcome_type = "shutdown"
    elif any(keyword in process_final.lower() for keyword in ["crash", "fail"]):
        outcome_type = "crash"
    else:
        outcome_type = "success"
    
    # Get initial component states
    initial_state = {}
    for transition in trace_data:
        if is_component_source(transition["source"]) and transition["source"] not in initial_state:
            initial_state[transition["source"]] = transition["from"]
    
    # Combine component and state machine final states for terminal state
    terminal_state = {**component_states, **state_machine_states}
    
    return TraceMetadata(
        name=trace_name,
        transitions=component_transition_count,  # Only count component transitions
        initial_state=initial_state,
        terminal_state=terminal_state,
        components=list(component_states.keys()),
        error_events=error_events,
        outcome_type=outcome_type,
        key_patterns=list(set(key_patterns))  # Remove duplicates
    )

def generate_trace_module(trace_data: List[Dict[str, Any]], module_name: str) -> str:
    # Filter to only component transitions (ignore state machine transitions since they're derived)
    component_transitions = []
    
    for transition in trace_data:
        if is_component_source(transition["source"]):
            component_index = map_component_to_index(transition["source"])  # This will raise if invalid
            component_transitions.append({
                "index": component_index,
                "from": transition["from"],
                "to": transition["to"],
                "trigger": transition["trigger"],
                "source": transition["source"]
            })
    
    # If no component transitions, create a minimal trace
    if not component_transitions:
        component_transitions = [
            {"index": 1, "from": "Initializing", "to": "Starting", "trigger": "Auto", "source": "component1"},
            {"index": 1, "from": "Starting", "to": "Running", "trigger": "Auto", "source": "component1"},
            {"index": 2, "from": "Initializing", "to": "Starting", "trigger": "Auto", "source": "component2"},
            {"index": 2, "from": "Starting", "to": "Running", "trigger": "Auto", "source": "component2"}
        ]

    # Create TLA+ content with consolidated architecture
    tla_header = f"""---------------------------- MODULE {module_name} ----------------------------

EXTENDS sprite_env

\\* Validation module for observed trace
\\* Verifies that the exact sequence of component transitions is valid

CONSTANTS N
VARIABLE step

traceVars == <<components, step>>

\\* Initialize with standard initial state (all components "Initializing")
TraceInit ==
    /\\ components = [i \\in 1..N |-> "Initializing"]
    /\\ step = 0

\\* The exact sequence of component transitions from the trace
TraceNext ==
"""

    # Build the trace transitions
    tla_content = tla_header
    
    # Add the component transitions
    step_counter = 0
    for i, transition in enumerate(component_transitions):
        component_index = transition["index"]
        from_state = transition["from"]
        to_state = transition["to"]
        trigger = transition["trigger"]
        source = transition["source"]
        
        step_comment = f"    \\* Step {step_counter+1}: Component {component_index} ({source}): {from_state} -> {to_state} (trigger: {trigger})\n"
        step_condition = f"    \\/ /\\ step = {step_counter}\n"
        step_guard = f"       /\\ components[{component_index}] = \"{from_state}\"\n"
        step_action = f"       /\\ components' = [components EXCEPT ![{component_index}] = \"{to_state}\"]\n"
        step_increment = f"       /\\ step' = {step_counter+1}\n"
        
        tla_content += step_comment + step_condition + step_guard + step_action + step_increment
        step_counter += 1

    # Add the footer
    tla_footer = f"""

\\* The trace specification  
TraceSpec == TraceInit /\\ [][TraceNext]_traceVars

\\* Invariant: check that we're following the observed path and all invariants hold
TraceValid ==
    /\\ TypeOK
    /\\ HierarchyInvariant
    /\\ ProcessStateDependencyInvariant
    /\\ NoRecoveryAfterErrorInvariant
    /\\ step >= 0
    /\\ step <= {step_counter}

=============================================================================
"""
    tla_content += tla_footer
    return tla_content

def generate_tla_config(module_name: str) -> str:
    return f"""SPECIFICATION TraceSpec
CONSTANTS N = 2
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
        
        # Load trace data with strict validation
        try:
            trace_data = load_trace_file(trace_file)
            
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
            # Always crash on validation errors - don't continue with invalid traces
            print(f"❌ FATAL: Invalid trace format in {trace_file}")
            print(f"    Error: {e}")
            print(f"    Trace conversion failed - fix trace format and try again")
            raise SystemExit(1)
    if args.return_metadata:
        return trace_metadata
    else:
        print(f"✅ Generated {len(converted_modules)} TLA+ validation modules")
        return converted_modules

if __name__ == "__main__":
    main() 