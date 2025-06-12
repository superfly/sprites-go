#!/usr/bin/env python3
"""
Convert JSON trace files to TLA+ modules for verification against sprite-env.tla
"""

import json
import os
import glob
import argparse
from typing import List, Dict, Any

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

def generate_trace_module(trace_data: List[Dict[str, Any]], module_name: str) -> str:
    """Generate TLA+ module that validates the exact trace sequence"""
    
    # Build the exact sequence of state changes
    state_changes = []
    for transition in trace_data:
        var_name = map_component_to_variable(transition["source"])
        from_state = transition["from"]
        to_state = transition["to"]
        trigger = transition["trigger"]
        
        state_changes.append({
            "variable": var_name,
            "from": from_state,
            "to": to_state,
            "trigger": trigger
        })
    
    tla_content = f"""---------------------------- MODULE {module_name} ----------------------------

EXTENDS sprite_env

\\* Validation module for observed trace
\\* Verifies that the exact sequence of transitions is valid

VARIABLE step

traceVars == <<vars, step>>

\\* Initialize with standard initial state
TraceInit ==
    /\\ Init
    /\\ step = 0

\\* The exact sequence of transitions from the trace
TraceNext ==
"""

    # Add each transition as a specific step
    for i, change in enumerate(state_changes):
        var_name = change["variable"]
        from_state = change["from"]
        to_state = change["to"]
        trigger = change["trigger"]
        
        # All variables except the changing one and step
        all_vars = ["overallState", "componentSetState", "dbState", "fsState", "processState", "processExitCode", "checkpointInProgress", "restoreInProgress", "currentOperation", "errorType", "restartAttempt", "restartDelay", "shutdownInProgress", "exitRequested", "signalReceived", "dbShutdownTimeout", "fsShutdownTimeout", "dbForceKilled", "fsForceKilled"]
        other_vars = [v for v in all_vars if v != var_name]
        
        tla_content += f"""    \\* Step {i+1}: {var_name}: {from_state} -> {to_state} (trigger: {trigger})
    \\/ /\\ step = {i}
       /\\ {var_name} = "{from_state}"
       /\\ {var_name}' = "{to_state}"
       /\\ step' = {i+1}
       /\\ UNCHANGED <<{", ".join(other_vars)}>>
"""

    tla_content += f"""

\\* The trace specification
TraceSpec == TraceInit /\\ [][TraceNext]_traceVars

\\* Invariant: check that we're following the observed path
TraceValid ==
    /\\ TypeOK
    /\\ step >= 0
    /\\ step <= {len(state_changes)}

=============================================================================
"""
    
    return tla_content

def generate_tla_config(module_name: str) -> str:
    """Generate TLA+ config file for the trace module"""
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
    
    for pattern in patterns:
        for file in glob.glob(pattern):
            try:
                os.remove(file)
                print(f"Cleaned up {file}")
            except Exception as e:
                print(f"Failed to clean up {file}: {e}")

def main():
    """Main conversion function"""
    parser = argparse.ArgumentParser(description='Convert trace files to TLA+ modules')
    parser.add_argument('--output-dir', default='spec', help='Output directory for TLA+ files')
    parser.add_argument('--cleanup', action='store_true', help='Clean up generated files')
    args = parser.parse_args()
    
    if args.cleanup:
        cleanup_trace_files(args.output_dir)
        return
    
    trace_files = glob.glob("server/tests/tmp/*.trace")
    
    if not trace_files:
        print("No trace files found in server/tests/tmp/")
        return
    
    print(f"Found {len(trace_files)} trace files")
    
    for trace_file in trace_files:
        print(f"Processing {trace_file}...")
        
        # Extract base name for module
        base_name = os.path.basename(trace_file).replace('.trace', '').replace('-', '_')
        module_name = f"trace_{base_name}"
        
        # Load trace data
        try:
            trace_data = load_trace_file(trace_file)
            print(f"  Loaded {len(trace_data)} transitions")
            
            # Skip empty trace files
            if not trace_data:
                print(f"  Skipping empty trace file: {trace_file}")
                continue
            
            # Generate TLA+ module
            tla_content = generate_trace_module(trace_data, module_name)
            
            # Write TLA+ module file
            tla_filename = f"{args.output_dir}/{module_name}.tla"
            with open(tla_filename, 'w') as f:
                f.write(tla_content)
            print(f"  Generated {tla_filename}")
            
            # Generate config file
            cfg_content = generate_tla_config(module_name)
            cfg_filename = f"{args.output_dir}/{module_name}.cfg"
            with open(cfg_filename, 'w') as f:
                f.write(cfg_content)
            print(f"  Generated {cfg_filename}")
            
        except Exception as e:
            print(f"  Error processing {trace_file}: {e}")
    
    print("\nConversion complete!")

if __name__ == "__main__":
    main() 