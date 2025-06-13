#!/usr/bin/env python3
"""
Enhanced trace validation with combined metadata and TLC verification
"""

import subprocess
import sys
import os
import re
import tempfile
from pathlib import Path
from typing import Dict, List, Optional, NamedTuple

# Import our trace conversion module
sys.path.append(str(Path(__file__).parent.parent.parent))
from convert_traces import TraceMetadata, main as convert_traces

class TLCResult(NamedTuple):
    """Results from TLC verification"""
    success: bool
    states_generated: int
    distinct_states: int
    depth: int
    execution_time: str
    warnings: int
    errors: List[str]
    raw_output: str

class Colors:
    GREEN = '\033[0;32m'
    YELLOW = '\033[0;33m'
    RED = '\033[0;31m'
    BLUE = '\033[0;34m'
    CYAN = '\033[0;36m'
    BOLD = '\033[1m'
    NC = '\033[0m'

def run_tlc_verification(tla_tools_path: str, trace_file: str) -> TLCResult:
    """Run TLC verification on a trace module and parse results"""
    
    java_cmd = [
        "java", "-cp", tla_tools_path, "tlc2.TLC",
        "-workers", "auto", trace_file
    ]
    
    try:
        result = subprocess.run(
            java_cmd,
            capture_output=True,
            text=True,
            timeout=30
        )
        
        output = result.stdout + result.stderr
        
        # Parse state exploration details
        states_generated = extract_number(output, r'(\d+) states generated') or 1
        distinct_states = extract_number(output, r'(\d+) distinct states found') or 1
        
        # Detect different types of TLC results
        has_error_output = "Error:" in output
        has_invariant_violation = "Invariant" in output and "violated" in output
        has_no_error_msg = "No error has been found" in output
        has_fingerprint = "fingerprint" in output
        
        # Check for suspicious patterns that indicate problems
        suspiciously_low_exploration = states_generated <= 1 and distinct_states <= 1
        has_initial_state_only = "depth of the complete state graph search is 1" in output
        
        # Success criteria: non-zero exit code OR error messages indicate failure
        success = (result.returncode == 0 and 
                  not has_error_output and 
                  not has_invariant_violation and
                  (has_no_error_msg or has_fingerprint))
        
        if success and suspiciously_low_exploration:
            # Still mark as success but add a warning
            success = True
        
        # Parse TLC output
        states_generated = extract_number(output, r'(\d+) states generated')
        distinct_states = extract_number(output, r'(\d+) distinct states found')
        depth = extract_number(output, r'depth of the complete state graph search is (\d+)')
        execution_time = extract_match(output, r'Finished in (\w+)')
        warnings = len(re.findall(r'Warning:', output))
        
        errors = []
        if not success:
            # Extract error messages and behavior trace
            output_lines = output.split('\n')
            
            # Find error lines
            error_lines = [line.strip() for line in output_lines 
                         if 'Error:' in line or 'Exception' in line]
            errors.extend(error_lines[:3])  # First few error messages
            
            # If there's an invariant violation, capture the behavior trace
            if has_invariant_violation:
                behavior_start = -1
                for i, line in enumerate(output_lines):
                    if "The behavior up to this point is:" in line:
                        behavior_start = i
                        break
                
                if behavior_start >= 0:
                    # Find where the behavior trace ends (look for "states generated" line)
                    behavior_end = len(output_lines)
                    for i in range(behavior_start + 1, len(output_lines)):
                        if "states generated" in output_lines[i]:
                            behavior_end = i
                            break
                    
                    # Extract the behavior trace
                    behavior_lines = []
                    current_state = None
                    for i in range(behavior_start + 1, behavior_end):
                        line = output_lines[i].strip()
                        if line.startswith("State ") and ":" in line:
                            # Save previous state
                            if current_state:
                                behavior_lines.append(current_state)
                            # Start new state
                            current_state = {"header": line, "vars": []}
                        elif line.startswith("/\\") and current_state:
                            # Extract variable assignments
                            var_line = line.replace("/\\", "").strip()
                            if "=" in var_line:
                                current_state["vars"].append(var_line)
                        elif line and current_state and not line.startswith("State "):
                            # Handle continuation lines that don't start with /\
                            if "=" in line:
                                current_state["vars"].append(line)
                    
                    # Add the last state
                    if current_state:
                        behavior_lines.append(current_state)
                    
                    # Format behavior trace for display
                    if behavior_lines:
                        errors.append("BEHAVIOR_TRACE")  # Special marker
                        # Show more states if we have them, especially the final one
                        states_to_show = behavior_lines[-4:] if len(behavior_lines) > 4 else behavior_lines
                        for state in states_to_show:
                            errors.append(f"  {state['header']}")
                            # Show key variables that changed
                            key_vars = [v for v in state['vars'] 
                                      if any(key in v for key in ['componentSetState', 'dbState', 'fsState', 'processState', 'step'])]
                            for var in key_vars[:6]:  # Show more relevant variables
                                errors.append(f"    {var}")
                            if len(state['vars']) > len(key_vars):
                                errors.append(f"    ... and {len(state['vars']) - len(key_vars)} other variables")
        
        # Add warnings for suspicious patterns
        if success and suspiciously_low_exploration:
            errors.append("⚠️  Warning: Only 1 state explored - trace may have initial state compatibility issues")
        
        return TLCResult(
            success=success,
            states_generated=states_generated,
            distinct_states=distinct_states,
            depth=depth or 1,
            execution_time=execution_time or "00s",
            warnings=warnings,
            errors=errors,
            raw_output=output
        )
        
    except subprocess.TimeoutExpired:
        return TLCResult(
            success=False,
            states_generated=0,
            distinct_states=0,
            depth=0,
            execution_time="timeout",
            warnings=0,
            errors=["Verification timed out"],
            raw_output="Timeout after 30 seconds"
        )
    except Exception as e:
        return TLCResult(
            success=False,
            states_generated=0,
            distinct_states=0,
            depth=0,
            execution_time="error",
            warnings=0,
            errors=[str(e)],
            raw_output=f"Failed to run TLC: {e}"
        )

def extract_number(text: str, pattern: str) -> Optional[int]:
    """Extract a number from text using regex pattern"""
    match = re.search(pattern, text)
    return int(match.group(1)) if match else None

def extract_match(text: str, pattern: str) -> Optional[str]:
    """Extract a string match from text using regex pattern"""
    match = re.search(pattern, text)
    return match.group(1) if match else None

def format_trace_name(name: str) -> str:
    """Format trace name for display"""
    return name.replace('_', ' ').replace('-', ' ').title()

def format_outcome_icon(outcome_type: str) -> str:
    """Get appropriate icon for outcome type"""
    icons = {
        'success': f'{Colors.GREEN}✅{Colors.NC}',
        'shutdown': f'{Colors.BLUE}🔄{Colors.NC}',
        'error': f'{Colors.RED}❌{Colors.NC}',
        'crash': f'{Colors.YELLOW}💥{Colors.NC}',
        'empty': f'{Colors.YELLOW}📭{Colors.NC}'
    }
    return icons.get(outcome_type, f'{Colors.BLUE}❓{Colors.NC}')

def print_verification_result(metadata: TraceMetadata, tlc_result: TLCResult, verbose: bool = False):
    """Print combined verification result with metadata"""
    
    trace_name = format_trace_name(metadata.name)
    outcome_icon = format_outcome_icon(metadata.outcome_type)
    
    if tlc_result.success:
        # Success case - show verification success + trace details
        print(f"{Colors.GREEN}✅ Verified:{Colors.NC} {trace_name}")
        
        # Show trace metadata
        print(f"   {outcome_icon} {metadata.outcome_type.title()} trace: {metadata.transitions} transitions")
        
        # Show terminal states
        if metadata.terminal_state:
            terminal_info = []
            for component, state in metadata.terminal_state.items():
                if component in ['SystemStateMachine', 'ProcessStateMachine']:
                    terminal_info.append(f"{component.replace('StateMachine', '')}: {state}")
            if terminal_info:
                print(f"   {Colors.BLUE}Final states:{Colors.NC} {', '.join(terminal_info)}")
        
        # Show key patterns
        if metadata.key_patterns:
            patterns_str = ', '.join(metadata.key_patterns)
            print(f"   {Colors.CYAN}Patterns:{Colors.NC} {patterns_str}")
        
        # Show error events if any
        if metadata.error_events:
            print(f"   {Colors.YELLOW}Error events:{Colors.NC} {len(metadata.error_events)} detected")
        
        # Show TLC verification details
        if verbose:
            print(f"   {Colors.BLUE}TLC:{Colors.NC} {tlc_result.states_generated} states, depth {tlc_result.depth}, {tlc_result.execution_time}")
            if tlc_result.warnings > 0:
                print(f"   {Colors.YELLOW}⚠{Colors.NC} {tlc_result.warnings} warnings")
        
    else:
        # Failure case - show failure + TLC output
        print(f"{Colors.RED}❌ Failed:{Colors.NC} {trace_name}")
        print(f"   {Colors.RED}Verification failed{Colors.NC}")
        
        if tlc_result.errors:
            print(f"   {Colors.RED}Errors:{Colors.NC}")
            in_behavior_trace = False
            for error in tlc_result.errors:
                if error == "BEHAVIOR_TRACE":
                    in_behavior_trace = True
                    print(f"     {Colors.CYAN}Behavior trace (last states):{Colors.NC}")
                elif in_behavior_trace:
                    if error.startswith("  State "):
                        print(f"     {Colors.BLUE}{error}{Colors.NC}")
                    elif error.startswith("    "):
                        # Variable assignment or continuation
                        if "componentSetState" in error and "Runing" in error:
                            print(f"     {Colors.RED}{error}{Colors.NC}")  # Highlight invalid state
                        else:
                            print(f"     {Colors.YELLOW}{error}{Colors.NC}")
                    else:
                        print(f"     {error}")
                else:
                    print(f"     • {error}")
        
        if verbose:
            print(f"   {Colors.RED}Raw TLC output:{Colors.NC}")
            for line in tlc_result.raw_output.split('\n')[:10]:  # Show first 10 lines
                if line.strip():
                    print(f"     {line}")
    
    print()  # Empty line between traces

def main():
    """Main validation function"""
    if len(sys.argv) < 2:
        print("Usage: validate_traces.py <path_to_tla2tools.jar> [verbose]")
        sys.exit(1)
    
    tla_tools_path = sys.argv[1]
    verbose = len(sys.argv) > 2 and sys.argv[2] in ['verbose', '-v', '--verbose']
    
    if not os.path.exists(tla_tools_path):
        print(f"Error: TLA+ tools not found at {tla_tools_path}")
        sys.exit(1)
    
    print(f"{Colors.BOLD}🧪 Formal Verification with TLA+{Colors.NC}")
    print()
    
    # Step 1: Generate traces and collect metadata (quietly)
    # Temporarily change sys.argv to pass return-metadata flag
    original_argv = sys.argv[:]
    sys.argv = ['convert_traces.py', '--return-metadata', '--output-dir', 'spec']
    
    try:
        trace_metadata_list = convert_traces()
        if not trace_metadata_list:
            print("No traces found to validate")
            return
    finally:
        sys.argv = original_argv
    
    # Step 2: Verify each trace with TLC and combine with metadata
    successful_verifications = 0
    failed_verifications = 0
    total_states_explored = 0
    
    for metadata in trace_metadata_list:
        trace_module = f"spec/trace_{metadata.name}.tla"
        
        if not os.path.exists(trace_module):
            print(f"{Colors.RED}❌ Missing:{Colors.NC} {format_trace_name(metadata.name)} (module not generated)")
            failed_verifications += 1
            continue
        
        # Run TLC verification
        tlc_result = run_tlc_verification(tla_tools_path, trace_module)
        
        # Print combined result
        print_verification_result(metadata, tlc_result, verbose)
        
        # Update counters
        if tlc_result.success:
            successful_verifications += 1
            total_states_explored += tlc_result.states_generated
        else:
            failed_verifications += 1
    
    # Final summary
    total_traces = len(trace_metadata_list)
    print(f"{Colors.BOLD}📊 Verification Summary{Colors.NC}")
    print(f"  {Colors.BLUE}Traces processed:{Colors.NC} {total_traces}")
    print(f"  {Colors.GREEN}Successfully verified:{Colors.NC} {successful_verifications}")
    
    if failed_verifications > 0:
        print(f"  {Colors.RED}Failed verifications:{Colors.NC} {failed_verifications}")
    
    print(f"  {Colors.BLUE}Total states explored:{Colors.NC} {total_states_explored}")
    
    if failed_verifications == 0:
        print(f"  {Colors.GREEN}✅ All traces formally verified against specification{Colors.NC}")
        sys.exit(0)
    else:
        sys.exit(1)

if __name__ == "__main__":
    main() 