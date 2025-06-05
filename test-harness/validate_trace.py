#!/usr/bin/env python3
"""
Simple trace validation script for sprite-env
Validates execution traces against the TLA+ specification
"""

import os
import sys
import subprocess
import argparse
from pathlib import Path

def run_trace_validation(trace_file, spec_file="trace-validation/sprite_env_trace.tla", 
                        config_file="trace-validation/sprite_env_trace.cfg", 
                        tla_tools_dir=None):
    """
    Run trace validation using TLC
    
    Args:
        trace_file: Path to the JSON trace file
        spec_file: Path to the TLA+ trace specification
        config_file: Path to the TLC config file  
        tla_tools_dir: Directory containing tla2tools.jar
    """
    
    # Find TLA+ tools
    if tla_tools_dir is None:
        # Try common locations
        for path in [
            "/opt/TLA+Toolbox/",
            "/usr/local/bin/",
            os.path.expanduser("~/tla+/"),
            "./tla-tools/"
        ]:
            if os.path.exists(os.path.join(path, "tla2tools.jar")):
                tla_tools_dir = path
                break
    
    if tla_tools_dir is None:
        print("Error: Could not find tla2tools.jar")
        print("Please specify the directory containing TLA+ tools with --tla-dir")
        return False
        
    tla2tools_jar = os.path.join(tla_tools_dir, "tla2tools.jar")
    
    if not os.path.exists(tla2tools_jar):
        print(f"Error: tla2tools.jar not found at {tla2tools_jar}")
        return False
        
    if not os.path.exists(trace_file):
        print(f"Error: Trace file not found: {trace_file}")
        return False
        
    if not os.path.exists(spec_file):
        print(f"Error: Specification file not found: {spec_file}")
        return False
    
    # Set environment variable for trace path
    env = os.environ.copy()
    env["TRACE_PATH"] = os.path.abspath(trace_file)
    
    # Build TLC command
    cmd = [
        "java", 
        "-jar", tla2tools_jar,
        "-config", config_file,
        "-deadlock",  # Allow checking deadlocks explicitly
        "-workers", "auto",  # Use available CPU cores
        spec_file
    ]
    
    print(f"Running trace validation...")
    print(f"Trace file: {trace_file}")
    print(f"Spec file: {spec_file}")
    print(f"Command: {' '.join(cmd)}")
    print("-" * 60)
    
    try:
        result = subprocess.run(cmd, env=env, capture_output=True, text=True)
        
        print("TLC Output:")
        print(result.stdout)
        
        if result.stderr:
            print("TLC Errors:")
            print(result.stderr)
            
        if result.returncode == 0:
            print("✅ Trace validation PASSED - Binary behavior is consistent with specification")
            return True
        else:
            print("❌ Trace validation FAILED - Binary behavior violates specification")
            print(f"Exit code: {result.returncode}")
            return False
            
    except Exception as e:
        print(f"Error running TLC: {e}")
        return False

def main():
    parser = argparse.ArgumentParser(
        description="Validate execution traces against TLA+ specification"
    )
    parser.add_argument("trace_file", help="Path to JSON trace file")
    parser.add_argument("--spec", default="trace-validation/sprite_env_trace.tla", 
                       help="Path to TLA+ trace specification")
    parser.add_argument("--config", default="trace-validation/sprite_env_trace.cfg",
                       help="Path to TLC config file")
    parser.add_argument("--tla-dir", help="Directory containing tla2tools.jar")
    
    args = parser.parse_args()
    
    success = run_trace_validation(
        args.trace_file, 
        args.spec, 
        args.config, 
        args.tla_dir
    )
    
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main() 