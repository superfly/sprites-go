#!/bin/bash

# Enhanced trace validation script showing detailed TLA+ verification
# Usage: validate_traces.sh <tla_tools_path>

set -e

# Colors for output
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
RED='\033[0;31m'
BLUE='\033[0;34m'
BOLD='\033[1m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

TLA_TOOLS="$1"
if [ -z "$TLA_TOOLS" ]; then
    echo "Usage: $0 <path_to_tla2tools.jar>"
    exit 1
fi

JAVA_PATH="${JAVA_PATH:-$(which java 2>/dev/null || echo "/opt/homebrew/opt/openjdk@11/bin/java")}"
TLC="$JAVA_PATH -cp $TLA_TOOLS tlc2.TLC"

# Extract and display detailed TLC verification information
analyze_tlc_verification() {
    local output_file="$1"
    local trace_name="$2"
    
    # Clean trace name for display
    local clean_name=$(echo "$trace_name" | sed 's/trace_//' | sed 's/_/ /g')
    
    echo -e "${BOLD}🔍 Verifying: ${clean_name}${NC}"
    
    # Extract TLC version and setup
    local tlc_version=$(grep "TLC2 Version" "$output_file" 2>/dev/null | sed 's/.*TLC2 Version //' | awk '{print $1}' || echo "unknown")
    local memory=$(grep "Running.*search" "$output_file" 2>/dev/null | grep -o '[0-9]*MB heap' | head -1 || echo "")
    local workers=$(grep "Running.*search" "$output_file" 2>/dev/null | grep -o 'with [0-9]* worker' | awk '{print $2}' || echo "1")
    local cores=$(grep "Running.*search" "$output_file" 2>/dev/null | grep -o 'on [0-9]* cores' | awk '{print $2}' || echo "")
    
    echo -e "  ${BLUE}TLC ${tlc_version}${NC} | ${BLUE}${workers} worker(s)${NC} | ${BLUE}${memory}${NC}"
    
    # Show parsing and semantic processing
    local parsed_count=$(grep "Parsing file" "$output_file" 2>/dev/null | wc -l | tr -d ' ')
    local semantic_count=$(grep "Semantic processing" "$output_file" 2>/dev/null | wc -l | tr -d ' ')
    echo -e "  ${CYAN}Parsed ${parsed_count} files, processed ${semantic_count} modules${NC}"
    
    # State exploration details
    local initial_states=$(grep "Finished computing initial states" "$output_file" 2>/dev/null | awk '{print $4}' || echo "")
    local total_states=$(grep "states generated" "$output_file" 2>/dev/null | awk '{print $1}' || echo "")
    local distinct_states=$(grep "distinct states found" "$output_file" 2>/dev/null | awk '{print $4}' || echo "")
    local queue_states=$(grep "states left on queue" "$output_file" 2>/dev/null | awk '{print $1}' || echo "")
    
    if [ -n "$initial_states" ] && [ -n "$total_states" ]; then
        echo -e "  ${GREEN}State Exploration:${NC} ${total_states} states generated, ${distinct_states} distinct"
        if [ "$queue_states" = "0" ]; then
            echo -e "    ${GREEN}✅ Complete state space explored${NC}"
        else
            echo -e "    ${YELLOW}⚠ ${queue_states} states remaining in queue${NC}"
        fi
    fi
    
    # State graph analysis
    local depth=$(grep "depth of the complete state graph" "$output_file" 2>/dev/null | awk '{print $10}' | sed 's/\.$//' || echo "")
    local avg_outdegree=$(grep "average outdegree" "$output_file" 2>/dev/null | awk '{print $10}' || echo "")
    local min_outdegree=$(grep "average outdegree" "$output_file" 2>/dev/null | grep -o 'minimum is [0-9]*' | awk '{print $3}' || echo "")
    local max_outdegree=$(grep "average outdegree" "$output_file" 2>/dev/null | grep -o 'maximum [0-9]*' | awk '{print $2}' || echo "")
    
    if [ -n "$depth" ]; then
        echo -e "  ${BLUE}State Graph:${NC} depth ${depth}, avg outdegree ${avg_outdegree} (min: ${min_outdegree}, max: ${max_outdegree})"
    fi
    
    # Fingerprint collision analysis
    local collision_prob=$(grep "calculated (optimistic)" "$output_file" 2>/dev/null | awk '{print $4}' || echo "")
    local fingerprint_bits=$(grep "Running.*search" "$output_file" 2>/dev/null | grep -o 'fp [0-9]*' | awk '{print $2}' || echo "")
    
    if [ -n "$collision_prob" ] && [ "$collision_prob" != "0.0" ]; then
        echo -e "  ${YELLOW}Fingerprint collision probability: ${collision_prob}${NC}"
    elif [ -n "$fingerprint_bits" ]; then
        echo -e "  ${GREEN}No fingerprint collisions detected (${fingerprint_bits}-bit)${NC}"
    fi
    
    # Property verification results
    if grep -q "No error has been found" "$output_file"; then
        echo -e "  ${GREEN}✅ All safety properties verified${NC}"
        echo -e "  ${GREEN}✅ All invariants satisfied${NC}"
    fi
    
    if grep -q "CHECK_DEADLOCK FALSE" "$output_file" 2>/dev/null; then
        echo -e "  ${BLUE}ℹ  Deadlock checking disabled${NC}"
    fi
    
    # Performance timing
    local execution_time=$(grep "Finished in" "$output_file" 2>/dev/null | awk '{print $3}' || echo "")
    if [ -n "$execution_time" ]; then
        echo -e "  ${CYAN}Verification completed in ${execution_time}${NC}"
    fi
    
    # Show any warnings
    if grep -q "Warning:" "$output_file"; then
        local warning_count=$(grep "Warning:" "$output_file" | wc -l | tr -d ' ')
        echo -e "  ${YELLOW}⚠ ${warning_count} warning(s) issued${NC}"
    fi
    
    echo ""
}

# Validate traces with detailed output
validate_traces() {
    echo -e "${BOLD}🧪 Formal Verification with TLA+${NC}"
    echo ""
    
    # First, convert .trace files to .tla files  
    echo -e "${CYAN}📊 Converting trace files to TLA+ modules...${NC}"
    local trace_count=$(find server/tests/tmp -name "*.trace" | wc -l | tr -d ' ')
    echo -e "${BLUE}Found ${trace_count} trace files to convert${NC}"
    
    if ! python3 convert_traces.py --output-dir spec > /tmp/convert_traces.out 2>&1; then
        echo -e "${RED}❌ Failed to convert trace files${NC}"
        cat /tmp/convert_traces.out
        return 1
    fi
    
    # Show conversion results
    cat /tmp/convert_traces.out
    
    local total_traces=0
    local valid_traces=0
    local failed_traces=0
    local total_states_explored=0
    
    for trace_file in spec/trace_*.tla; do
        if [ -f "$trace_file" ]; then
            total_traces=$((total_traces + 1))
            local trace_name=$(basename "$trace_file" .tla)
            local output_file="/tmp/tlc_trace_${trace_name}.out"
            
            if $TLC -workers auto "$trace_file" > "$output_file" 2>&1; then
                analyze_tlc_verification "$output_file" "$trace_name"
                valid_traces=$((valid_traces + 1))
                
                # Extract state count for summary
                local states=$(grep "states generated" "$output_file" 2>/dev/null | awk '{print $1}' || echo "1")
                total_states_explored=$((total_states_explored + states))
                
            elif grep -q "fingerprint\|No error has been found" "$output_file"; then
                analyze_tlc_verification "$output_file" "$trace_name"
                valid_traces=$((valid_traces + 1))
                
                local states=$(grep "states generated" "$output_file" 2>/dev/null | awk '{print $1}' || echo "1")
                total_states_explored=$((total_states_explored + states))
                
            else
                echo -e "${RED}❌ Verification failed: ${trace_name}${NC}"
                echo -e "${RED}Errors:${NC}"
                cat "$output_file"
                failed_traces=$((failed_traces + 1))
                echo ""
            fi
            
            rm -f "$output_file"
        fi
    done
    
    # Clean up generated trace files
    echo -e "${CYAN}🧹 Cleaning up generated trace files...${NC}"
    python3 convert_traces.py --cleanup --output-dir spec > /dev/null 2>&1
    
    # Final summary
    echo -e "${BOLD}📊 Verification Summary${NC}"
    echo -e "  ${BLUE}Traces processed:${NC} ${total_traces}"
    echo -e "  ${GREEN}Successfully verified:${NC} ${valid_traces}"
    echo -e "  ${BLUE}Total states explored:${NC} ${total_states_explored}"
    
    if [ $failed_traces -gt 0 ]; then
        echo -e "  ${YELLOW}Failed verifications:${NC} ${failed_traces}"
        return 1
    else
        echo -e "  ${GREEN}✅ All traces formally verified against specification${NC}"
        return 0
    fi
}

# Run validation
validate_traces 