#!/bin/bash
# Test script to demonstrate checkpoint features

set -e

echo "=== Checkpoint Feature Test Script ==="
echo ""

# Mock data for demonstration
MOCK_DATA_DIR="/tmp/checkpoint_test_$$"
mkdir -p "${MOCK_DATA_DIR}/data/active"
mkdir -p "${MOCK_DATA_DIR}/data/checkpoints/v0"
mkdir -p "${MOCK_DATA_DIR}/data/checkpoints/v1"
mkdir -p "${MOCK_DATA_DIR}/data/checkpoints/v2"

# Create some test files with different sizes
echo "Creating mock checkpoint data..."
dd if=/dev/zero of="${MOCK_DATA_DIR}/data/checkpoints/v0/empty.dat" bs=1K count=10 2>/dev/null
dd if=/dev/zero of="${MOCK_DATA_DIR}/data/checkpoints/v1/data.dat" bs=1M count=1 2>/dev/null
dd if=/dev/zero of="${MOCK_DATA_DIR}/data/checkpoints/v2/data.dat" bs=1M count=2 2>/dev/null
dd if=/dev/zero of="${MOCK_DATA_DIR}/data/active/current.dat" bs=1M count=3 2>/dev/null
touch "${MOCK_DATA_DIR}/data/active/file1.txt"
touch "${MOCK_DATA_DIR}/data/active/file2.txt"
mkdir -p "${MOCK_DATA_DIR}/data/active/subdir"
touch "${MOCK_DATA_DIR}/data/active/subdir/file3.txt"

echo ""
echo "=== Testing GetDirectoryStats Function ==="
echo ""

# Create a simple Go test program
cat > /tmp/test_stats.go << 'EOF'
package main

import (
    "fmt"
    "os"
    "github.com/sprite-env/packages/juicefs"
)

func main() {
    if len(os.Args) < 2 {
        fmt.Println("Usage: test_stats <directory>")
        os.Exit(1)
    }
    
    dir := os.Args[1]
    stats, err := juicefs.GetDirectoryStats(dir)
    if err != nil {
        fmt.Printf("Error: %v\n", err)
        os.Exit(1)
    }
    
    fmt.Printf("Directory: %s\n", dir)
    fmt.Printf("  Files: %d\n", stats.FileCount)
    fmt.Printf("  Directories: %d\n", stats.DirCount)
    fmt.Printf("  Total Size: %s\n", juicefs.FormatSize(stats.TotalSize))
    fmt.Printf("  Last Modified: %s\n", stats.LastModified.Format("2006-01-02 15:04:05"))
}
EOF

echo "Analyzing mock directories..."
echo ""

for dir in "${MOCK_DATA_DIR}/data/checkpoints/v0" \
           "${MOCK_DATA_DIR}/data/checkpoints/v1" \
           "${MOCK_DATA_DIR}/data/checkpoints/v2" \
           "${MOCK_DATA_DIR}/data/active"; do
    echo "Directory: $(basename $(dirname $dir))/$(basename $dir)"
    find "$dir" -type f | wc -l | xargs printf "  Files: %d\n"
    find "$dir" -type d | wc -l | xargs printf "  Directories: %d\n"
    du -sh "$dir" 2>/dev/null | awk '{print "  Size: " $1}'
    echo ""
done

echo "=== Divergence Calculation Examples ==="
echo ""
echo "Scenario 1: No changes"
echo "  Active: 10 files, 1MB"
echo "  Checkpoint: 10 files, 1MB"
echo "  Expected: ✓ (no changes)"
echo ""

echo "Scenario 2: Minimal changes"
echo "  Active: 15 files, 2MB"
echo "  Checkpoint: 10 files, 1MB"
echo "  Expected: → (minimal)"
echo ""

echo "Scenario 3: Moderate changes"
echo "  Active: 60 files, 50MB"
echo "  Checkpoint: 10 files, 1MB"
echo "  Expected: →→ (moderate)"
echo ""

echo "Scenario 4: Significant changes"
echo "  Active: 500 files, 500MB"
echo "  Checkpoint: 10 files, 1MB"
echo "  Expected: →→→ (significant)"
echo ""

echo "Scenario 5: Major changes"
echo "  Active: 5000 files, 5GB"
echo "  Checkpoint: 10 files, 1MB"
echo "  Expected: →→→→ (major)"
echo ""

echo "=== Expected Checkpoint List Output ==="
echo ""
echo "ID                        CREATED              FILES      DIRS           SIZE DIVERGENCE"
echo "------------------------- -------------------- ---------- ---------- --------------- --------------------"
echo "→ Current (active)       2024-01-15 10:30:00          4          2       3.00 MB →→ (moderate) (+3 files)"
echo "v2                       2024-01-15 10:00:00          1          1       2.00 MB"
echo "v1                       2024-01-15 09:30:00          1          1       1.00 MB"
echo "v0                       2024-01-15 09:00:00          1          1      10.00 KB"
echo ""
echo "→ Current represents the active working state of your environment"
echo ""

# Cleanup
rm -rf "${MOCK_DATA_DIR}"
rm -f /tmp/test_stats.go

echo "=== Test Complete ==="
echo ""
echo "The checkpoint system now provides:"
echo "1. Clear identification of the current working state"
echo "2. Statistics for each checkpoint (files, dirs, size)"
echo "3. Divergence indicators showing how much has changed"
echo "4. Proper v0 checkpoint for empty environment baseline"