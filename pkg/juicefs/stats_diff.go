package juicefs

// ComputeByteDelta computes a simple delta between prev and curr byte slices by
// identifying a common prefix and suffix, and returning the differing middles.
// It also classifies the change type and returns the index where the change
// begins in the current buffer.
func ComputeByteDelta(prev, curr []byte) (changeType string, changeAt int, oldDelta, newDelta []byte) {
    // Find common prefix
    i := 0
    maxPrefix := len(curr)
    if len(prev) < maxPrefix {
        maxPrefix = len(prev)
    }
    for i < maxPrefix && curr[i] == prev[i] {
        i++
    }

    // Find common suffix (avoid overlapping the prefix)
    j1 := len(curr)
    j2 := len(prev)
    for j1 > i && j2 > i && curr[j1-1] == prev[j2-1] {
        j1--
        j2--
    }

    oldDelta = prev[i:j2]
    newDelta = curr[i:j1]
    changeAt = i

    // Classify change
    changeType = "modify"
    if len(prev) == 0 {
        changeType = "init"
    } else if len(oldDelta) == 0 && len(newDelta) > 0 && len(curr) >= len(prev) {
        changeType = "append"
    } else if len(newDelta) == 0 && len(oldDelta) > 0 {
        changeType = "shrink"
    }

    return
}

// TruncateBytes converts bytes to string and truncates to max characters,
// appending an ellipsis if truncated.
func TruncateBytes(b []byte, max int) string {
    if len(b) <= max {
        return string(b)
    }
    return string(b[:max]) + "…"
}


