package handlers

import (
	"encoding/json"
	"fmt"
	"net/http"
	"os/exec"
	"strings"
	"time"
)

// HandleDebugCreateZombie creates a zombie process and returns its PID
// This is a debug endpoint for testing zombie reaping functionality
func (h *Handlers) HandleDebugCreateZombie(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	// Subscribe to reap events before creating the process
	reapCh := h.system.SubscribeToReapEvents()
	defer h.system.UnsubscribeFromReapEvents(reapCh)

	// Create a simple process that will become a zombie
	// We use a shell command that exits immediately
	cmd := exec.Command("sh", "-c", "exit 0")

	// Start the process
	if err := cmd.Start(); err != nil {
		http.Error(w, fmt.Sprintf("Failed to create process: %v", err), http.StatusInternalServerError)
		return
	}

	// Get the PID before it becomes a zombie
	pid := cmd.Process.Pid
	h.logger.Info("Created process that will become zombie", "pid", pid)

	// Don't wait for it - this creates the zombie
	// The process has exited but we haven't called Wait()

	// Give it a moment to ensure the process exits
	time.Sleep(100 * time.Millisecond)

	// Check if it's a zombie now
	isZombie := false
	if statData, err := exec.Command("cat", fmt.Sprintf("/proc/%d/stat", pid)).Output(); err == nil {
		statStr := string(statData)
		if lastParen := strings.LastIndex(statStr, ")"); lastParen != -1 {
			fields := strings.Fields(statStr[lastParen+1:])
			if len(fields) > 0 && fields[0] == "Z" {
				isZombie = true
			}
		}
	}

	// Now wait for sprite to reap it using the event system
	reaped := false
	reapStartTime := time.Now()
	var reapDuration time.Duration

	// First check if it was already reaped (in case we missed the event)
	if wasReaped, reapTime := h.system.WasProcessReaped(pid); wasReaped {
		reaped = true
		reapDuration = reapTime.Sub(reapStartTime)
	} else {
		// Wait for the reap event
		timeout := time.After(1 * time.Second)
		for !reaped {
			select {
			case reapedPID := <-reapCh:
				if reapedPID == pid {
					reaped = true
					reapDuration = time.Since(reapStartTime)
				}
			case <-timeout:
				// Timeout - check one more time in case we missed it
				if wasReaped, reapTime := h.system.WasProcessReaped(pid); wasReaped {
					reaped = true
					reapDuration = reapTime.Sub(reapStartTime)
				} else {
					reapDuration = time.Since(reapStartTime)
				}
				goto done
			}
		}
	}

done:
	// Clean up - call Wait() to release resources if not already reaped
	go func() {
		cmd.Wait()
	}()

	result := map[string]interface{}{
		"message":       "Zombie reaping test completed",
		"pid":           pid,
		"was_zombie":    isZombie,
		"was_reaped":    reaped,
		"reap_duration": reapDuration.String(),
		"note":          "This is a debug endpoint for testing zombie process reaping",
	}

	if !isZombie {
		result["warning"] = "Process may have exited too quickly to observe zombie state"
	}

	if !reaped {
		result["error"] = "Process was not reaped within 1 second - sprite may not be functioning as init"
	} else {
		result["success"] = "Zombie was properly reaped by sprite (PID 1)"
	}

	h.logger.Info("Zombie reaping test result",
		"pid", pid,
		"was_zombie", isZombie,
		"was_reaped", reaped,
		"duration", reapDuration)

	// Return the result
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(result)
}

// HandleDebugCheckProcess checks if a process exists and its status
// This is a debug endpoint for testing zombie reaping functionality
func (h *Handlers) HandleDebugCheckProcess(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodGet {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	// Get PID from query parameter
	pidStr := r.URL.Query().Get("pid")
	if pidStr == "" {
		http.Error(w, "pid query parameter is required", http.StatusBadRequest)
		return
	}

	var pid int
	if _, err := fmt.Sscanf(pidStr, "%d", &pid); err != nil {
		http.Error(w, "Invalid pid format", http.StatusBadRequest)
		return
	}

	// Check if process exists by trying to send signal 0
	// This doesn't actually send a signal, just checks if we could
	err := exec.Command("kill", "-0", fmt.Sprintf("%d", pid)).Run()
	exists := err == nil

	// Try to get process status (if on Linux)
	var status string
	var isZombie bool

	statFile := fmt.Sprintf("/proc/%d/stat", pid)
	if data, err := exec.Command("cat", statFile).Output(); err == nil {
		// Parse the stat file - the status is the third field after the command name in parentheses
		statStr := string(data)
		if lastParen := strings.LastIndex(statStr, ")"); lastParen != -1 {
			fields := strings.Fields(statStr[lastParen+1:])
			if len(fields) > 0 {
				status = fields[0]
				isZombie = status == "Z"
			}
		}
	}

	// Also try ps command as a fallback
	var psStatus string
	if psOut, err := exec.Command("ps", "-p", fmt.Sprintf("%d", pid), "-o", "stat=").Output(); err == nil {
		psStatus = strings.TrimSpace(string(psOut))
		if strings.Contains(psStatus, "Z") || strings.Contains(psStatus, "<defunct>") {
			isZombie = true
		}
	}

	result := map[string]interface{}{
		"pid":       pid,
		"exists":    exists,
		"is_zombie": isZombie,
	}

	if status != "" {
		result["proc_status"] = status
	}
	if psStatus != "" {
		result["ps_status"] = psStatus
	}

	h.logger.Debug("Checked process status", "pid", pid, "exists", exists, "is_zombie", isZombie)

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(result)
}
