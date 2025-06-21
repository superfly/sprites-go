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

	// Create a simple command that will fork and exit, leaving a zombie
	cmd := exec.Command("sh", "-c", "sleep 0.1 & exit")

	// Start the command
	if err := cmd.Start(); err != nil {
		http.Error(w, fmt.Sprintf("Failed to start zombie creator: %v", err), http.StatusInternalServerError)
		return
	}

	// Get the PID of the shell process
	pid := cmd.Process.Pid

	// Don't wait for it - let it become a zombie
	// The shell will exit, and its child (sleep) will be orphaned and adopted by PID 1

	// Give it a moment to create the zombie
	time.Sleep(200 * time.Millisecond)

	h.logger.Info("Created zombie process for testing", "parent_pid", pid)

	// Return the PID
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"message": "Zombie process created",
		"pid":     pid,
		"note":    "The sleep child process should be adopted by PID 1 and become a zombie when it exits",
	})
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
