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

	// Create a zombie by having a parent that forks a child and doesn't wait for it
	// The parent stays alive (sleep 3600) so the child remains a zombie
	cmd := exec.Command("sh", "-c", `
		# Create a C program that creates a zombie
		cat > /tmp/create_zombie.c << 'EOF'
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>

int main() {
    pid_t pid = fork();
    
    if (pid == 0) {
        // Child process - exit immediately
        exit(0);
    } else if (pid > 0) {
        // Parent process - print child PID and sleep without waiting
        printf("%d\n", pid);
        fflush(stdout);
        sleep(3600); // Sleep for an hour to keep the zombie
    }
    
    return 0;
}
EOF
		
		# Compile and run it
		gcc -o /tmp/create_zombie /tmp/create_zombie.c 2>/dev/null || {
			# Fallback if no gcc - use a simpler approach
			sh -c 'sleep 0.1 && exit 0' &
			CHILD=$!
			echo $CHILD
			# Keep this shell alive to maintain the zombie
			sleep 3600
		} &
		
		# Run the compiled program if it exists
		if [ -x /tmp/create_zombie ]; then
			/tmp/create_zombie &
		fi
		
		# Wait a bit for output
		sleep 0.1
	`)

	// Start the command in background
	if err := cmd.Start(); err != nil {
		http.Error(w, fmt.Sprintf("Failed to create zombie: %v", err), http.StatusInternalServerError)
		return
	}

	// Get the output quickly before detaching
	go func() {
		cmd.Wait()
	}()

	// Alternative simpler approach - use a known pattern that creates zombies
	zombieCmd := exec.Command("sh", "-c", "(sleep 0.1 && exit 0) & echo $!")
	output, err := zombieCmd.Output()
	if err != nil {
		http.Error(w, fmt.Sprintf("Failed to create zombie: %v", err), http.StatusInternalServerError)
		return
	}

	pidStr := strings.TrimSpace(string(output))
	var pid int
	if _, err := fmt.Sscanf(pidStr, "%d", &pid); err != nil {
		http.Error(w, fmt.Sprintf("Failed to parse zombie PID: %v", err), http.StatusInternalServerError)
		return
	}

	// Give it a moment to ensure the process exits and becomes zombie
	time.Sleep(500 * time.Millisecond)

	h.logger.Info("Created zombie process for testing", "zombie_pid", pid)

	// Return the PID
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"message": "Zombie process created",
		"pid":     pid,
		"note":    "This process should be in zombie state until reaped by init",
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
