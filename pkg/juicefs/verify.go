package juicefs

import (
	"context"
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"time"
)

// JuiceFSStatus represents the output of `juicefs status` command
type JuiceFSStatus struct {
	Setting struct {
		Name             string `json:"Name"`
		UUID             string `json:"UUID"`
		Storage          string `json:"Storage"`
		Bucket           string `json:"Bucket"`
		BlockSize        int    `json:"BlockSize"`
		Compression      string `json:"Compression"`
		EncryptAlgo      string `json:"EncryptAlgo"`
		TrashDays        int    `json:"TrashDays"`
		MetaVersion      int    `json:"MetaVersion"`
		MinClientVersion string `json:"MinClientVersion"`
		DirStats         bool   `json:"DirStats"`
		EnableACL        bool   `json:"EnableACL"`
	} `json:"Setting"`
	Sessions []struct {
		Sid        int       `json:"Sid"`
		Expire     time.Time `json:"Expire"`
		Version    string    `json:"Version"`
		HostName   string    `json:"HostName"`
		IPAddrs    []string  `json:"IPAddrs"`
		MountPoint string    `json:"MountPoint"`
		MountTime  time.Time `json:"MountTime"`
		ProcessID  int       `json:"ProcessID"`
	} `json:"Sessions"`
	Stat struct {
		UsedSpace       int64 `json:"UsedSpace"`
		AvailableSpace  int64 `json:"AvailableSpace"`
		UsedInodes      int64 `json:"UsedInodes"`
		AvailableInodes int64 `json:"AvailableInodes"`
	} `json:"Stat"`
}

// VerifyMountReadiness performs comprehensive verification that the JuiceFS mount
// is fully ready for block device operations. This helps prevent deadlocks that
// can occur when attempting block operations too quickly after mount.
func (j *JuiceFS) VerifyMountReadiness(ctx context.Context) error {
	metaDB := filepath.Join(j.config.BaseDir, "metadata.db")
	metaURL := fmt.Sprintf("sqlite3://%s", metaDB)
	mountPath := filepath.Join(j.config.BaseDir, "data")

	j.logger.Info("Starting comprehensive JuiceFS mount verification")

	// Step 1: Verify JuiceFS status
	if err := j.verifyJuiceFSStatus(ctx, metaURL, mountPath); err != nil {
		return fmt.Errorf("juicefs status verification failed: %w", err)
	}

	// Step 2: Only status verification here. File and block-device probing happens in overlay.

	j.logger.Info("JuiceFS mount verification completed successfully")
	return nil
}

// verifyJuiceFSStatus runs `juicefs status` and validates the output
func (j *JuiceFS) verifyJuiceFSStatus(ctx context.Context, metaURL, expectedMountPath string) error {
	j.logger.Debug("Running juicefs status command", "metaURL", metaURL)

	cmd := exec.CommandContext(ctx, "juicefs", "status", metaURL)
	cmd.Env = append(os.Environ(), "JUICEFS_LOG_FORMAT=json")

	output, err := cmd.Output()
	if err != nil {
		if exitErr, ok := err.(*exec.ExitError); ok {
			return fmt.Errorf("juicefs status failed: %w, stderr: %s", err, string(exitErr.Stderr))
		}
		return fmt.Errorf("juicefs status failed: %w", err)
	}

	// Parse the JSON output
	var status JuiceFSStatus
	if err := json.Unmarshal(output, &status); err != nil {
		return fmt.Errorf("failed to parse juicefs status output: %w", err)
	}

	j.logger.Debug("JuiceFS status retrieved",
		"name", status.Setting.Name,
		"uuid", status.Setting.UUID,
		"storage", status.Setting.Storage,
		"sessions", len(status.Sessions))

	// Filter sessions for our mount point
	var (
		now             = time.Now()
		candidateNewest *struct {
			Sid        int
			Expire     time.Time
			Version    string
			HostName   string
			IPAddrs    []string
			MountPoint string
			MountTime  time.Time
			ProcessID  int
		}
		candidateByPID *struct {
			Sid        int
			Expire     time.Time
			Version    string
			HostName   string
			IPAddrs    []string
			MountPoint string
			MountTime  time.Time
			ProcessID  int
		}
	)

	for i := range status.Sessions {
		s := &status.Sessions[i]
		if s.MountPoint != expectedMountPath {
			continue
		}

		// Ignore clearly expired sessions
		if now.After(s.Expire) {
			j.logger.Debug("Ignoring expired JuiceFS session",
				"sid", s.Sid,
				"mountPoint", s.MountPoint,
				"expire", s.Expire,
				"mountTime", s.MountTime,
				"pid", s.ProcessID)
			continue
		}

		// Prefer session matching our mount process PID
		if j.mountCmd != nil && j.mountCmd.Process != nil && s.ProcessID == j.mountCmd.Process.Pid {
			candidateByPID = &struct {
				Sid        int
				Expire     time.Time
				Version    string
				HostName   string
				IPAddrs    []string
				MountPoint string
				MountTime  time.Time
				ProcessID  int
			}{Sid: s.Sid, Expire: s.Expire, Version: s.Version, HostName: s.HostName, IPAddrs: s.IPAddrs, MountPoint: s.MountPoint, MountTime: s.MountTime, ProcessID: s.ProcessID}
			break
		}

		// Track newest unexpired session by mount time as fallback
		if candidateNewest == nil || s.MountTime.After(candidateNewest.MountTime) {
			candidateNewest = &struct {
				Sid        int
				Expire     time.Time
				Version    string
				HostName   string
				IPAddrs    []string
				MountPoint string
				MountTime  time.Time
				ProcessID  int
			}{Sid: s.Sid, Expire: s.Expire, Version: s.Version, HostName: s.HostName, IPAddrs: s.IPAddrs, MountPoint: s.MountPoint, MountTime: s.MountTime, ProcessID: s.ProcessID}
		}
	}

	var selected *struct {
		Sid        int
		Expire     time.Time
		Version    string
		HostName   string
		IPAddrs    []string
		MountPoint string
		MountTime  time.Time
		ProcessID  int
	}
	if candidateByPID != nil {
		selected = candidateByPID
	} else {
		selected = candidateNewest
	}

	if selected == nil {
		return fmt.Errorf("no active, unexpired JuiceFS session found for mount path %s", expectedMountPath)
	}

	j.logger.Info("Validated active JuiceFS session",
		"sid", selected.Sid,
		"version", selected.Version,
		"hostname", selected.HostName,
		"mountPoint", selected.MountPoint,
		"mountTime", selected.MountTime,
		"pid", selected.ProcessID,
		"expire", selected.Expire)

	// Log filesystem statistics
	j.logger.Debug("JuiceFS filesystem statistics",
		"usedSpaceBytes", status.Stat.UsedSpace,
		"availableSpaceBytes", status.Stat.AvailableSpace,
		"usedInodes", status.Stat.UsedInodes,
		"availableInodes", status.Stat.AvailableInodes)

	return nil
}

// (Removed) File probe now lives in overlay and is executed before loop attach.

// enhancedMountReadinessCheck is an enhanced version of isMountReady that includes
// the comprehensive verification checks
func (j *JuiceFS) enhancedMountReadinessCheck(ctx context.Context, mountPath string) bool {
	// First do the basic checks
	if !j.isMountReady(mountPath) {
		return false
	}

	// Then run the comprehensive verification
	if err := j.VerifyMountReadiness(ctx); err != nil {
		j.logger.Warn("Enhanced mount readiness check failed", "error", err)
		return false
	}

	return true
}
