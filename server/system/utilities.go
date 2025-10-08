package system

import (
	"github.com/superfly/sprite-env/pkg/tap"
)

// initializeUtilities initializes utility components (no dependencies)
func (s *System) initializeUtilities() error {
	// Initialize crash reporter
	var s3Config *tap.S3Config
	if s.config.S3AccessKey != "" && s.config.S3SecretAccessKey != "" {
		s3Config = &tap.S3Config{
			AccessKey:   s.config.S3AccessKey,
			SecretKey:   s.config.S3SecretAccessKey,
			EndpointURL: s.config.S3EndpointURL,
			Bucket:      s.config.S3Bucket,
			Region:      "us-east-1",
		}
	}

	crashReporter, err := tap.NewCrashReporter(s.logger, s.config.WriteDir, s3Config)
	if err != nil {
		s.logger.Warn("Failed to create crash reporter", "error", err)
		// Non-fatal, continue without crash reporting
	} else {
		s.CrashReporter = crashReporter
	}

	// Initialize reaper - always create, but it will be no-op if not PID 1
	s.Reaper = NewReaper(s.ctx)

	// Note: ResourceMonitor is initialized in services.go after AdminChannel is available

	return nil
}
