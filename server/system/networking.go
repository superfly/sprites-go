package system

import (
	"fmt"
	"path/filepath"
	"time"

	"github.com/superfly/sprite-env/server/api"
)

// initializeNetworkServices initializes network components (API, socket, admin channel)
func (s *System) initializeNetworkServices() error {
	// Initialize admin channel first (no dependencies)
	if err := s.initializeAdminChannel(); err != nil {
		// Non-fatal - continue without admin channel
		s.logger.Warn("Failed to initialize admin channel", "error", err)
	}

	// Initialize API server (always create, may be no-op if not configured)
	if err := s.initializeAPIServer(); err != nil {
		return fmt.Errorf("failed to initialize API server: %w", err)
	}

	// Initialize socket server
	if err := s.initializeSocketServer(); err != nil {
		// Non-fatal - services API won't be available
		s.logger.Warn("Failed to initialize socket server", "error", err)
	}

	return nil
}

// initializeAdminChannel creates the admin channel
func (s *System) initializeAdminChannel() error {
	channelURL := s.config.AdminChannelURL
	if channelURL == "" {
		channelURL = "https://api.sprites.dev/internal/admin"
	}

	// Always create admin channel struct, even if not configured
	// This ensures AdminChannel is never nil and can safely receive Push calls
	s.AdminChannel = &AdminChannel{
		url:    channelURL,
		token:  s.config.APIToken,
		logger: s.logger,
		env:    s.Environment,
		system: s, // Set system reference for handling sprite assignment
	}

	if s.config.APIToken == "" {
		s.logger.Info("Admin channel disabled (no API token) - messages will be discarded")
	}

	return nil
}

// initializeAPIServer creates the API server
func (s *System) initializeAPIServer() error {
	// Calculate the sync target path
	var syncTargetPath string
	if s.config.JuiceFSBaseDir != "" {
		syncTargetPath = filepath.Join(s.config.JuiceFSBaseDir, "mount", "active", "fs")
	} else {
		// Fallback to /tmp/sync if JuiceFS is not configured
		syncTargetPath = "/tmp/sync"
	}

	apiConfig := api.Config{
		ListenAddr:         s.config.APIListenAddr,
		APIToken:           s.config.APIToken,
		AdminToken:         s.config.AdminToken,
		MaxWaitTime:        30 * time.Second,
		ContainerEnabled:   s.config.ContainerEnabled,
		SyncTargetPath:     syncTargetPath,
		ProxyLocalhostIPv4: s.config.ProxyLocalhostIPv4,
		ProxyLocalhostIPv6: s.config.ProxyLocalhostIPv6,
		SpriteVersion:      getVersion(),
	}

	// API server will be no-op if ListenAddr is empty
	apiServer, err := api.NewServer(apiConfig, s, s.ctx)
	if err != nil {
		return fmt.Errorf("failed to create API server: %w", err)
	}

	// Pass admin channel to API server for context enrichment
	if s.AdminChannel != nil {
		apiServer.SetAdminChannel(s.AdminChannel)
	}

	// Wire HTTP activity observation immediately
	apiServer.SetActivityObserver(func(start bool, source string) {
		if start {
			s.ActivityMonitor.ActivityStarted(source)
		} else {
			s.ActivityMonitor.ActivityEnded(source)
		}
	})

	s.APIServer = apiServer

	// Do not create tmux manager here; it is initialized in initializeServices()
	return nil
}

// initializeSocketServer creates the socket server
func (s *System) initializeSocketServer() error {
	sockServer, err := NewSockServer(s.ctx, s, s.config.LogDir)
	if err != nil {
		return fmt.Errorf("failed to create socket server: %w", err)
	}
	s.SocketServer = sockServer
	return nil
}
