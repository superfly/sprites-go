package system

import (
	"github.com/superfly/sprite-env/pkg/services"
)

// GetServicesManager returns the services manager
func (s *System) GetServicesManager() *services.Manager {
	return s.ServicesManager
}

// GetLogDir returns the log directory
func (s *System) GetLogDir() string {
	return s.config.LogDir
}
