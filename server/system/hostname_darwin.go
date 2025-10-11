//go:build darwin

package system

// setContainerHostname is a no-op on macOS - this only runs on Linux
func setContainerHostname(hostname string) error {
	// No-op: sprite-env only runs on Linux in production
	return nil
}

// getHostname is a no-op on macOS - this only runs on Linux
func getHostname() (string, error) {
	// No-op: sprite-env only runs on Linux in production
	return "", nil
}
