package runner

var (
	// Export common errors for callers who want to switch on them.
	ErrMissingStdout  = errMissingStdout
	ErrMissingStderr  = errMissingStderr
	ErrConflictingTTY = errConflictingTTY
)
