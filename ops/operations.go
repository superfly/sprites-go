package ops

import "context"

// StreamID identifies a logical data stream for exec sessions.
// These values align with the server's exec protocol.
type StreamID uint8

const (
	StreamStdin    StreamID = 0
	StreamStdout   StreamID = 1
	StreamStderr   StreamID = 2
	StreamExit     StreamID = 3
	StreamStdinEOF StreamID = 4
	// StreamText represents a websocket text frame delivered out-of-band
	// (e.g., notifications). Consumers may route these to a handler.
	StreamText StreamID = 250
)

// ExecOptions captures the minimal options needed to start an exec operation.
type ExecOptions struct {
	Cmd     []string
	Env     map[string]string
	TTY     bool
	Cols    int
	Rows    int
	Workdir string
	// When false, server should not expect stdin; session will send StdinEOF immediately.
	HasStdin bool
}

// ExecSession provides a bidirectional streaming API for a single exec.
type ExecSession interface {
	// Write sends data to the process stdin (binary frame semantics).
	Write(p []byte) (int, error)
	// Read returns the next output frame from the server.
	Read(ctx context.Context) (StreamID, []byte, error)
	// Resize requests a TTY size change, if TTY is enabled.
	Resize(ctx context.Context, cols, rows int) error
	// StdinEOF indicates no more stdin will be sent.
	StdinEOF(ctx context.Context) error
	// ExitCode blocks until the server signals process exit and returns the code.
	ExitCode(ctx context.Context) (int, error)
	// Close closes the underlying connection for this session.
	Close() error
}

// OperationAPI starts exec operations using a specific transport (control or legacy endpoint).
type OperationAPI interface {
	StartExec(ctx context.Context, opts ExecOptions) (ExecSession, error)
}
