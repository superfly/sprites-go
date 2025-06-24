package api

// ExecCreateRequest represents the request to create an exec instance
type ExecCreateRequest struct {
	Cmd          []string `json:"Cmd"`
	AttachStdout bool     `json:"AttachStdout,omitempty"`
	AttachStderr bool     `json:"AttachStderr,omitempty"`
	DetachKeys   string   `json:"DetachKeys,omitempty"`
	Tty          bool     `json:"Tty,omitempty"`
	Env          []string `json:"Env,omitempty"`
	WorkingDir   string   `json:"WorkingDir,omitempty"`
	User         string   `json:"User,omitempty"`
	Privileged   bool     `json:"Privileged,omitempty"`
}

// ExecCreateResponse represents the response from creating an exec instance
type ExecCreateResponse struct {
	Id string `json:"Id"`
}

// ExecStartRequest represents the request to start an exec instance
type ExecStartRequest struct {
	Detach bool `json:"Detach,omitempty"`
	Tty    bool `json:"Tty,omitempty"`
}

// ExecInspectResponse represents the response from inspecting an exec instance
type ExecInspectResponse struct {
	Id            string        `json:"Id"`
	Running       bool          `json:"Running"`
	ExitCode      int           `json:"ExitCode"`
	ProcessConfig ProcessConfig `json:"ProcessConfig"`
	OpenStdin     bool          `json:"OpenStdin"`
	OpenStderr    bool          `json:"OpenStderr"`
	OpenStdout    bool          `json:"OpenStdout"`
	CanRemove     bool          `json:"CanRemove"`
	ContainerID   string        `json:"ContainerID"`
	DetachKeys    string        `json:"DetachKeys"`
	Pid           int           `json:"Pid,omitempty"`
}

// ProcessConfig represents the process configuration
type ProcessConfig struct {
	Entrypoint string   `json:"entrypoint"`
	Arguments  []string `json:"arguments"`
	Privileged bool     `json:"privileged"`
	Tty        bool     `json:"tty"`
	User       string   `json:"user,omitempty"`
}

// ExecRequest represents the request payload for the /exec endpoint (legacy)
type ExecRequest struct {
	Command []string  `json:"command"`
	Timeout *Duration `json:"timeout,omitempty"`
	TTY     bool      `json:"tty,omitempty"`
}
