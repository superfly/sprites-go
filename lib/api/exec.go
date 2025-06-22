package api

// DockerExecCreateRequest represents the request to create an exec instance
type DockerExecCreateRequest struct {
	Cmd          []string `json:"Cmd"`
	AttachStdin  bool     `json:"AttachStdin,omitempty"`
	AttachStdout bool     `json:"AttachStdout,omitempty"`
	AttachStderr bool     `json:"AttachStderr,omitempty"`
	DetachKeys   string   `json:"DetachKeys,omitempty"`
	Tty          bool     `json:"Tty,omitempty"`
	Env          []string `json:"Env,omitempty"`
	WorkingDir   string   `json:"WorkingDir,omitempty"`
	User         string   `json:"User,omitempty"`
	Privileged   bool     `json:"Privileged,omitempty"`
}

// DockerExecCreateResponse represents the response from creating an exec instance
type DockerExecCreateResponse struct {
	Id string `json:"Id"`
}

// DockerExecStartRequest represents the request to start an exec instance
type DockerExecStartRequest struct {
	Detach bool `json:"Detach,omitempty"`
	Tty    bool `json:"Tty,omitempty"`
}

// DockerExecInspectResponse represents the response from inspecting an exec instance
type DockerExecInspectResponse struct {
	Id            string              `json:"Id"`
	Running       bool                `json:"Running"`
	ExitCode      int                 `json:"ExitCode"`
	ProcessConfig DockerProcessConfig `json:"ProcessConfig"`
	OpenStdin     bool                `json:"OpenStdin"`
	OpenStderr    bool                `json:"OpenStderr"`
	OpenStdout    bool                `json:"OpenStdout"`
	CanRemove     bool                `json:"CanRemove"`
	ContainerID   string              `json:"ContainerID"`
	DetachKeys    string              `json:"DetachKeys"`
	Pid           int                 `json:"Pid,omitempty"`
}

// DockerProcessConfig represents the process configuration
type DockerProcessConfig struct {
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
