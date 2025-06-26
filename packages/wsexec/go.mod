module github.com/sprite-env/packages/wsexec

go 1.24.4

require (
	github.com/creack/pty v1.1.24
	github.com/superfly/sprite-env/packages/container v0.0.0
	github.com/gorilla/websocket v1.5.3
)

replace github.com/superfly/sprite-env/packages/container => ../container
