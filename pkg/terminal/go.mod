module github.com/superfly/sprite-env/pkg/terminal

go 1.24.4

require (
	github.com/creack/pty v1.1.21
	github.com/superfly/sprite-env/packages/container v0.0.0
)

require (
	github.com/gorilla/websocket v1.5.0 // indirect
	github.com/sprite-env/packages/supervisor v0.0.0 // indirect
)

replace github.com/superfly/sprite-env/packages/container => ../../packages/container

replace github.com/sprite-env/packages/supervisor => ../../packages/supervisor
