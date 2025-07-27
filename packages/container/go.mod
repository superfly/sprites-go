module github.com/superfly/sprite-env/packages/container

go 1.24.4

require (
	github.com/creack/pty v1.1.24
	github.com/superfly/sprite-env/packages/supervisor v0.0.0
)

replace github.com/superfly/sprite-env/packages/supervisor => ../supervisor
