module github.com/sprite-env/client

go 1.24.4

require (
	github.com/sprite-env/lib v0.0.0
	github.com/sprite-env/packages/wsexec v0.0.0-00010101000000-000000000000
	golang.org/x/term v0.32.0
)

require (
	github.com/creack/pty v1.1.24 // indirect
	github.com/gorilla/websocket v1.5.3 // indirect
	golang.org/x/sys v0.33.0 // indirect
)

replace github.com/sprite-env/lib => ../lib

replace github.com/sprite-env/packages/wsexec => ../packages/wsexec
