module github.com/sprite-env/server

go 1.24.4

require (
	github.com/creack/pty v1.1.24 // indirect
	github.com/gorilla/websocket v1.5.3 // indirect
	github.com/mattn/go-sqlite3 v1.14.22 // indirect
	golang.org/x/term v0.32.0 // indirect
)

require github.com/sprite-env/lib v0.0.0

require (
	github.com/sprite-env/packages/juicefs v0.0.0-00010101000000-000000000000
	github.com/sprite-env/packages/supervisor v0.0.0-00010101000000-000000000000
	github.com/sprite-env/packages/wsexec v0.0.0-00010101000000-000000000000
)

replace github.com/sprite-env/lib => ../lib

replace github.com/sprite-env/packages/juicefs => ../packages/juicefs

replace github.com/sprite-env/packages/supervisor => ../packages/supervisor

replace github.com/sprite-env/packages/wsexec => ../packages/wsexec
