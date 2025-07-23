module github.com/superfly/sprite-env/cmd/sprite-run

go 1.24.4

require (
	github.com/superfly/sprite-env/pkg/terminal v0.0.0
	github.com/superfly/sprite-env/pkg/sync v0.0.0-00010101000000-000000000000
	github.com/urfave/cli/v2 v2.27.5
	golang.org/x/term v0.32.0
)

require (
	github.com/cpuguy83/go-md2man/v2 v2.0.5 // indirect
	github.com/creack/pty v1.1.24 // indirect
	github.com/google/uuid v1.6.0 // indirect
	github.com/gorilla/websocket v1.5.3 // indirect
	github.com/mattn/go-sqlite3 v1.14.28 // indirect
	github.com/russross/blackfriday/v2 v2.1.0 // indirect
	github.com/sprite-env/packages/supervisor v0.0.0 // indirect
	github.com/superfly/sprite-env/packages/container v0.0.0 // indirect
	github.com/xrash/smetrics v0.0.0-20240521201337-686a1a2994c1 // indirect
	golang.org/x/sys v0.33.0 // indirect
)

replace github.com/superfly/sprite-env/pkg/terminal => ../../pkg/terminal

replace github.com/superfly/sprite-env/packages/container => ../../packages/container

replace github.com/sprite-env/packages/supervisor => ../../packages/supervisor

replace github.com/superfly/sprite-env/pkg/sync => ../../pkg/sync
