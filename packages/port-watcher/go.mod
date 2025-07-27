module github.com/superfly/sprite-env/packages/port-watcher

go 1.24.4

replace github.com/superfly/sprite-env/packages/container => ../container

replace github.com/superfly/sprite-env/packages/supervisor => ../supervisor

require github.com/superfly/sprite-env/packages/container v0.0.0-00010101000000-000000000000

require github.com/superfly/sprite-env/packages/supervisor v0.0.0 // indirect
