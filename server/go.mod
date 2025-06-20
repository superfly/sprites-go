module spritectl

go 1.24.4

require github.com/mattn/go-sqlite3 v1.14.22 // indirect

require lib v0.0.0-00010101000000-000000000000

require (
	github.com/fly-dev-env/sprite-env/server/packages/juicefs v0.0.0-00010101000000-000000000000
	github.com/sprite-env/server/packages/supervisor v0.0.0-00010101000000-000000000000
)

replace lib => ../lib

replace github.com/fly-dev-env/sprite-env/server/packages/juicefs => ../packages/juicefs

replace github.com/sprite-env/server/packages/supervisor => ../packages/supervisor
