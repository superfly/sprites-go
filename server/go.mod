module github.com/sprite-env/server

go 1.24.4

require (
	github.com/aws/aws-sdk-go-v2 v1.36.5 // indirect
	github.com/aws/aws-sdk-go-v2/aws/protocol/eventstream v1.6.11 // indirect
	github.com/aws/aws-sdk-go-v2/credentials v1.16.12 // indirect
	github.com/aws/aws-sdk-go-v2/internal/configsources v1.3.36 // indirect
	github.com/aws/aws-sdk-go-v2/internal/endpoints/v2 v2.6.36 // indirect
	github.com/aws/aws-sdk-go-v2/internal/v4a v1.3.36 // indirect
	github.com/aws/aws-sdk-go-v2/service/internal/accept-encoding v1.12.4 // indirect
	github.com/aws/aws-sdk-go-v2/service/internal/checksum v1.7.4 // indirect
	github.com/aws/aws-sdk-go-v2/service/internal/presigned-url v1.12.17 // indirect
	github.com/aws/aws-sdk-go-v2/service/internal/s3shared v1.18.17 // indirect
	github.com/aws/aws-sdk-go-v2/service/s3 v1.81.0 // indirect
	github.com/aws/smithy-go v1.22.4 // indirect
	github.com/creack/pty v1.1.24 // indirect
	github.com/dustin/go-humanize v1.0.1 // indirect
	github.com/fsnotify/fsnotify v1.7.0 // indirect
	github.com/google/uuid v1.6.0 // indirect
	github.com/gorilla/websocket v1.5.3 // indirect
	github.com/hashicorp/golang-lru/v2 v2.0.7 // indirect
	github.com/mattn/go-isatty v0.0.20 // indirect
	github.com/mattn/go-sqlite3 v1.14.28 // indirect
	github.com/ncruces/go-strftime v0.1.9 // indirect
	github.com/remyoudompheng/bigfft v0.0.0-20230129092748-24d4a6f8daec // indirect
	golang.org/x/sys v0.33.0 // indirect
	modernc.org/gc/v3 v3.0.0-20240107210532-573471604cb6 // indirect
	modernc.org/libc v1.49.3 // indirect
	modernc.org/mathutil v1.6.0 // indirect
	modernc.org/memory v1.8.0 // indirect
	modernc.org/sqlite v1.29.8 // indirect
	modernc.org/strutil v1.2.0 // indirect
	modernc.org/token v1.1.0 // indirect
)

require github.com/sprite-env/lib v0.0.0

require (
	github.com/sprite-env/packages/juicefs v0.0.0-00010101000000-000000000000
	github.com/sprite-env/packages/leaser v0.0.0-00010101000000-000000000000
	github.com/sprite-env/packages/supervisor v0.0.0
	github.com/sprite-env/packages/wsexec v0.0.0-00010101000000-000000000000
	github.com/superfly/sprite-env/packages/container v0.0.0
	github.com/superfly/sprite-env/packages/port-watcher v0.0.0-00010101000000-000000000000
	github.com/superfly/sprite-env/pkg/terminal v0.0.0-00010101000000-000000000000
)

replace github.com/sprite-env/lib => ../lib

replace github.com/sprite-env/packages/juicefs => ../packages/juicefs

replace github.com/sprite-env/packages/leaser => ../packages/leaser

replace github.com/sprite-env/packages/supervisor => ../packages/supervisor

replace github.com/sprite-env/packages/wsexec => ../packages/wsexec

replace github.com/superfly/sprite-env/packages/container => ../packages/container

replace github.com/superfly/sprite-env/packages/port-watcher => ../packages/port-watcher

replace github.com/superfly/sprite-env/pkg/terminal => ../pkg/terminal
