package sprites

import (
	"log/slog"
	"os"
	"sync/atomic"
)

var sdkDebug atomic.Bool

func init() {
	if v := os.Getenv("SPRITES_SDK_DEBUG"); v != "" && v != "0" && v != "false" {
		sdkDebug.Store(true)
	}
}

func dbg(msg string, args ...any) {
	if sdkDebug.Load() {
		slog.Default().Debug(msg, args...)
	}
}
