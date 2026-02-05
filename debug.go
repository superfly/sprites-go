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

// SetDebug enables or disables SDK debug logging.
// When enabled, debug messages are written via slog.Default().
// This allows the calling application to control SDK debug output
// programmatically (e.g., when a CLI debug flag is set).
func SetDebug(enabled bool) {
	sdkDebug.Store(enabled)
}
