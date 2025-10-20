package sprites

import (
	"log/slog"
	"os"
)

var sdkLogger *slog.Logger

func init() {
	// Default logger: error level to stderr so debug logs are silent by default
	sdkLogger = slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{Level: slog.LevelError}))
	// Back-compat: if SPRITES_SDK_DEBUG is set truthy, elevate to debug level
	if v := os.Getenv("SPRITES_SDK_DEBUG"); v != "" && v != "0" && v != "false" {
		sdkLogger = slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{Level: slog.LevelDebug}))
	}
}

// SetLogger allows applications to override the SDK logger.
// Provide a slog.Logger configured with your desired handler and level.
func SetLogger(l *slog.Logger) {
	if l == nil {
		return
	}
	sdkLogger = l
}

func dbg(msg string, args ...any) {
	// Always log at debug level; visibility controlled by logger's level.
	sdkLogger.Debug(msg, args...)
}

// spritesDbg is exported to subpackages via go import alias to avoid import cycles.
// Internal packages in this module may call spritesDbg(...) for consistent debug logging.
func spritesDbg(msg string, args ...any) { dbg(msg, args...) }

// LogDebug is an exported helper for subpackages (e.g., controlapi/endpointapi)
// to write debug logs through the SDK's configured logger without importing
// an unexported symbol.
func LogDebug(msg string, args ...any) { sdkLogger.Debug(msg, args...) }
