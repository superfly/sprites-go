package lib

import (
	"log"
	"os"
)

var (
	debugLogger *log.Logger
)

func init() {
	// Create a debug logger that writes to stdout
	debugLogger = log.New(os.Stdout, "", 0)
}

// debugLog writes a debug message to stdout
func debugLog(format string, v ...interface{}) {
	debugLogger.Printf("DEBUG: "+format, v...)
}
