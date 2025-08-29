package juicefs

import (
	"database/sql"
	"fmt"
	"io"
	"log/slog"
	"path/filepath"
	"strings"
	"time"

	_ "modernc.org/sqlite"
)

// configureSQLite applies optimal configuration for SQLite
func configureSQLite(db *sql.DB) error {
	pragmas := []string{
		"PRAGMA journal_mode=WAL",
		"PRAGMA synchronous=NORMAL",
		"PRAGMA cache_size=10000",
		"PRAGMA foreign_keys=ON",
		"PRAGMA busy_timeout=30000",
		"PRAGMA wal_autocheckpoint=1000",
	}

	for _, pragma := range pragmas {
		if _, err := db.Exec(pragma); err != nil {
			return fmt.Errorf("failed to execute %s: %w", pragma, err)
		}
	}

	return nil
}

// CheckpointRecord represents a checkpoint entry in the database
type CheckpointRecord struct {
	ID        int64
	Path      string
	ParentID  sql.NullInt64
	CreatedAt time.Time
}

// CheckpointDBConfig contains configuration for CheckpointDB
type CheckpointDBConfig struct {
	// BaseDir is the base directory where the database file will be stored
	BaseDir string
	// DBPath is an optional custom path for the database file
	// If empty, defaults to {BaseDir}/checkpoints.db
	DBPath string
	// Logger for logging operations
	Logger *slog.Logger
}

// CheckpointDB manages checkpoint records in SQLite
type CheckpointDB struct {
	db     *sql.DB
	dbPath string
	logger *slog.Logger
}

// NewCheckpointDB creates a new checkpoint database manager
func NewCheckpointDB(config CheckpointDBConfig) (*CheckpointDB, error) {
	// Create a no-op logger if none provided
	if config.Logger == nil {
		config.Logger = slog.New(slog.NewTextHandler(io.Discard, nil))
	}

	// Determine database path
	var dbPath string
	if config.DBPath != "" {
		dbPath = config.DBPath
	} else {
		dbPath = filepath.Join(config.BaseDir, "checkpoints.db")
	}

	db, err := sql.Open("sqlite", dbPath)
	if err != nil {
		return nil, fmt.Errorf("failed to open checkpoint database: %w", err)
	}

	// Configure SQLite for better performance and memory usage
	if err := configureSQLite(db); err != nil {
		db.Close()
		return nil, fmt.Errorf("failed to configure SQLite: %w", err)
	}

	cdb := &CheckpointDB{
		db:     db,
		dbPath: dbPath,
		logger: config.Logger,
	}

	if err := cdb.initialize(); err != nil {
		db.Close()
		return nil, err
	}

	return cdb, nil
}

// initialize creates the checkpoint table and initial v0 record if needed
func (c *CheckpointDB) initialize() error {
	// Create the sprite_checkpoints table
	createTableSQL := `
	CREATE TABLE IF NOT EXISTS sprite_checkpoints (
		id INTEGER PRIMARY KEY AUTOINCREMENT,
		path TEXT NOT NULL,
		parent_id INTEGER,
		created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
		FOREIGN KEY (parent_id) REFERENCES sprite_checkpoints(id)
	);`

	if _, err := c.db.Exec(createTableSQL); err != nil {
		return fmt.Errorf("failed to create sprite_checkpoints table: %w", err)
	}

	// Check if we need to create the initial records
	var count int
	if err := c.db.QueryRow("SELECT COUNT(*) FROM sprite_checkpoints").Scan(&count); err != nil {
		return fmt.Errorf("failed to check checkpoint count: %w", err)
	}

	if count == 0 {
		// Insert the initial v0 record pointing to checkpoints/v0/
		if _, err := c.db.Exec("INSERT INTO sprite_checkpoints (path, parent_id) VALUES (?, NULL)", "checkpoints/v0"); err != nil {
			return fmt.Errorf("failed to create initial v0 checkpoint record: %w", err)
		}

		// Insert the v1 record pointing to active/ with parent_id of 1 (the v0 record)
		if _, err := c.db.Exec("INSERT INTO sprite_checkpoints (path, parent_id) VALUES (?, ?)", "active/", 1); err != nil {
			return fmt.Errorf("failed to create initial v1 checkpoint record: %w", err)
		}
	}

	return nil
}

// GetLatestCheckpoint returns the most recent checkpoint record
func (c *CheckpointDB) GetLatestCheckpoint() (*CheckpointRecord, error) {
	var record CheckpointRecord

	row := c.db.QueryRow(`
		SELECT id, path, parent_id, created_at 
		FROM sprite_checkpoints 
		ORDER BY id DESC 
		LIMIT 1
	`)

	err := row.Scan(&record.ID, &record.Path, &record.ParentID, &record.CreatedAt)
	if err != nil {
		return nil, fmt.Errorf("failed to get latest checkpoint: %w", err)
	}

	return &record, nil
}

// GetCheckpointByID returns a checkpoint record by ID
func (c *CheckpointDB) GetCheckpointByID(id int64) (*CheckpointRecord, error) {
	var record CheckpointRecord

	row := c.db.QueryRow(`
		SELECT id, path, parent_id, created_at 
		FROM sprite_checkpoints 
		WHERE id = ?
	`, id)

	err := row.Scan(&record.ID, &record.Path, &record.ParentID, &record.CreatedAt)
	if err != nil {
		return nil, fmt.Errorf("failed to get checkpoint %d: %w", id, err)
	}

	return &record, nil
}

// CreateCheckpoint performs the transactional checkpoint operation
func (c *CheckpointDB) CreateCheckpoint(cloneFn func(src, dst string) error, renameFn func(src, dst string) error) (*CheckpointRecord, error) {
	// Retry logic for database locks
	maxRetries := 3
	baseDelay := 100 * time.Millisecond

	for retry := 0; retry < maxRetries; retry++ {
		if retry > 0 {
			// Exponential backoff with jitter
			delay := baseDelay * time.Duration(1<<retry)
			if delay > 5*time.Second {
				delay = 5 * time.Second
			}
			time.Sleep(delay)
		}

		record, tempPath, err := c.createCheckpointAttempt(cloneFn)
		if err == nil && record != nil {
			// Transaction succeeded, now rename the temporary directory to final location
			// The final path is the path of the PREVIOUS record (which now contains the checkpoint)
			// We need to get the checkpoint path that was stored in the database
			prevRecord, err := c.GetCheckpointByID(record.ID - 1)
			if err != nil {
				return nil, fmt.Errorf("failed to get previous checkpoint record: %w", err)
			}
			finalPath := prevRecord.Path

			if err := renameFn(tempPath, finalPath); err != nil {
				return nil, fmt.Errorf("failed to rename checkpoint directory from %s to %s: %w", tempPath, finalPath, err)
			}
			return record, nil
		}

		// Clean up the temporary directory if it exists
		if tempPath != "" {
			// Use renameFn with empty destination to signal cleanup
			_ = renameFn(tempPath, "")
		}

		// Check if it's a database lock error (SQLITE_BUSY = 5, SQLITE_LOCKED = 6)
		if strings.Contains(err.Error(), "database is locked") ||
			strings.Contains(err.Error(), "database is busy") ||
			strings.Contains(err.Error(), "(5)") || strings.Contains(err.Error(), "(6)") ||
			strings.Contains(err.Error(), "(517)") { // SQLITE_BUSY_SNAPSHOT
			if retry < maxRetries-1 {
				c.logger.Warn("Database locked, retrying checkpoint creation", "attempt", retry+2, "maxAttempts", maxRetries)
				continue
			}
		}

		return nil, err
	}

	return nil, fmt.Errorf("failed to create checkpoint after %d attempts", maxRetries)
}

// createCheckpointAttempt performs a single attempt at creating a checkpoint
// Returns the record, checkpoint path (for cleanup), and error
func (c *CheckpointDB) createCheckpointAttempt(cloneFn func(src, dst string) error) (*CheckpointRecord, string, error) {
	tx, err := c.db.Begin()
	if err != nil {
		return nil, "", fmt.Errorf("failed to begin transaction: %w", err)
	}
	defer tx.Rollback()

	// Get the current latest checkpoint
	var currentID int64
	var currentPath string
	row := tx.QueryRow(`
		SELECT id, path 
		FROM sprite_checkpoints 
		ORDER BY id DESC 
		LIMIT 1
	`)
	if err := row.Scan(&currentID, &currentPath); err != nil {
		return nil, "", fmt.Errorf("failed to get current checkpoint: %w", err)
	}

	// The new checkpoint directory will be v{currentID-1} since IDs start at 1
	checkpointPath := fmt.Sprintf("checkpoints/v%d", currentID-1)
	// Use a temporary in-progress path during the operation
	tempPath := fmt.Sprintf("checkpoints/v%d.in-progress", currentID-1)

	// Perform the clone operation to the temporary path
	if err := cloneFn("active/", tempPath); err != nil {
		return nil, tempPath, fmt.Errorf("clone operation failed: %w", err)
	}

	// Update the current checkpoint's path
	if _, err := tx.Exec("UPDATE sprite_checkpoints SET path = ? WHERE id = ?", checkpointPath, currentID); err != nil {
		return nil, tempPath, fmt.Errorf("failed to update checkpoint path: %w", err)
	}

	// Insert new checkpoint record pointing to active/ with parent_id of the previous checkpoint
	result, err := tx.Exec("INSERT INTO sprite_checkpoints (path, parent_id) VALUES (?, ?)", "active/", currentID)
	if err != nil {
		return nil, tempPath, fmt.Errorf("failed to insert new checkpoint: %w", err)
	}

	newID, err := result.LastInsertId()
	if err != nil {
		return nil, tempPath, fmt.Errorf("failed to get new checkpoint ID: %w", err)
	}

	// Commit the transaction
	if err := tx.Commit(); err != nil {
		return nil, tempPath, fmt.Errorf("failed to commit transaction: %w", err)
	}

	// Return the new checkpoint record and the paths for the rename operation
	record, err := c.GetCheckpointByID(newID)
	// Return both the temp path and final path so the caller can rename
	return record, tempPath, err
}

// FindCheckpointByPath finds a checkpoint by its path (e.g., "checkpoints/v3")
func (c *CheckpointDB) FindCheckpointByPath(path string) (*CheckpointRecord, error) {
	var record CheckpointRecord

	row := c.db.QueryRow(`
		SELECT id, path, parent_id, created_at 
		FROM sprite_checkpoints 
		WHERE path = ?
	`, path)

	err := row.Scan(&record.ID, &record.Path, &record.ParentID, &record.CreatedAt)
	if err != nil {
		if err == sql.ErrNoRows {
			return nil, fmt.Errorf("checkpoint with path %s not found", path)
		}
		return nil, fmt.Errorf("failed to find checkpoint: %w", err)
	}

	return &record, nil
}

// Close closes the database connection
func (c *CheckpointDB) Close() error {
	return c.db.Close()
}
