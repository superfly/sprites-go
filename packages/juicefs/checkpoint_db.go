package juicefs

import (
	"database/sql"
	"fmt"
	"path/filepath"
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
		"PRAGMA busy_timeout=5000",
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

// CheckpointDB manages checkpoint records in SQLite
type CheckpointDB struct {
	db     *sql.DB
	dbPath string
}

// NewCheckpointDB creates a new checkpoint database manager in the baseDir (outside JuiceFS partition)
func NewCheckpointDB(baseDir string) (*CheckpointDB, error) {
	// Use a separate sprite-checkpoints.db file in baseDir (not inside the JuiceFS partition)
	dbPath := filepath.Join(baseDir, "sprite-checkpoints.db")

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

	// Check if we need to create the initial v0 record
	var count int
	if err := c.db.QueryRow("SELECT COUNT(*) FROM sprite_checkpoints").Scan(&count); err != nil {
		return fmt.Errorf("failed to check checkpoint count: %w", err)
	}

	if count == 0 {
		// Insert the initial v0 record pointing to active/
		if _, err := c.db.Exec("INSERT INTO sprite_checkpoints (path, parent_id) VALUES (?, NULL)", "active/"); err != nil {
			return fmt.Errorf("failed to create initial checkpoint record: %w", err)
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
func (c *CheckpointDB) CreateCheckpoint(cloneFn func(src, dst string) error) (*CheckpointRecord, error) {
	tx, err := c.db.Begin()
	if err != nil {
		return nil, fmt.Errorf("failed to begin transaction: %w", err)
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
		return nil, fmt.Errorf("failed to get current checkpoint: %w", err)
	}

	// The new checkpoint directory will be v{currentID-1} since IDs start at 1
	checkpointPath := fmt.Sprintf("checkpoints/v%d", currentID-1)

	// Perform the clone operation
	if err := cloneFn("active/", checkpointPath); err != nil {
		return nil, fmt.Errorf("clone operation failed: %w", err)
	}

	// Update the current checkpoint's path
	if _, err := tx.Exec("UPDATE sprite_checkpoints SET path = ? WHERE id = ?", checkpointPath, currentID); err != nil {
		return nil, fmt.Errorf("failed to update checkpoint path: %w", err)
	}

	// Insert new checkpoint record pointing to active/ with parent_id of the previous checkpoint
	result, err := tx.Exec("INSERT INTO sprite_checkpoints (path, parent_id) VALUES (?, ?)", "active/", currentID)
	if err != nil {
		return nil, fmt.Errorf("failed to insert new checkpoint: %w", err)
	}

	newID, err := result.LastInsertId()
	if err != nil {
		return nil, fmt.Errorf("failed to get new checkpoint ID: %w", err)
	}

	// Commit the transaction
	if err := tx.Commit(); err != nil {
		return nil, fmt.Errorf("failed to commit transaction: %w", err)
	}

	// Return the new checkpoint record
	return c.GetCheckpointByID(newID)
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
