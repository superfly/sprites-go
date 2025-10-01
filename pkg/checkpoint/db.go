package checkpoint

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

type SQLiteDB struct {
	db     *sql.DB
	dbPath string
	logger *slog.Logger
}

type SQLiteConfig struct {
	BaseDir string
	DBPath  string
	Logger  *slog.Logger
}

func NewSQLiteDB(cfg SQLiteConfig) (*SQLiteDB, error) {
	if cfg.Logger == nil {
		cfg.Logger = slog.New(slog.NewTextHandler(io.Discard, nil))
	}
	dbPath := cfg.DBPath
	if dbPath == "" {
		dbPath = filepath.Join(cfg.BaseDir, "checkpoints.db")
	}
	db, err := sql.Open("sqlite", dbPath)
	if err != nil {
		return nil, fmt.Errorf("open sqlite: %w", err)
	}
	if err := configureSQLite(db); err != nil {
		db.Close()
		return nil, err
	}
	s := &SQLiteDB{db: db, dbPath: dbPath, logger: cfg.Logger}
	if err := s.initialize(); err != nil {
		db.Close()
		return nil, err
	}
	return s, nil
}

func configureSQLite(db *sql.DB) error {
	pragmas := []string{
		"PRAGMA journal_mode=WAL",
		"PRAGMA synchronous=NORMAL",
		"PRAGMA cache_size=10000",
		"PRAGMA foreign_keys=ON",
		"PRAGMA busy_timeout=30000",
		"PRAGMA wal_autocheckpoint=1000",
	}
	for _, p := range pragmas {
		if _, err := db.Exec(p); err != nil {
			return fmt.Errorf("sqlite pragma %s: %w", p, err)
		}
	}
	return nil
}

func (s *SQLiteDB) initialize() error {
	createTable := `
CREATE TABLE IF NOT EXISTS sprite_checkpoints (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  path TEXT NOT NULL,
  parent_id INTEGER,
  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
  FOREIGN KEY (parent_id) REFERENCES sprite_checkpoints(id)
);`
	if _, err := s.db.Exec(createTable); err != nil {
		return fmt.Errorf("create table: %w", err)
	}
	var count int
	if err := s.db.QueryRow("SELECT COUNT(*) FROM sprite_checkpoints").Scan(&count); err != nil {
		return fmt.Errorf("count: %w", err)
	}
	if count == 0 {
		if _, err := s.db.Exec("INSERT INTO sprite_checkpoints (path, parent_id) VALUES (?, NULL)", "checkpoints/v0"); err != nil {
			return fmt.Errorf("seed v0: %w", err)
		}
		if _, err := s.db.Exec("INSERT INTO sprite_checkpoints (path, parent_id) VALUES (?, ?)", "active/", 1); err != nil {
			return fmt.Errorf("seed v1: %w", err)
		}
	}
	return nil
}

func (s *SQLiteDB) Close() error { return s.db.Close() }

type dbRecord struct {
	ID        int64
	Path      string
	ParentID  sql.NullInt64
	CreatedAt time.Time
}

// DB interface implementation

func (s *SQLiteDB) CreateCheckpoint(cloneFn func(src, dst string) error, renameFn func(src, dst string) error) (*Record, error) {
	maxRetries := 3
	baseDelay := 100 * time.Millisecond
	for retry := 0; retry < maxRetries; retry++ {
		if retry > 0 {
			delay := baseDelay * time.Duration(1<<retry)
			if delay > 5*time.Second {
				delay = 5 * time.Second
			}
			time.Sleep(delay)
		}
		rec, tempPath, err := s.createCheckpointAttempt(cloneFn)
		if err == nil && rec != nil {
			prev, err := s.GetCheckpointByID(rec.ID - 1)
			if err != nil {
				return nil, fmt.Errorf("get prev: %w", err)
			}
			if err := renameFn(tempPath, prev.Path); err != nil {
				return nil, fmt.Errorf("finalize rename: %w", err)
			}
			return rec, nil
		}
		if tempPath != "" {
			_ = renameFn(tempPath, "")
		}
		if err != nil && (strings.Contains(err.Error(), "database is locked") || strings.Contains(err.Error(), "database is busy") || strings.Contains(err.Error(), "(5)") || strings.Contains(err.Error(), "(6)") || strings.Contains(err.Error(), "(517)")) {
			if retry < maxRetries-1 {
				s.logger.Warn("Database locked, retrying checkpoint creation", "attempt", retry+2, "maxAttempts", maxRetries)
				continue
			}
		}
		if err != nil {
			return nil, err
		}
	}
	return nil, fmt.Errorf("failed to create checkpoint after retries")
}

func (s *SQLiteDB) createCheckpointAttempt(cloneFn func(src, dst string) error) (*Record, string, error) {
	tx, err := s.db.Begin()
	if err != nil {
		return nil, "", fmt.Errorf("begin: %w", err)
	}
	defer tx.Rollback()
	var currentID int64
	var currentPath string
	row := tx.QueryRow("SELECT id, path FROM sprite_checkpoints ORDER BY id DESC LIMIT 1")
	if err := row.Scan(&currentID, &currentPath); err != nil {
		return nil, "", fmt.Errorf("scan current: %w", err)
	}
	cpPath := fmt.Sprintf("checkpoints/v%d", currentID-1)
	tempPath := fmt.Sprintf("checkpoints/v%d.in-progress", currentID-1)
	if err := cloneFn("active/", tempPath); err != nil {
		return nil, tempPath, fmt.Errorf("clone: %w", err)
	}
	if _, err := tx.Exec("UPDATE sprite_checkpoints SET path = ? WHERE id = ?", cpPath, currentID); err != nil {
		return nil, tempPath, fmt.Errorf("update path: %w", err)
	}
	res, err := tx.Exec("INSERT INTO sprite_checkpoints (path, parent_id) VALUES (?, ?)", "active/", currentID)
	if err != nil {
		return nil, tempPath, fmt.Errorf("insert: %w", err)
	}
	newID, err := res.LastInsertId()
	if err != nil {
		return nil, tempPath, fmt.Errorf("lastInsertId: %w", err)
	}
	if err := tx.Commit(); err != nil {
		return nil, tempPath, fmt.Errorf("commit: %w", err)
	}
	rec, err := s.GetCheckpointByID(newID)
	return rec, tempPath, err
}

func (s *SQLiteDB) GetCheckpointByID(id int64) (*Record, error) {
	var r dbRecord
	row := s.db.QueryRow("SELECT id, path, parent_id, created_at FROM sprite_checkpoints WHERE id = ?", id)
	if err := row.Scan(&r.ID, &r.Path, &r.ParentID, &r.CreatedAt); err != nil {
		return nil, fmt.Errorf("get by id: %w", err)
	}
	return &Record{ID: r.ID, Path: r.Path, CreatedAt: r.CreatedAt}, nil
}

func (s *SQLiteDB) FindCheckpointByPath(path string) (*Record, error) {
	var r dbRecord
	row := s.db.QueryRow("SELECT id, path, parent_id, created_at FROM sprite_checkpoints WHERE path = ?", path)
	if err := row.Scan(&r.ID, &r.Path, &r.ParentID, &r.CreatedAt); err != nil {
		if err == sql.ErrNoRows {
			return nil, fmt.Errorf("checkpoint with path %s not found", path)
		}
		return nil, fmt.Errorf("find by path: %w", err)
	}
	return &Record{ID: r.ID, Path: r.Path, CreatedAt: r.CreatedAt}, nil
}

// ListAllCheckpoints opens the DB from the provided config and returns the latest record
// and all checkpoint records (excluding the active row), newest first.
func ListAllCheckpoints(cfg SQLiteConfig) (*Record, []Record, error) {
	db, err := NewSQLiteDB(cfg)
	if err != nil {
		return nil, nil, err
	}
	defer db.Close()

	latest, err := db.GetLatest()
	if err != nil {
		return nil, nil, err
	}
	records, err := db.ListAll()
	if err != nil {
		return nil, nil, err
	}
	return latest, records, nil
}

// ListAll returns all checkpoint records (excluding the active row), newest first
func (s *SQLiteDB) ListAll() ([]Record, error) {
	rows, err := s.db.Query(`
        SELECT id, path, parent_id, created_at
        FROM sprite_checkpoints
        WHERE path LIKE 'checkpoints/%'
        ORDER BY id DESC
    `)
	if err != nil {
		return nil, fmt.Errorf("list all: %w", err)
	}
	defer rows.Close()

	var out []Record
	for rows.Next() {
		var r dbRecord
		if err := rows.Scan(&r.ID, &r.Path, &r.ParentID, &r.CreatedAt); err != nil {
			return nil, fmt.Errorf("scan: %w", err)
		}
		out = append(out, Record{ID: r.ID, Path: r.Path, CreatedAt: r.CreatedAt})
	}
	if err := rows.Err(); err != nil {
		return nil, fmt.Errorf("iterate: %w", err)
	}
	return out, nil
}

// GetLatest returns the newest checkpoint record (the row with highest id)
func (s *SQLiteDB) GetLatest() (*Record, error) {
	var r dbRecord
	row := s.db.QueryRow(`
        SELECT id, path, parent_id, created_at
        FROM sprite_checkpoints
        ORDER BY id DESC
        LIMIT 1
    `)
	if err := row.Scan(&r.ID, &r.Path, &r.ParentID, &r.CreatedAt); err != nil {
		return nil, fmt.Errorf("latest: %w", err)
	}
	return &Record{ID: r.ID, Path: r.Path, CreatedAt: r.CreatedAt}, nil
}
