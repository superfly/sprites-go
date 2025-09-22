package services

import (
	"database/sql"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"

	_ "modernc.org/sqlite"
)

type DB struct {
	db *sql.DB
}

func NewDB(dataDir string) (*DB, error) {
	// Ensure the data directory exists
	if err := os.MkdirAll(dataDir, 0755); err != nil {
		return nil, fmt.Errorf("failed to create data directory: %w", err)
	}

	dbPath := filepath.Join(dataDir, "services.db")
	fmt.Println("Opening services database", dbPath)
	db, err := sql.Open("sqlite", dbPath)
	if err != nil {
		return nil, fmt.Errorf("failed to open database: %w", err)
	}

	if err := createTables(db); err != nil {
		db.Close()
		return nil, fmt.Errorf("failed to create tables: %w", err)
	}

	return &DB{db: db}, nil
}

func (d *DB) Close() error {
	return d.db.Close()
}

func createTables(db *sql.DB) error {
	queries := []string{
		`CREATE TABLE IF NOT EXISTS services (
			name TEXT PRIMARY KEY,
			cmd TEXT NOT NULL,
			args TEXT NOT NULL
		);`,
		`CREATE TABLE IF NOT EXISTS service_dependencies (
			service_name TEXT NOT NULL,
			dependency_name TEXT NOT NULL,
			PRIMARY KEY (service_name, dependency_name),
			FOREIGN KEY (service_name) REFERENCES services(name) ON DELETE CASCADE,
			FOREIGN KEY (dependency_name) REFERENCES services(name)
		);`,
	}

	for _, query := range queries {
		if _, err := db.Exec(query); err != nil {
			return err
		}
	}
	return nil
}

func (d *DB) CreateService(s *Service) error {
	args, err := json.Marshal(s.Args)
	if err != nil {
		return fmt.Errorf("failed to marshal args: %w", err)
	}

	// Use a transaction to ensure atomicity
	tx, err := d.db.Begin()
	if err != nil {
		return fmt.Errorf("failed to begin transaction: %w", err)
	}
	defer tx.Rollback()

	// Insert the service
	query := `INSERT INTO services (name, cmd, args) VALUES (?, ?, ?)`
	_, err = tx.Exec(query, s.Name, s.Cmd, string(args))
	if err != nil {
		// Get the database path for debugging
		var dbPath string
		d.db.QueryRow("SELECT file FROM pragma_database_list WHERE name='main'").Scan(&dbPath)
		return fmt.Errorf("failed to insert service (db: %s): %w", dbPath, err)
	}

	// Insert dependencies
	if len(s.Needs) > 0 {
		depQuery := `INSERT INTO service_dependencies (service_name, dependency_name) VALUES (?, ?)`
		for _, dep := range s.Needs {
			if _, err := tx.Exec(depQuery, s.Name, dep); err != nil {
				return fmt.Errorf("failed to insert dependency %s: %w", dep, err)
			}
		}
	}

	if err := tx.Commit(); err != nil {
		return fmt.Errorf("failed to commit transaction: %w", err)
	}

	return nil
}

func (d *DB) GetService(name string) (*Service, error) {
	// First get the service basic info
	query := `SELECT cmd, args FROM services WHERE name = ?`

	var cmd, argsJSON string
	err := d.db.QueryRow(query, name).Scan(&cmd, &argsJSON)
	if err == sql.ErrNoRows {
		return nil, fmt.Errorf("service not found: %s", name)
	}
	if err != nil {
		return nil, fmt.Errorf("failed to query service: %w", err)
	}

	var args []string
	if err := json.Unmarshal([]byte(argsJSON), &args); err != nil {
		return nil, fmt.Errorf("failed to unmarshal args: %w", err)
	}

	// Get dependencies
	depQuery := `SELECT dependency_name FROM service_dependencies WHERE service_name = ?`
	rows, err := d.db.Query(depQuery, name)
	if err != nil {
		return nil, fmt.Errorf("failed to query dependencies: %w", err)
	}
	defer rows.Close()

	var needs []string
	for rows.Next() {
		var dep string
		if err := rows.Scan(&dep); err != nil {
			return nil, fmt.Errorf("failed to scan dependency: %w", err)
		}
		needs = append(needs, dep)
	}

	return &Service{
		Name:  name,
		Cmd:   cmd,
		Args:  args,
		Needs: needs,
	}, nil
}

func (d *DB) ListServices() ([]*Service, error) {
	// Get all services
	query := `SELECT name, cmd, args FROM services ORDER BY name`

	rows, err := d.db.Query(query)
	if err != nil {
		return nil, fmt.Errorf("failed to query services: %w", err)
	}
	defer rows.Close()

	// Build service map
	serviceMap := make(map[string]*Service)
	var services []*Service

	for rows.Next() {
		var name, cmd, argsJSON string
		if err := rows.Scan(&name, &cmd, &argsJSON); err != nil {
			return nil, fmt.Errorf("failed to scan row: %w", err)
		}

		var args []string
		if err := json.Unmarshal([]byte(argsJSON), &args); err != nil {
			return nil, fmt.Errorf("failed to unmarshal args: %w", err)
		}

		svc := &Service{
			Name:  name,
			Cmd:   cmd,
			Args:  args,
			Needs: []string{},
		}
		serviceMap[name] = svc
		services = append(services, svc)
	}

	// Get all dependencies
	depQuery := `SELECT service_name, dependency_name FROM service_dependencies`
	depRows, err := d.db.Query(depQuery)
	if err != nil {
		return nil, fmt.Errorf("failed to query dependencies: %w", err)
	}
	defer depRows.Close()

	for depRows.Next() {
		var serviceName, depName string
		if err := depRows.Scan(&serviceName, &depName); err != nil {
			return nil, fmt.Errorf("failed to scan dependency: %w", err)
		}

		if svc, exists := serviceMap[serviceName]; exists {
			svc.Needs = append(svc.Needs, depName)
		}
	}

	return services, nil
}

func (d *DB) DeleteService(name string) error {
	query := `DELETE FROM services WHERE name = ?`
	result, err := d.db.Exec(query, name)
	if err != nil {
		return fmt.Errorf("failed to delete service: %w", err)
	}

	rows, err := result.RowsAffected()
	if err != nil {
		return fmt.Errorf("failed to get rows affected: %w", err)
	}
	if rows == 0 {
		return fmt.Errorf("service not found: %s", name)
	}

	return nil
}
