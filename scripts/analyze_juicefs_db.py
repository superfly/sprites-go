#!/usr/bin/env python3
"""
Analyze JuiceFS meta database to understand checkpoint structure
and calculate usage statistics.
"""

import sqlite3
import json
import sys
import os
from datetime import datetime
from pathlib import Path

def connect_db(db_path):
    """Connect to SQLite database"""
    if not os.path.exists(db_path):
        print(f"Error: Database {db_path} not found")
        sys.exit(1)
    
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    return conn

def list_tables(conn):
    """List all tables in the database"""
    cursor = conn.cursor()
    cursor.execute("SELECT name FROM sqlite_master WHERE type='table'")
    tables = cursor.fetchall()
    return [t['name'] for t in tables]

def analyze_checkpoints_table(conn):
    """Analyze checkpoints table structure and contents"""
    cursor = conn.cursor()
    
    # Check if checkpoints table exists
    cursor.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='checkpoints'")
    if not cursor.fetchone():
        print("No 'checkpoints' table found")
        return None
    
    # Get table schema
    cursor.execute("PRAGMA table_info(checkpoints)")
    columns = cursor.fetchall()
    print("\nCheckpoints table schema:")
    for col in columns:
        print(f"  - {col['name']}: {col['type']}")
    
    # Get checkpoint data
    cursor.execute("SELECT * FROM checkpoints ORDER BY id DESC")
    checkpoints = cursor.fetchall()
    
    print(f"\nFound {len(checkpoints)} checkpoints:")
    checkpoint_data = []
    for cp in checkpoints:
        cp_dict = dict(cp)
        checkpoint_data.append(cp_dict)
        print(f"\n  Checkpoint {cp['id']}:")
        for key, value in cp_dict.items():
            if key == 'history' and value:
                try:
                    history = json.loads(value)
                    print(f"    {key}: {history}")
                except:
                    print(f"    {key}: {value}")
            else:
                print(f"    {key}: {value}")
    
    return checkpoint_data

def analyze_file_stats(conn):
    """Analyze file statistics to understand usage"""
    cursor = conn.cursor()
    
    # Common JuiceFS tables for file metadata
    possible_tables = ['jfs_inode', 'jfs_edge', 'jfs_chunk', 'inode', 'edge', 'chunk']
    
    for table_name in possible_tables:
        cursor.execute(f"SELECT name FROM sqlite_master WHERE type='table' AND name='{table_name}'")
        if cursor.fetchone():
            print(f"\nAnalyzing {table_name} table:")
            
            # Get row count
            cursor.execute(f"SELECT COUNT(*) as count FROM {table_name}")
            count = cursor.fetchone()['count']
            print(f"  Total entries: {count}")
            
            # Get table schema for more info
            cursor.execute(f"PRAGMA table_info({table_name})")
            columns = cursor.fetchall()
            col_names = [col['name'] for col in columns]
            
            # Sample some data
            cursor.execute(f"SELECT * FROM {table_name} LIMIT 5")
            samples = cursor.fetchall()
            if samples:
                print(f"  Sample entries:")
                for sample in samples:
                    print(f"    {dict(sample)}")

def analyze_directory_structure(base_path):
    """Analyze actual directory structure and sizes"""
    base_path = Path(base_path)
    
    # Look for active and checkpoints directories
    active_path = base_path / "active"
    checkpoints_path = base_path / "checkpoints"
    
    results = {}
    
    if active_path.exists():
        print(f"\nActive directory found at: {active_path}")
        size_info = get_directory_size_info(active_path)
        results['active'] = size_info
        print(f"  Files: {size_info['file_count']}")
        print(f"  Directories: {size_info['dir_count']}")
        print(f"  Total size: {format_size(size_info['total_size'])}")
        print(f"  Modification time: {datetime.fromtimestamp(size_info['last_modified'])}")
    
    if checkpoints_path.exists():
        print(f"\nCheckpoints directory found at: {checkpoints_path}")
        for checkpoint_dir in sorted(checkpoints_path.iterdir()):
            if checkpoint_dir.is_dir():
                size_info = get_directory_size_info(checkpoint_dir)
                checkpoint_name = checkpoint_dir.name
                results[f'checkpoint_{checkpoint_name}'] = size_info
                print(f"\n  Checkpoint {checkpoint_name}:")
                print(f"    Files: {size_info['file_count']}")
                print(f"    Directories: {size_info['dir_count']}")
                print(f"    Total size: {format_size(size_info['total_size'])}")
                print(f"    Modification time: {datetime.fromtimestamp(size_info['last_modified'])}")
    
    return results

def get_directory_size_info(path):
    """Get size and file count info for a directory"""
    total_size = 0
    file_count = 0
    dir_count = 0
    last_modified = 0
    
    for entry in path.rglob('*'):
        if entry.is_file():
            try:
                stat = entry.stat()
                # Use actual disk size if available, otherwise file size
                size = getattr(stat, 'st_blocks', stat.st_size // 512) * 512
                total_size += size
                file_count += 1
                last_modified = max(last_modified, stat.st_mtime)
            except (OSError, IOError):
                pass
        elif entry.is_dir():
            dir_count += 1
            try:
                stat = entry.stat()
                last_modified = max(last_modified, stat.st_mtime)
            except (OSError, IOError):
                pass
    
    return {
        'total_size': total_size,
        'file_count': file_count,
        'dir_count': dir_count,
        'last_modified': last_modified
    }

def format_size(size):
    """Format size in human-readable format"""
    for unit in ['B', 'KB', 'MB', 'GB']:
        if size < 1024.0:
            return f"{size:.2f} {unit}"
        size /= 1024.0
    return f"{size:.2f} TB"

def calculate_divergence(active_info, checkpoint_info):
    """Calculate how much active has diverged from a checkpoint"""
    if not active_info or not checkpoint_info:
        return None
    
    file_diff = active_info['file_count'] - checkpoint_info['file_count']
    size_diff = active_info['total_size'] - checkpoint_info['total_size']
    time_diff = active_info['last_modified'] - checkpoint_info['last_modified']
    
    return {
        'file_difference': file_diff,
        'size_difference': size_diff,
        'size_difference_formatted': format_size(abs(size_diff)),
        'time_since_checkpoint': time_diff,
        'divergence_indicator': get_divergence_indicator(file_diff, size_diff)
    }

def get_divergence_indicator(file_diff, size_diff):
    """Get a visual indicator of divergence level"""
    # Simple heuristic based on file count and size changes
    total_change = abs(file_diff) + abs(size_diff / (1024 * 1024))  # Size in MB
    
    if total_change < 10:
        return "→ (minimal)"
    elif total_change < 100:
        return "→→ (moderate)"
    elif total_change < 1000:
        return "→→→ (significant)"
    else:
        return "→→→→ (major)"

def main():
    if len(sys.argv) < 2:
        print("Usage: python analyze_juicefs_db.py <path-to-db-or-directory>")
        print("\nExamples:")
        print("  python analyze_juicefs_db.py jfs-meta-example.db")
        print("  python analyze_juicefs_db.py /path/to/juicefs/mount")
        sys.exit(1)
    
    path = sys.argv[1]
    
    # Check if it's a database file or directory
    if path.endswith('.db') and os.path.isfile(path):
        print(f"Analyzing database: {path}")
        conn = connect_db(path)
        
        # List all tables
        tables = list_tables(conn)
        print(f"\nTables in database: {tables}")
        
        # Analyze checkpoints
        checkpoint_data = analyze_checkpoints_table(conn)
        
        # Analyze file statistics
        analyze_file_stats(conn)
        
        conn.close()
        
        # If there's a directory with the same base name, analyze it too
        base_dir = path.replace('.db', '')
        if os.path.isdir(base_dir):
            print(f"\n{'='*60}")
            print(f"Analyzing directory structure: {base_dir}")
            dir_info = analyze_directory_structure(base_dir)
            
            # Calculate divergence if we have both active and checkpoints
            if 'active' in dir_info and checkpoint_data:
                print(f"\n{'='*60}")
                print("Divergence Analysis:")
                for cp in checkpoint_data:
                    cp_key = f"checkpoint_{cp['id']}"
                    if cp_key in dir_info:
                        divergence = calculate_divergence(dir_info['active'], dir_info[cp_key])
                        if divergence:
                            print(f"\n  Active vs Checkpoint {cp['id']}:")
                            print(f"    Files changed: {divergence['file_difference']:+d}")
                            print(f"    Size changed: {divergence['size_difference_formatted']}")
                            print(f"    Divergence: {divergence['divergence_indicator']}")
    
    elif os.path.isdir(path):
        print(f"Analyzing directory: {path}")
        dir_info = analyze_directory_structure(path)
        
        # Look for a .db file in the directory
        db_files = list(Path(path).glob('*.db'))
        if db_files:
            for db_file in db_files:
                print(f"\n{'='*60}")
                print(f"Found database: {db_file}")
                conn = connect_db(str(db_file))
                tables = list_tables(conn)
                print(f"Tables: {tables}")
                analyze_checkpoints_table(conn)
                conn.close()
    
    else:
        print(f"Error: {path} is neither a valid database file nor directory")
        sys.exit(1)

if __name__ == "__main__":
    main()