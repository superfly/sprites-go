"""
Pytest configuration for Sprites SDK tests.

This module configures test behavior based on environment capabilities.
"""

import os
import pytest
import subprocess


def juicefs_available():
    """Check if JuiceFS is available and configured."""
    try:
        # Check if juicefs binary exists
        result = subprocess.run(['which', 'juicefs'], capture_output=True)
        if result.returncode != 0:
            return False
        
        # Check if JuiceFS environment variables are set
        if not os.environ.get('SPRITE_JUICEFS_META_URL'):
            return False
            
        return True
    except Exception:
        return False


def pytest_configure(config):
    """Configure pytest with custom markers and settings."""
    # Add marker descriptions programmatically
    config.addinivalue_line(
        "markers", "checkpoint: Tests requiring JuiceFS checkpoint/restore"
    )
    config.addinivalue_line(
        "markers", "tty: Tests requiring TTY functionality"
    )


def pytest_collection_modifyitems(config, items):
    """Modify test collection to skip tests based on environment."""
    skip_checkpoint = pytest.mark.skip(
        reason="JuiceFS not available or not configured"
    )
    
    # Only skip checkpoint tests if JuiceFS is not available
    if not juicefs_available():
        for item in items:
            if "checkpoint" in item.keywords:
                item.add_marker(skip_checkpoint)
    
    # Optionally skip TTY tests if requested
    if os.environ.get('SKIP_TTY_TESTS'):
        skip_tty = pytest.mark.skip(reason="TTY tests skipped by environment")
        for item in items:
            if "tty" in item.keywords:
                item.add_marker(skip_tty)