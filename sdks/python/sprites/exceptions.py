"""
Custom exceptions for the Sprites SDK.
"""


class SpritesError(Exception):
    """Base exception for all Sprites SDK errors."""
    pass


class AuthenticationError(SpritesError):
    """Raised when authentication fails."""
    pass


class ConnectionError(SpritesError):
    """Raised when connection to the Sprites API fails."""
    pass


class CheckpointError(SpritesError):
    """Raised when checkpoint operations fail."""
    pass


class RestoreError(SpritesError):
    """Raised when restore operations fail."""
    pass


class ExecutionError(SpritesError):
    """Raised when command execution fails."""
    pass