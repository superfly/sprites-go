"""
Sprites Python SDK

A Python client library for interacting with Sprites environments.
"""

from .client import SpritesClient
from .sprite import Sprite
from .exec import SpriteExec
from .types import Checkpoint, StreamMessage
from .exceptions import (
    SpritesError,
    AuthenticationError,
    ConnectionError,
    CheckpointError,
    RestoreError,
    ExecutionError
)

__all__ = [
    'SpritesClient',
    'Sprite', 
    'SpriteExec',
    'Checkpoint',
    'StreamMessage',
    'SpritesError',
    'AuthenticationError',
    'ConnectionError',
    'CheckpointError',
    'RestoreError',
    'ExecutionError'
]

__version__ = '0.2.0'