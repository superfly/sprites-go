"""
Common types and constants for the Sprites SDK.
"""

from typing import Dict, Any, NamedTuple
from datetime import datetime

# Stream IDs from the protocol
STREAM_STDIN = 0x00
STREAM_STDOUT = 0x01
STREAM_STDERR = 0x02
STREAM_EXIT = 0x03
STREAM_STDIN_EOF = 0x04


class Checkpoint:
    """
    Represents a checkpoint.
    
    Attributes:
        id (str): Unique identifier for the checkpoint.
        create_time (datetime): When the checkpoint was created.
        source_id (str): ID of the source checkpoint if this is a restore.
        history (list): List of checkpoint IDs in the history chain.
    """
    def __init__(self, id: str, create_time: datetime, source_id: str = "", history: list = None):
        self.id = id
        self.create_time = create_time
        self.source_id = source_id
        self.history = history or []


class StreamMessage:
    """
    Represents a streaming message from checkpoint/restore operations.
    
    Attributes:
        type (str): Message type (info, error, progress, complete).
        message (str): Human-readable message.
        time (datetime): When the message was generated.
        error (str): Error details if type is "error".
        data (dict): Additional data specific to the message type.
    """
    def __init__(self, type: str, message: str = "", time: datetime = None, 
                 error: str = "", data: Dict[str, Any] = None):
        self.type = type
        self.message = message
        self.time = time or datetime.now()
        self.error = error
        self.data = data or {}