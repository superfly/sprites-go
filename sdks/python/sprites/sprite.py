"""
Sprite class for interacting with a specific Sprite environment.
"""

import json
import requests
from typing import Optional, Union, List, Dict, Callable, Iterator
from urllib.parse import urlparse, urlencode, quote, quote_plus
from datetime import datetime
import shlex
import re

from .exec import SpriteExec
from .types import Checkpoint, StreamMessage
from .exceptions import CheckpointError, RestoreError


def parse_datetime(dt_string):
    """
    Parse various ISO 8601 datetime formats flexibly.
    
    Handles:
    - RFC 3339 / ISO 8601 with 'Z' suffix
    - ISO 8601 with timezone offset (+00:00)
    - Microseconds with various precisions
    - Missing timezone (assumes UTC)
    """
    if not dt_string:
        return datetime.now()
    
    # Handle 'Z' suffix by replacing with '+00:00'
    dt_string = dt_string.replace('Z', '+00:00')
    
    # Try parsing with fromisoformat first (works for most standard formats)
    try:
        return datetime.fromisoformat(dt_string)
    except (ValueError, AttributeError):
        pass
    
    # Handle microseconds with more than 6 digits by truncating
    # Match pattern: 2025-06-28T19:08:52.11605474+00:00
    pattern = r'(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2})\.(\d+)([\+\-]\d{2}:\d{2}|Z)?'
    match = re.match(pattern, dt_string)
    if match:
        base_time, microseconds, tz_offset = match.groups()
        # Truncate microseconds to 6 digits
        microseconds = microseconds[:6].ljust(6, '0')
        # Reconstruct the datetime string
        dt_string = f"{base_time}.{microseconds}"
        if tz_offset:
            dt_string += tz_offset if tz_offset != 'Z' else '+00:00'
        else:
            dt_string += '+00:00'  # Assume UTC if no timezone
        
        try:
            return datetime.fromisoformat(dt_string)
        except (ValueError, AttributeError):
            pass
    
    # Last resort: try parsing without microseconds
    try:
        # Remove microseconds entirely
        dt_string = re.sub(r'\.\d+', '', dt_string)
        return datetime.fromisoformat(dt_string)
    except (ValueError, AttributeError):
        # If all parsing fails, return current time
        return datetime.now()


class Sprite:
    """
    Represents an attached Sprite environment.
    
    This class provides methods to execute commands within the Sprite,
    create checkpoints, and restore from checkpoints.
    
    Args:
        client: The SpritesClient instance that created this Sprite.
        sprite_id (str): The ID of the Sprite.
    """
    
    def __init__(self, client, sprite_id: str):
        """Initialize the Sprite instance."""
        self.client = client
        self.sprite_id = sprite_id
    
    def exec(self, 
             cmd: Union[str, List[str]], 
             cwd: Optional[str] = None,
             env: Optional[Dict[str, str]] = None,
             tty: bool = False,
             initial_window_size: Optional[tuple] = None) -> SpriteExec:
        """
        Execute a command in the Sprite.
        
        This returns a SpriteExec object that can be used to interact with
        the running process.
        
        Args:
            cmd (str or list): Command to execute. Can be a string that will be
                parsed into command arguments, or a list of arguments.
                If the string contains shell syntax (like |, >, ;, $), it will
                be executed via /bin/sh -c. Otherwise, it's parsed as individual arguments.
            cwd (str, optional): Working directory for the command.
            env (dict, optional): Environment variables to set for the command.
            tty (bool): Whether to allocate a pseudo-TTY. Default is False.
                In TTY mode, all I/O is raw bytes without stream multiplexing.
            initial_window_size (tuple, optional): Initial terminal size as (cols, rows)
                for TTY mode.
            
        Returns:
            SpriteExec: An object to interact with the running command.
            
        Example:
            >>> # Simple command (parsed as arguments)
            >>> exec = sprite.exec("echo hello world")
            >>> exec.run()
            >>> print(exec.stdout)
            b'hello world\\n'
            
            >>> # Shell command (executed via /bin/sh -c)
            >>> exec = sprite.exec("echo hello | wc -w")
            >>> exec.run()
            >>> print(exec.stdout)
            b'1\\n'
            
            >>> # Command as list (executed directly)
            >>> exec = sprite.exec(["echo", "hello world"])
            >>> exec.run()
            >>> print(exec.stdout)
            b'hello world\\n'
            
            >>> # Interactive TTY command
            >>> exec = sprite.exec(["/bin/bash"], tty=True)
            >>> exec.send_stdin(b"ls\\n")
            >>> output = exec.read_output()
        """
        # Convert string command to list if needed
        if isinstance(cmd, str):
            # Check if the command contains shell syntax
            shell_chars = ['|', '>', '<', ';', '&', '$', '`', '(', ')', '{', '}', '*', '?', '[', ']']
            # Also check for quotes which indicate shell parsing is needed
            has_quotes = "'" in cmd or '"' in cmd
            
            if any(char in cmd for char in shell_chars) or has_quotes:
                # Use shell execution for complex commands or quoted strings
                cmd = ["/bin/sh", "-c", cmd]
            else:
                # Parse simple commands into arguments
                cmd = shlex.split(cmd)
        
        # Build WebSocket URL
        ws_url = self._build_ws_url(cmd, cwd, env, tty, initial_window_size)
        
        # Create exec command
        return SpriteExec(
            ws_url=ws_url,
            token=self.client.token,
            cmd=cmd,
            tty=tty
        )
    
    def checkpoint(self, on_message: Optional[Callable[[StreamMessage], None]] = None) -> bool:
        """
        Create a checkpoint of the current Sprite state.
        
        This creates a snapshot of the Sprite's filesystem and process state
        that can be restored later.
        
        Args:
            on_message (callable, optional): Callback function that receives
                streaming messages during the checkpoint operation.
                
        Returns:
            bool: True if checkpoint was created successfully.
            
        Raises:
            CheckpointError: If the checkpoint operation fails.
            
        Example:
            >>> # Simple checkpoint
            >>> success = sprite.checkpoint()
            >>> if success:
            ...     print("Checkpoint created successfully")
            
            >>> # Checkpoint with progress monitoring
            >>> def on_progress(msg):
            ...     print(f"{msg.type}: {msg.message}")
            >>> success = sprite.checkpoint(on_message=on_progress)
        """
        url = f"{self.client.endpoint}/v1/sprites/{self.sprite_id}/checkpoint"
        headers = {"Authorization": f"Bearer {self.client.token}"}
        
        try:
            response = requests.post(url, headers=headers, stream=True)
            response.raise_for_status()
            
            completed = False
            had_error = False
            
            # Process streaming response
            for line in response.iter_lines():
                if not line:
                    continue
                    
                try:
                    data = json.loads(line)
                    msg = StreamMessage(
                        type=data.get("type", ""),
                        message=data.get("message", ""),
                        time=parse_datetime(data.get("time")),
                        error=data.get("error", ""),
                        data=data.get("data", {})
                    )
                    
                    # Check for completion
                    if msg.type == "complete":
                        completed = True
                    
                    # Check for errors
                    if msg.type == "error":
                        had_error = True
                    
                    # Call user callback if provided
                    if on_message:
                        on_message(msg)
                        
                except json.JSONDecodeError:
                    # Skip invalid JSON lines
                    pass
            
            if had_error:
                raise CheckpointError("Checkpoint operation failed")
            
            if not completed:
                raise CheckpointError("Checkpoint operation did not complete")
            
            return True
            
        except requests.RequestException as e:
            raise CheckpointError(f"Failed to create checkpoint: {e}")
    
    def restore(self, checkpoint_id: str, on_message: Optional[Callable[[StreamMessage], None]] = None) -> bool:
        """
        Restore the Sprite to a previous checkpoint state.
        
        This replaces the current Sprite state with the state from the
        specified checkpoint.
        
        Args:
            checkpoint_id (str): ID of the checkpoint to restore.
            on_message (callable, optional): Callback function that receives
                streaming messages during the restore operation.
                
        Returns:
            bool: True if restore was successful.
                
        Raises:
            RestoreError: If the restore operation fails.
            
        Example:
            >>> # Simple restore
            >>> success = sprite.restore("checkpoint-123")
            >>> if success:
            ...     print("Restore completed successfully")
            
            >>> # Restore with progress monitoring
            >>> def on_progress(msg):
            ...     print(f"{msg.type}: {msg.message}")
            >>> success = sprite.restore("checkpoint-123", on_message=on_progress)
        """
        url = f"{self.client.endpoint}/v1/sprites/{self.sprite_id}/checkpoints/{checkpoint_id}/restore"
        headers = {"Authorization": f"Bearer {self.client.token}"}
        
        try:
            response = requests.post(url, headers=headers, stream=True)
            response.raise_for_status()
            
            completed = False
            had_error = False
            error_message = ""
            
            # Process streaming response
            for line in response.iter_lines():
                if not line:
                    continue
                    
                try:
                    data = json.loads(line)
                    msg = StreamMessage(
                        type=data.get("type", ""),
                        message=data.get("message", ""),
                        time=parse_datetime(data.get("time")),
                        error=data.get("error", ""),
                        data=data.get("data", {})
                    )
                    
                    # Check for completion
                    if msg.type == "complete":
                        completed = True
                    
                    # Check for errors
                    if msg.type == "error":
                        had_error = True
                        error_message = msg.error or msg.message
                    
                    # Call user callback if provided
                    if on_message:
                        on_message(msg)
                        
                except json.JSONDecodeError:
                    # Skip invalid JSON lines
                    pass
            
            if had_error:
                raise RestoreError(f"Restore failed: {error_message}")
            
            if not completed:
                raise RestoreError("Restore operation did not complete")
            
            return True
                    
        except requests.RequestException as e:
            raise RestoreError(f"Failed to restore checkpoint: {e}")
    
    def list_checkpoints(self, history_filter: Optional[str] = None) -> List[Checkpoint]:
        """
        List available checkpoints for this Sprite.
        
        Args:
            history_filter (str, optional): If provided, only return checkpoints
                that have this checkpoint ID in their history chain.
                
        Returns:
            List[Checkpoint]: List of available checkpoints, sorted by creation
                time (newest first).
                
        Example:
            >>> # List all checkpoints
            >>> checkpoints = sprite.list_checkpoints()
            >>> for cp in checkpoints:
            ...     print(f"{cp.id}: {cp.create_time}")
            
            >>> # List checkpoints derived from a specific checkpoint
            >>> related = sprite.list_checkpoints(history_filter="checkpoint-123")
        """
        url = f"{self.client.endpoint}/v1/sprites/{self.sprite_id}/checkpoints"
        headers = {"Authorization": f"Bearer {self.client.token}"}
        params = {}
        
        if history_filter:
            params["history"] = history_filter
        
        try:
            response = requests.get(url, headers=headers, params=params)
            response.raise_for_status()
            
            if history_filter:
                # History filter returns plain text
                checkpoints = []
                for line in response.text.strip().split('\n'):
                    if line:
                        # Parse checkpoint ID from grep-style output
                        # Format: "checkpoint-id: history line"
                        checkpoint_id = line.split(':')[0].strip()
                        checkpoints.append(self._get_checkpoint(checkpoint_id))
                return checkpoints
            else:
                # Regular listing returns JSON
                data = response.json()
                checkpoints = []
                for item in data:
                    checkpoints.append(Checkpoint(
                        id=item["id"],
                        create_time=parse_datetime(item.get("create_time")),
                        source_id=item.get("source_id", ""),
                        history=[]  # Not included in list response
                    ))
                return checkpoints
                
        except requests.RequestException as e:
            raise CheckpointError(f"Failed to list checkpoints: {e}")
    
    def get_checkpoint(self, checkpoint_id: str) -> Checkpoint:
        """
        Get detailed information about a specific checkpoint.
        
        Args:
            checkpoint_id (str): ID of the checkpoint.
            
        Returns:
            Checkpoint: Detailed checkpoint information including history.
            
        Example:
            >>> checkpoint = sprite.get_checkpoint("checkpoint-123")
            >>> print(f"Created: {checkpoint.create_time}")
            >>> print(f"History: {checkpoint.history}")
        """
        return self._get_checkpoint(checkpoint_id)
    
    def _get_checkpoint(self, checkpoint_id: str) -> Checkpoint:
        """Internal method to get checkpoint details."""
        url = f"{self.client.endpoint}/v1/sprites/{self.sprite_id}/checkpoints/{checkpoint_id}"
        headers = {"Authorization": f"Bearer {self.client.token}"}
        
        try:
            response = requests.get(url, headers=headers)
            response.raise_for_status()
            data = response.json()
            
            return Checkpoint(
                id=data["id"],
                create_time=parse_datetime(data.get("create_time")),
                source_id=data.get("source_id", ""),
                history=data.get("history", [])
            )
            
        except requests.RequestException as e:
            if hasattr(e, 'response') and e.response.status_code == 404:
                raise CheckpointError(f"Checkpoint not found: {checkpoint_id}")
            raise CheckpointError(f"Failed to get checkpoint: {e}")
    
    def _build_ws_url(self, cmd: List[str], cwd: Optional[str], 
                      env: Optional[Dict[str, str]], tty: bool,
                      initial_window_size: Optional[tuple]) -> str:
        """Build the WebSocket URL for exec endpoint."""
        # Parse the base URL
        parsed = urlparse(self.client.endpoint)
        
        # Convert scheme to WebSocket
        if parsed.scheme == 'https':
            ws_scheme = 'wss'
        elif parsed.scheme == 'http':
            ws_scheme = 'ws'
        else:
            raise ValueError(f"Unsupported scheme: {parsed.scheme}")
        
        # Build the path
        path = f"/v1/sprites/{self.sprite_id}/exec"
        
        # Build query parameters manually to match Go client order
        query_parts = []
        
        # Add command arguments (all as 'cmd' parameters)
        for arg in cmd:
            query_parts.append(f"cmd={quote_plus(arg)}")
        
        # Add path parameter (first command argument)
        if cmd:
            query_parts.append(f"path={quote_plus(cmd[0])}")
        
        # Add optional parameters
        if cwd:
            query_parts.append(f"dir={quote_plus(cwd)}")
        
        if tty:
            query_parts.append("tty=true")
            
            # Add initial terminal size if provided
            if initial_window_size:
                cols, rows = initial_window_size
                query_parts.append(f"cols={cols}")
                query_parts.append(f"rows={rows}")
        
        if env:
            for key, value in env.items():
                env_str = f"{key}={value}"
                query_parts.append(f"env={quote_plus(env_str)}")
        
        # Build the final URL
        query_string = "&".join(query_parts)
        ws_url = f"{ws_scheme}://{parsed.netloc}{path}?{query_string}"
        
        return ws_url