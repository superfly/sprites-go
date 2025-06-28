#!/usr/bin/env python3
"""
Unit tests for the Sprites Python SDK.

These tests mock external dependencies and test individual components.
"""

import sys
import json
import pytest
from unittest.mock import Mock, patch, MagicMock
from datetime import datetime
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from sprites import (
    SpritesClient, Sprite, SpriteExec,
    Checkpoint, StreamMessage,
    AuthenticationError, CheckpointError, RestoreError
)
from sprites.types import (
    STREAM_STDIN, STREAM_STDOUT, STREAM_STDERR,
    STREAM_EXIT, STREAM_STDIN_EOF
)


class TestSpritesClient:
    """Test SpritesClient class."""
    
    def test_init_with_token(self):
        """Test client initialization with token."""
        client = SpritesClient(token="test-token")
        assert client.token == "test-token"
        assert client.endpoint == "https://api.sprites.dev"
    
    def test_init_with_custom_endpoint(self):
        """Test client initialization with custom endpoint."""
        client = SpritesClient(endpoint="http://localhost:8080", token="test-token")
        assert client.endpoint == "http://localhost:8080"
        assert client.token == "test-token"
    
    def test_init_from_environment(self):
        """Test client initialization from environment variables."""
        with patch.dict('os.environ', {
            'SPRITES_TOKEN': 'env-token',
            'SPRITES_ENDPOINT': 'http://env-endpoint'
        }):
            client = SpritesClient()
            assert client.token == "env-token"
            assert client.endpoint == "http://env-endpoint"
    
    def test_init_without_token_raises(self):
        """Test that missing token raises AuthenticationError."""
        with patch.dict('os.environ', {}, clear=True):
            with pytest.raises(AuthenticationError):
                SpritesClient()
    
    def test_endpoint_trailing_slash_removed(self):
        """Test that trailing slash is removed from endpoint."""
        client = SpritesClient(endpoint="http://localhost/", token="test")
        assert client.endpoint == "http://localhost"
    
    def test_attach(self):
        """Test attaching to a sprite."""
        client = SpritesClient(token="test")
        sprite = client.attach("sprite-123")
        assert isinstance(sprite, Sprite)
        assert sprite.sprite_id == "sprite-123"
        assert sprite.client == client


class TestSprite:
    """Test Sprite class."""
    
    @pytest.fixture
    def sprite(self):
        """Create a test sprite."""
        client = Mock()
        client.endpoint = "http://localhost"
        client.token = "test-token"
        return Sprite(client, "sprite-123")
    
    def test_exec_creates_spriteexec(self, sprite):
        """Test that exec() creates a SpriteExec object."""
        exec_obj = sprite.exec("echo test")
        assert isinstance(exec_obj, SpriteExec)
        assert exec_obj.args == ["echo", "test"]  # Simple command parsed as arguments
        assert exec_obj.tty is False
    
    def test_exec_with_list_command(self, sprite):
        """Test exec with command as list."""
        exec_obj = sprite.exec(["echo", "hello", "world"])
        assert exec_obj.args == ["echo", "hello", "world"]
    
    def test_exec_with_options(self, sprite):
        """Test exec with various options."""
        exec_obj = sprite.exec(
            "test",
            cwd="/tmp",
            env={"KEY": "value"},
            tty=True,
            initial_window_size=(100, 50)
        )
        assert exec_obj.tty is True
        # Check URL contains parameters
        assert "dir=%2Ftmp" in exec_obj.ws_url  # /tmp is URL-encoded
        assert "env=KEY%3Dvalue" in exec_obj.ws_url
        assert "tty=true" in exec_obj.ws_url
        assert "cols=100" in exec_obj.ws_url
        assert "rows=50" in exec_obj.ws_url
    
    def test_build_ws_url(self, sprite):
        """Test WebSocket URL building."""
        url = sprite._build_ws_url(
            ["echo", "test"],
            cwd="/tmp",
            env={"A": "1", "B": "2"},
            tty=False,
            initial_window_size=None
        )
        
        # Check scheme conversion
        assert url.startswith("ws://")
        
        # Check path
        assert "/v1/sprites/sprite-123/exec" in url
        
        # Check query parameters
        assert "cmd=echo" in url
        assert "cmd=test" in url
        assert "path=echo" in url
        assert "dir=%2Ftmp" in url  # /tmp is URL-encoded
        assert "env=A%3D1" in url
        assert "env=B%3D2" in url
    
    def test_build_ws_url_https(self, sprite):
        """Test WebSocket URL building with HTTPS endpoint."""
        sprite.client.endpoint = "https://api.sprites.dev"
        url = sprite._build_ws_url(["test"], None, None, False, None)
        assert url.startswith("wss://")
    
    @patch('requests.post')
    def test_checkpoint(self, mock_post, sprite):
        """Test checkpoint creation."""
        # Mock streaming response
        mock_response = Mock()
        mock_response.iter_lines.return_value = [
            json.dumps({
                "type": "info",
                "message": "Starting checkpoint"
            }).encode(),
            json.dumps({
                "type": "complete",
                "message": "Checkpoint created",
                "data": {"checkpoint_id": "cp-123"}
            }).encode()
        ]
        mock_response.raise_for_status = Mock()
        mock_post.return_value = mock_response
        
        # Create checkpoint
        messages = []
        success = sprite.checkpoint(on_message=lambda m: messages.append(m))
        
        assert success is True
        assert len(messages) == 2
        assert messages[0].type == "info"
        assert messages[1].type == "complete"
    
    @patch('requests.post')
    def test_restore(self, mock_post, sprite):
        """Test checkpoint restore."""
        # Mock streaming response
        mock_response = Mock()
        mock_response.iter_lines.return_value = [
            json.dumps({
                "type": "progress",
                "message": "Restoring..."
            }).encode(),
            json.dumps({
                "type": "complete",
                "message": "Restore complete"
            }).encode()
        ]
        mock_response.raise_for_status = Mock()
        mock_post.return_value = mock_response
        
        # Restore
        messages = []
        success = sprite.restore("cp-123", on_message=lambda m: messages.append(m))
        
        assert success is True
        assert len(messages) == 2
        assert messages[0].type == "progress"
        assert messages[1].type == "complete"
    
    @patch('requests.get')
    def test_list_checkpoints(self, mock_get, sprite):
        """Test listing checkpoints."""
        mock_response = Mock()
        mock_response.json.return_value = [
            {
                "id": "cp-1",
                "create_time": "2024-01-01T00:00:00Z",
                "source_id": ""
            },
            {
                "id": "cp-2",
                "create_time": "2024-01-02T00:00:00Z",
                "source_id": "cp-1"
            }
        ]
        mock_response.raise_for_status = Mock()
        mock_get.return_value = mock_response
        
        checkpoints = sprite.list_checkpoints()
        
        assert len(checkpoints) == 2
        assert checkpoints[0].id == "cp-1"
        assert checkpoints[1].id == "cp-2"
        assert checkpoints[1].source_id == "cp-1"
    
    @patch('requests.get')
    def test_get_checkpoint(self, mock_get, sprite):
        """Test getting checkpoint details."""
        mock_response = Mock()
        mock_response.json.return_value = {
            "id": "cp-123",
            "create_time": "2024-01-01T00:00:00Z",
            "source_id": "cp-100",
            "history": ["cp-100", "cp-50", "cp-1"]
        }
        mock_response.raise_for_status = Mock()
        mock_get.return_value = mock_response
        
        checkpoint = sprite.get_checkpoint("cp-123")
        
        assert checkpoint.id == "cp-123"
        assert checkpoint.source_id == "cp-100"
        assert len(checkpoint.history) == 3


class TestSpriteExec:
    """Test SpriteExec class."""
    
    def create_exec(self, tty=False):
        """Create a test SpriteExec instance."""
        return SpriteExec(
            ws_url="ws://localhost/exec",
            token="test-token",
            cmd=["echo", "test"],
            tty=tty
        )
    
    def test_init(self):
        """Test SpriteExec initialization."""
        exec_obj = self.create_exec()
        assert exec_obj.ws_url == "ws://localhost/exec"
        assert exec_obj.token == "test-token"
        assert exec_obj.args == ["echo", "test"]
        assert exec_obj.tty is False
        assert exec_obj.returncode is None
        assert exec_obj.stdout == b''
        assert exec_obj.stderr == b''
    
    @patch('websocket.WebSocketApp')
    def test_start(self, mock_ws_class):
        """Test starting execution."""
        mock_ws = Mock()
        mock_ws_class.return_value = mock_ws
        
        exec_obj = self.create_exec()
        
        # Simulate connection opened
        exec_obj._connected.set()
        
        with patch('threading.Thread') as mock_thread:
            mock_thread_instance = Mock()
            mock_thread.return_value = mock_thread_instance
            
            exec_obj.start()
            
            # Check WebSocket created with correct parameters
            mock_ws_class.assert_called_once()
            args, kwargs = mock_ws_class.call_args
            assert args[0] == "ws://localhost/exec"
            assert kwargs['header']['Authorization'] == "Bearer test-token"
            
            # Check thread started
            mock_thread_instance.start.assert_called_once()
    
    def test_run_blocking(self):
        """Test blocking run method."""
        exec_obj = self.create_exec()
        
        # Mock start and wait
        exec_obj.start = Mock()
        exec_obj.wait = Mock(return_value=True)
        exec_obj.send_stdin = Mock()
        exec_obj.send_stdin_eof = Mock()
        
        result = exec_obj.run(stdin="test input")
        
        exec_obj.start.assert_called_once()
        exec_obj.send_stdin.assert_called_once_with(b"test input")
        exec_obj.send_stdin_eof.assert_called_once()
        exec_obj.wait.assert_called_once()
        assert result == exec_obj
    
    def test_on_message_non_tty(self):
        """Test message handling in non-TTY mode."""
        exec_obj = self.create_exec(tty=False)
        
        # Test stdout message
        stdout_msg = bytes([STREAM_STDOUT]) + b"Hello stdout"
        exec_obj._on_message(None, stdout_msg)
        assert exec_obj.stdout == b"Hello stdout"
        
        # Test stderr message
        stderr_msg = bytes([STREAM_STDERR]) + b"Hello stderr"
        exec_obj._on_message(None, stderr_msg)
        assert exec_obj.stderr == b"Hello stderr"
        
        # Test exit message
        exit_msg = bytes([STREAM_EXIT, 42])
        exec_obj._on_message(None, exit_msg)
        assert exec_obj.returncode == 42
        assert exec_obj._exit_event.is_set()
    
    def test_on_message_tty(self):
        """Test message handling in TTY mode."""
        exec_obj = self.create_exec(tty=True)
        
        # In TTY mode, all binary data goes to output
        exec_obj._on_message(None, b"TTY output")
        assert exec_obj.output == b"TTY output"
    
    def test_send_stdin_non_tty(self):
        """Test sending stdin in non-TTY mode."""
        exec_obj = self.create_exec(tty=False)
        exec_obj.ws = Mock()
        exec_obj.ws.sock.connected = True
        
        exec_obj.send_stdin("Hello")
        
        # Check message sent with stream ID
        exec_obj.ws.send.assert_called_once()
        args, kwargs = exec_obj.ws.send.call_args
        assert args[0] == bytes([STREAM_STDIN]) + b"Hello"
        assert kwargs['opcode'] == 2  # OPCODE_BINARY
    
    def test_send_stdin_tty(self):
        """Test sending stdin in TTY mode."""
        exec_obj = self.create_exec(tty=True)
        exec_obj.ws = Mock()
        exec_obj.ws.sock.connected = True
        
        exec_obj.send_stdin(b"TTY input")
        
        # In TTY mode, raw bytes sent
        exec_obj.ws.send.assert_called_once_with(b"TTY input", opcode=2)
    
    def test_resize_terminal(self):
        """Test terminal resize."""
        exec_obj = self.create_exec(tty=True)
        exec_obj.ws = Mock()
        exec_obj.ws.sock.connected = True
        
        exec_obj.resize_terminal(120, 50)
        
        # Check control message sent
        exec_obj.ws.send.assert_called_once()
        args, kwargs = exec_obj.ws.send.call_args
        control_msg = json.loads(args[0])
        assert control_msg['type'] == 'resize'
        assert control_msg['cols'] == 120
        assert control_msg['rows'] == 50
        assert kwargs['opcode'] == 1  # OPCODE_TEXT
    
    def test_resize_terminal_non_tty_raises(self):
        """Test that resize in non-TTY mode raises error."""
        exec_obj = self.create_exec(tty=False)
        with pytest.raises(RuntimeError):
            exec_obj.resize_terminal(80, 24)
    
    def test_callbacks(self):
        """Test output callbacks."""
        exec_obj = self.create_exec(tty=False)
        
        stdout_data = []
        stderr_data = []
        exit_codes = []
        
        exec_obj.on_stdout = lambda d: stdout_data.append(d)
        exec_obj.on_stderr = lambda d: stderr_data.append(d)
        exec_obj.on_exit = lambda c: exit_codes.append(c)
        
        # Simulate messages
        exec_obj._on_message(None, bytes([STREAM_STDOUT]) + b"out")
        exec_obj._on_message(None, bytes([STREAM_STDERR]) + b"err")
        exec_obj._on_message(None, bytes([STREAM_EXIT, 0]))
        
        assert stdout_data == [b"out"]
        assert stderr_data == [b"err"]
        assert exit_codes == [0]


class TestTypes:
    """Test type classes."""
    
    def test_checkpoint(self):
        """Test Checkpoint class."""
        now = datetime.now()
        cp = Checkpoint(
            id="cp-123",
            create_time=now,
            source_id="cp-100",
            history=["cp-100", "cp-50"]
        )
        
        assert cp.id == "cp-123"
        assert cp.create_time == now
        assert cp.source_id == "cp-100"
        assert cp.history == ["cp-100", "cp-50"]
    
    def test_checkpoint_defaults(self):
        """Test Checkpoint with defaults."""
        cp = Checkpoint(id="cp-1", create_time=datetime.now())
        assert cp.source_id == ""
        assert cp.history == []
    
    def test_stream_message(self):
        """Test StreamMessage class."""
        msg = StreamMessage(
            type="info",
            message="Test message",
            error="",
            data={"key": "value"}
        )
        
        assert msg.type == "info"
        assert msg.message == "Test message"
        assert msg.error == ""
        assert msg.data == {"key": "value"}
        assert isinstance(msg.time, datetime)
    
    def test_stream_message_defaults(self):
        """Test StreamMessage with defaults."""
        msg = StreamMessage(type="error")
        assert msg.message == ""
        assert msg.data == {}
        assert isinstance(msg.time, datetime)


class TestExceptions:
    """Test exception classes."""
    
    def test_exception_hierarchy(self):
        """Test exception inheritance."""
        from sprites.exceptions import SpritesError
        
        assert issubclass(AuthenticationError, SpritesError)
        assert issubclass(CheckpointError, SpritesError)
        assert issubclass(RestoreError, SpritesError)
    
    def test_exception_messages(self):
        """Test exception messages."""
        exc = AuthenticationError("Invalid token")
        assert str(exc) == "Invalid token"
        
        exc = CheckpointError("Failed to create")
        assert str(exc) == "Failed to create"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])