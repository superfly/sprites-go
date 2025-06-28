"""
Command execution functionality for Sprites SDK.
"""

import json
import threading
import queue
from typing import Optional, Union, Callable
import websocket
import time

from .types import (
    STREAM_STDIN, STREAM_STDOUT, STREAM_STDERR, 
    STREAM_EXIT, STREAM_STDIN_EOF
)
from .exceptions import ConnectionError, ExecutionError


class SpriteExec:
    """
    Represents a command execution in a Sprite.
    
    This class handles the WebSocket connection and protocol for executing
    commands within a Sprite environment. It provides methods to send input,
    receive output, and control the execution.
    
    Attributes:
        args (list): The command arguments being executed.
        tty (bool): Whether this is a TTY session.
        returncode (int): The exit code of the command (None until command exits).
        stdout (bytes): Accumulated stdout data (non-TTY mode only).
        stderr (bytes): Accumulated stderr data (non-TTY mode only).
        output (bytes): Accumulated output data (TTY mode only).
    """
    
    def __init__(self, ws_url: str, token: str, cmd: list, tty: bool = False):
        """Initialize the exec command."""
        self.ws_url = ws_url
        self.token = token
        self.args = cmd
        self.tty = tty
        
        # Results
        self.returncode = None
        self.stdout = b''
        self.stderr = b''
        self.output = b''  # For TTY mode
        
        # WebSocket connection
        self.ws = None
        self._ws_thread = None
        self._connected = threading.Event()
        self._exit_event = threading.Event()
        self._error = None
        
        # Output queues
        self._stdout_queue = queue.Queue()
        self._stderr_queue = queue.Queue()
        self._output_queue = queue.Queue()  # For TTY mode
        
        # Callbacks
        self.on_stdout = None  # Callback for stdout data
        self.on_stderr = None  # Callback for stderr data
        self.on_output = None  # Callback for TTY output
        self.on_exit = None    # Callback for process exit
    
    def start(self):
        """
        Start the command execution.
        
        This establishes the WebSocket connection and begins executing the command.
        Use this for non-blocking execution where you want to interact with the
        process while it's running.
        
        Example:
            >>> exec = sprite.exec("bash", tty=True)
            >>> exec.start()
            >>> exec.send_stdin(b"echo hello\\n")
            >>> # Process runs in background
        """
        # Create WebSocket connection with ping interval
        self.ws = websocket.WebSocketApp(
            self.ws_url,
            header={"Authorization": f"Bearer {self.token}"},
            on_open=self._on_open,
            on_message=self._on_message,
            on_error=self._on_error,
            on_close=self._on_close,
            on_ping=self._on_ping,
            on_pong=self._on_pong
        )
        
        # Start WebSocket in thread
        self._ws_thread = threading.Thread(target=self._run_websocket)
        self._ws_thread.daemon = True
        self._ws_thread.start()
        
        # Wait for connection
        if not self._connected.wait(timeout=10):
            raise ConnectionError("Failed to establish WebSocket connection")
    
    def run(self, stdin: Optional[Union[str, bytes]] = None, timeout: Optional[float] = None):
        """
        Run the command to completion.
        
        This is a blocking call that waits for the command to finish.
        
        Args:
            stdin (str or bytes, optional): Input to send to the command.
            timeout (float, optional): Timeout in seconds.
            
        Returns:
            self: Returns self with populated results.
            
        Example:
            >>> result = sprite.exec("cat").run(stdin="Hello World")
            >>> print(result.stdout.decode())
            Hello World
        """
        self.start()
        
        # Send stdin if provided
        if stdin is not None:
            if isinstance(stdin, str):
                stdin = stdin.encode('utf-8')
            self.send_stdin(stdin)
            if not self.tty:
                self.send_stdin_eof()
        
        # Wait for completion
        if not self.wait(timeout):
            raise TimeoutError(f"Command timed out after {timeout} seconds")
        
        # Small delay to allow any remaining WebSocket messages to be processed
        # This prevents race conditions where stdout/stderr messages arrive after
        # the exit code
        time.sleep(0.3)  # 300ms delay for parallel execution reliability
        
        # Process any remaining queued messages (just drain them, don't accumulate)
        # The data has already been added to self.stdout/stderr in _on_message
        while not self._stdout_queue.empty():
            try:
                self._stdout_queue.get_nowait()
            except queue.Empty:
                break
                
        while not self._stderr_queue.empty():
            try:
                self._stderr_queue.get_nowait()
            except queue.Empty:
                break
        
        return self
    
    def wait(self, timeout: Optional[float] = None) -> bool:
        """
        Wait for the command to complete.
        
        Args:
            timeout (float, optional): Maximum time to wait in seconds.
            
        Returns:
            bool: True if command completed, False if timed out.
        """
        return self._exit_event.wait(timeout)
    
    def send_stdin(self, data: Union[str, bytes]):
        """
        Send data to the process's stdin.
        
        Args:
            data (str or bytes): Data to send. Strings are encoded as UTF-8.
            
        Example:
            >>> exec.send_stdin("echo hello\\n")
        """
        if isinstance(data, str):
            data = data.encode('utf-8')
        
        if not self.ws or not self.ws.sock or not self.ws.sock.connected:
            raise RuntimeError("WebSocket not connected")
        
        if self.tty:
            # In TTY mode, send raw bytes
            self.ws.send(data, opcode=websocket.ABNF.OPCODE_BINARY)
        else:
            # In non-TTY mode, prepend stream ID
            message = bytes([STREAM_STDIN]) + data
            self.ws.send(message, opcode=websocket.ABNF.OPCODE_BINARY)
    
    def send_stdin_eof(self):
        """
        Send EOF to stdin (non-TTY mode only).
        
        This closes the stdin stream, indicating no more input will be sent.
        """
        if self.tty:
            raise RuntimeError("Cannot send explicit EOF in TTY mode")
        
        if not self.ws or not self.ws.sock or not self.ws.sock.connected:
            raise RuntimeError("WebSocket not connected")
        
        eof_message = bytes([STREAM_STDIN_EOF])
        self.ws.send(eof_message, opcode=websocket.ABNF.OPCODE_BINARY)
    
    def resize_terminal(self, cols: int, rows: int):
        """
        Send a terminal resize event (TTY mode only).
        
        Args:
            cols (int): Number of columns.
            rows (int): Number of rows.
            
        Example:
            >>> exec.resize_terminal(120, 40)
        """
        if not self.tty:
            raise RuntimeError("Terminal resize only available in TTY mode")
        
        if not self.ws or not self.ws.sock or not self.ws.sock.connected:
            raise RuntimeError("WebSocket not connected")
        
        control_msg = {
            "type": "resize",
            "cols": cols,
            "rows": rows
        }
        
        self.ws.send(json.dumps(control_msg), opcode=websocket.ABNF.OPCODE_TEXT)
    
    def send_control_message(self, message: dict):
        """
        Send a custom control message.
        
        Control messages are sent as JSON text frames. Currently, the only
        supported control message is the resize message, which is handled
        by the resize_terminal() method.
        
        This method is provided for future extensibility or custom server
        implementations that support additional control messages.
        
        Args:
            message (dict): Control message to send as JSON.
            
        Example:
            >>> # Send a custom control message (for custom server implementations)
            >>> exec.send_control_message({"type": "custom", "data": "value"})
        """
        if not self.ws or not self.ws.sock or not self.ws.sock.connected:
            raise RuntimeError("WebSocket not connected")
        
        self.ws.send(json.dumps(message), opcode=websocket.ABNF.OPCODE_TEXT)
    
    def read_stdout(self, timeout: Optional[float] = None) -> bytes:
        """
        Read available stdout data (non-TTY mode only).
        
        Args:
            timeout (float, optional): Maximum time to wait for data.
            
        Returns:
            bytes: Available stdout data.
        """
        if self.tty:
            raise RuntimeError("Use read_output() for TTY mode")
        
        try:
            return self._stdout_queue.get(timeout=timeout)
        except queue.Empty:
            return b''
    
    def read_stderr(self, timeout: Optional[float] = None) -> bytes:
        """
        Read available stderr data (non-TTY mode only).
        
        Args:
            timeout (float, optional): Maximum time to wait for data.
            
        Returns:
            bytes: Available stderr data.
        """
        if self.tty:
            raise RuntimeError("Use read_output() for TTY mode")
        
        try:
            return self._stderr_queue.get(timeout=timeout)
        except queue.Empty:
            return b''
    
    def read_output(self, timeout: Optional[float] = None) -> bytes:
        """
        Read available output data (TTY mode only).
        
        In TTY mode, all output is combined into a single stream.
        
        Args:
            timeout (float, optional): Maximum time to wait for data.
            
        Returns:
            bytes: Available output data.
        """
        if not self.tty:
            raise RuntimeError("Use read_stdout() and read_stderr() for non-TTY mode")
        
        try:
            return self._output_queue.get(timeout=timeout)
        except queue.Empty:
            return b''
    
    def close(self):
        """
        Close the WebSocket connection and clean up resources.
        """
        if self.ws:
            try:
                self.ws.close()
            except:
                pass
        
        # Wait for thread to finish
        if self._ws_thread and self._ws_thread.is_alive():
            self._ws_thread.join(timeout=1)
    
    def _run_websocket(self):
        """
        Run the WebSocket connection.
        
        The connection automatically handles ping/pong frames to keep the
        connection alive. A ping is sent every 30 seconds, and if no pong
        is received within 10 seconds, the connection is considered dead.
        """
        try:
            # Run with automatic ping/pong handling for keepalive
            self.ws.run_forever(ping_interval=30, ping_timeout=10)
        except Exception as e:
            self._error = e
            self._exit_event.set()
    
    def _on_open(self, ws):
        """Handle WebSocket connection opened."""
        self._connected.set()
    
    def _on_message(self, ws, message):
        """Handle incoming WebSocket messages."""
        if isinstance(message, str):
            # Text message - control message
            try:
                data = json.loads(message)
                # Currently we don't receive control messages from server
                # but this is where they would be handled
            except:
                pass
        else:
            # Binary message - data or exit code
            if len(message) == 0:
                return
            
            if self.tty:
                # In TTY mode, check if this is an exit code message
                if len(message) == 2 and message[0] == STREAM_EXIT:
                    # TTY mode exit code
                    exit_code = message[1]
                    # Server sometimes sends -1 (255 as unsigned) for successful TTY commands
                    # This is a known issue with PTY exit codes
                    if exit_code == 255:  # -1 as unsigned byte
                        self.returncode = 0
                    else:
                        self.returncode = exit_code
                    
                    if self.on_exit:
                        self.on_exit(self.returncode)
                    
                    self._exit_event.set()
                else:
                    # Regular TTY output
                    self.output += message
                    self._output_queue.put(message)
                    if self.on_output:
                        self.on_output(message)
            else:
                # Non-TTY mode - check stream ID
                stream_id = message[0]
                data = message[1:]
                
                if stream_id == STREAM_STDOUT:
                    self.stdout += data
                    self._stdout_queue.put(data)
                    if self.on_stdout:
                        self.on_stdout(data)
                
                elif stream_id == STREAM_STDERR:
                    self.stderr += data
                    self._stderr_queue.put(data)
                    if self.on_stderr:
                        self.on_stderr(data)
                
                elif stream_id == STREAM_EXIT:
                    if len(data) > 0:
                        exit_code = data[0]
                        # Handle signed byte conversion: if > 127, it's negative
                        if exit_code > 127:
                            self.returncode = exit_code - 256  # Convert to signed
                        else:
                            self.returncode = exit_code
                    else:
                        self.returncode = 0
                    
                    if self.on_exit:
                        self.on_exit(self.returncode)
                    
                    self._exit_event.set()
    
    def _on_error(self, ws, error):
        """Handle WebSocket errors."""
        self._error = error
        self._exit_event.set()
    
    def _on_close(self, ws, close_status_code, close_msg):
        """Handle WebSocket connection closed."""
        if self.returncode is None:
            # If we didn't get an exit code, check if we're in TTY mode
            if self.tty:
                # For TTY mode, if we have output and no explicit error, assume success
                self.returncode = 0
            else:
                # For non-TTY mode, assume error if no exit code received
                self.returncode = 1
        self._exit_event.set()
    
    def _on_ping(self, ws, message):
        """
        Handle ping frame (for logging/debugging).
        
        Note: The websocket-client library automatically responds with a pong,
        so no manual handling is required. This callback is only for monitoring.
        """
        # websocket-client handles pong automatically
        pass
    
    def _on_pong(self, ws, message):
        """
        Handle pong frame (for logging/debugging).
        
        This is called when we receive a pong response to our ping.
        The connection is kept alive automatically by the ping_interval setting.
        """
        pass