"""
Sprites Python Client

This module provides the main client interface for interacting with Sprites environments.
"""

import os
from typing import Optional

from .sprite import Sprite
from .exceptions import AuthenticationError


class SpritesClient:
    """
    Client for interacting with the Sprites API.
    
    This client allows you to attach to existing Sprites and execute commands
    within them using WebSocket connections.
    
    Args:
        endpoint (str, optional): The Sprites API endpoint URL. 
            Defaults to 'https://api.sprites.dev' or the value of 
            SPRITES_ENDPOINT environment variable if set.
        token (str, optional): Authentication token for the API.
            If not provided, will try to read from SPRITES_TOKEN environment variable.
    
    Example:
        >>> client = SpritesClient(token="your-api-token")
        >>> sprite = client.attach("sprite-id")
        >>> result = sprite.exec(["echo", "Hello from Sprite!"])
        >>> print(result.stdout)
        Hello from Sprite!
    """
    
    def __init__(self, endpoint: Optional[str] = None, token: Optional[str] = None):
        """Initialize the Sprites client."""
        self.endpoint = endpoint or os.environ.get('SPRITES_ENDPOINT', 'https://api.sprites.dev')
        self.token = token or os.environ.get('SPRITES_TOKEN')
        
        if not self.token:
            raise AuthenticationError(
                "API token must be provided either as argument or via SPRITES_TOKEN environment variable"
            )
        
        # Ensure endpoint doesn't have trailing slash
        self.endpoint = self.endpoint.rstrip('/')
    
    def attach(self, sprite_id: str) -> Sprite:
        """
        Attach to an existing Sprite by ID.
        
        Args:
            sprite_id (str): The ID of the Sprite to attach to.
            
        Returns:
            Sprite: A Sprite object that can be used to execute commands.
            
        Example:
            >>> sprite = client.attach("my-sprite-id")
            >>> result = sprite.exec(["ls", "-la"])
        """
        return Sprite(self, sprite_id)