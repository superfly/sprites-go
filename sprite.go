package sprites

// Sprite represents a sprite instance.
type Sprite struct {
	name   string
	client *Client
}

// Name returns the sprite's name.
func (s *Sprite) Name() string {
	return s.name
}

// Destroy destroys the sprite.
// This is a placeholder for the actual sprite destruction API call.
func (s *Sprite) Destroy() error {
	// TODO: Implement actual sprite destruction API call
	return nil
}

