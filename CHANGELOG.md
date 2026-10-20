# Changelog

## 0.2.2 - 2026-10-20

- Require Go 1.26.0 or newer, including the example and test CLI modules.
- Fix filesystem `Stat` to return information about the requested directory
  rather than its first child, and correctly handle empty directories and root.
- Preserve HTTP status, request IDs, API error metadata, and underlying causes
  when command WebSocket connections fail. Bound and sanitize diagnostic text.
- Copy the default WebSocket dialer before configuring command connections.
- Update `golang.org/x/term` to 0.46.0 and synchronize nested module dependencies.
