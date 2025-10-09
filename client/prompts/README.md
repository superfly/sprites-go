# Prompts Package

Clean, reusable UI components for user interaction using [charmbracelet/huh](https://github.com/charmbracelet/huh).

## File Organization

### `common.go`
Shared utilities and helpers:
- `isInteractiveTerminal()` - Detects if running in interactive terminal
- `configureForm()` - Applies accessibility and theming
- `getOrgDisplayName()` - Formats organization names

### `organization.go`
Organization selection prompts:
- `SelectOrganization()` - Select from existing orgs
- `PromptForFlyOrganization()` - Select from Fly.io orgs
- `SelectURLForAlias()` - Select URL for new alias

### `sprite.go`
Sprite-related prompts:
- `PromptForSpriteName()` - Enter sprite name with validation

### `auth.go`
Authentication and confirmation prompts:
- `PromptToAuthenticate()` - Confirm starting auth flow
- `PromptToReAuthenticate()` - Confirm re-authentication
- `PromptForInviteCode()` - Enter invite code
- `PromptForConfirmation()` - Generic yes/no confirmation
- `PromptForAuth()` - Manual auth setup (org name, URL, token)

### `api.go`
Server/API operation prompts (existing)

## Design Principles

### 1. **Clean Separation**
Each prompt type has its own file for easy maintenance

### 2. **Consistent Interface**
All prompts return `(result, error)` pattern

### 3. **Accessibility**
- Automatically enables accessible mode for non-TTY
- Respects `ACCESSIBLE` and `NO_COLOR` env vars
- Works in CI/CD environments

### 4. **Validation**
Input prompts include appropriate validation:
- Required fields
- Format validation (e.g., URLs, sprite names)
- Clear error messages

### 5. **User-Friendly**
- Clear titles and descriptions
- Helpful placeholders
- Affirmative/Negative button labels

## Usage Examples

### Sprite Name

```go
import "github.com/superfly/sprite-env/client/prompts"

name, err := prompts.PromptForSpriteName()
if err != nil {
    return err
}
// name is validated: alphanumeric, hyphens, underscores only
```

### Organization Selection

```go
import "github.com/superfly/sprite-env/client/prompts"

org, err := prompts.SelectOrganization(configMgr)
if err != nil {
    return err
}
// org is set as current organization
```

### Fly Organization Selection

```go
flyOrgs := []prompts.FlyOrganization{...}
selectedOrg, err := prompts.PromptForFlyOrganization(flyOrgs)
if err != nil {
    return err
}
```

### Authentication Confirmation

```go
confirmed, err := prompts.PromptToAuthenticate()
if err != nil {
    return err
}
if confirmed {
    // Run auth flow
}
```

### Re-Authentication

```go
confirmed, err := prompts.PromptToReAuthenticate("my-org")
if err != nil {
    return err
}
if confirmed {
    // Re-authenticate
}
```

### Generic Confirmation

```go
confirmed, err := prompts.PromptForConfirmation(
    "Delete sprite?",
    "This action cannot be undone.",
)
if err != nil {
    return err
}
```

## Adding New Prompts

When adding a new prompt:

1. **Choose the right file**:
   - Organization-related → `organization.go`
   - Sprite-related → `sprite.go`
   - Auth/confirmation → `auth.go`
   - New category → Create new file

2. **Follow the pattern**:
   ```go
   func PromptForThing() (result, error) {
       var value Type
       
       if err := huh.NewInput(). // or NewSelect, NewConfirm, etc.
           Title("Clear title").
           Description("Helpful description").
           Value(&value).
           Validate(func(v Type) error {
               // Validation logic
           }).
           Run(); err != nil {
           return zero, fmt.Errorf("thing cancelled: %w", err)
       }
       
       return value, nil
   }
   ```

3. **Add validation** where appropriate

4. **Return descriptive errors**

## Testing

Prompts can be tested by:
- Mocking terminal input
- Using accessible mode (non-interactive)
- Setting environment variables

Example:
```bash
ACCESSIBLE=1 sprite create
# Uses simple line-by-line input instead of TUI
```

## Benefits

### ✅ **Organized**
Each category in its own file

### ✅ **Reusable**
Import and use anywhere in commands

### ✅ **Consistent**
Same look and feel across all prompts

### ✅ **Accessible**
Works in all environments (TTY, CI, screen readers)

### ✅ **Maintainable**
Easy to find and update specific prompts

## Summary

The prompts package provides:
- 📁 **Organized structure** by category
- 🎨 **Consistent UI** using huh library
- ♿ **Accessible** for all users
- 🔄 **Reusable** across commands
- ✅ **Validated** user input
- 🧪 **Testable** components

All prompts are part of the `prompts` package and can be imported and used throughout the codebase!


