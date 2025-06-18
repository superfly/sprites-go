# Release Process

This document describes the release process for sprite-env.

## Safety Guarantee

**All releases must pass ALL tests before binaries are built and published.** The release workflow automatically runs the complete test suite and will fail if any test doesn't pass.

## Automated Releases

Releases are automatically created when you push a semantic version tag to the repository. The architecture uses separate workflow files:

1. **Test workflow** (`.github/workflows/test.yml`) - Runs tests for normal development
2. **Release workflow** (`.github/workflows/release.yml`) - Calls the test workflow, then builds binaries

This separation provides:
- Clean separation of concerns
- No code duplication
- Tests must pass before any release
- Easy to maintain and update

### Creating a Release

1. Update the code and ensure all tests pass:
   ```bash
   make test
   ```

2. Create and push a semantic version tag:
   ```bash
   # For a new release
   git tag v1.0.0
   git push origin v1.0.0
   
   # For a pre-release
   git tag v1.0.0-rc.1
   git push origin v1.0.0-rc.1
   ```

3. The GitHub Actions workflow will automatically:
   - Run all tests (unit, integration, model validation, trace validation)
   - **Only proceed if ALL tests pass**
   - Build static binaries for:
     - Linux AMD64
     - Linux ARM64
     - macOS AMD64 (Intel)
     - macOS ARM64 (Apple Silicon)
   - Create compressed archives (.tar.gz) of each binary
   - Generate SHA256 checksums
   - Create a GitHub release with:
     - The binaries as downloadable assets
     - Installation instructions
     - Checksums for verification

### Manual Building

To build release binaries locally:

```bash
# Build all platforms
make release-all VERSION=v1.0.0

# Build specific platforms
make release-linux-amd64 VERSION=v1.0.0
make release-linux-arm64 VERSION=v1.0.0
make release-darwin-amd64 VERSION=v1.0.0
make release-darwin-arm64 VERSION=v1.0.0
```

Binaries will be created in the `dist/` directory.

### Binary Naming Convention

Release binaries follow the pattern: `sprite-env-{os}-{arch}`

- `sprite-env-linux-amd64`
- `sprite-env-linux-arm64`
- `sprite-env-darwin-amd64`
- `sprite-env-darwin-arm64`

### Version Information

The version is embedded in the binary at build time. Users can check the version with:

```bash
sprite-env -version
```

## Release Workflow Details

The release process uses two separate workflow files for clean separation of concerns:

### Test Workflow (`.github/workflows/test.yml`)
- Runs on pushes to main and pull requests
- Can be called by other workflows using `workflow_call`
- Executes the complete test suite:
  - Model validation tests
  - Server unit tests  
  - Server integration tests
  - Trace validation

### Release Workflow (`.github/workflows/release.yml`)
- **Automatically triggers on version tags** (e.g., `v1.0.0`)
- **First calls the test workflow** to run all tests
- **Only proceeds to build and release if ALL tests pass**
- Uses `CGO_ENABLED=0` for static binaries
- Uses `-ldflags="-w -s"` to strip debug information and reduce binary size
- Compresses binaries with tar.gz for smaller downloads
- Generates SHA256 checksums for integrity verification

This clean separation ensures:
1. No duplication of test logic
2. Tests can be updated in one place
3. Release workflow is focused only on building and publishing
4. No release is ever created without passing all tests

## Pre-releases

Tags containing a hyphen (e.g., `v1.0.0-rc.1`, `v1.0.0-beta.2`) are automatically marked as pre-releases in GitHub.