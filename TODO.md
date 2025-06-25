# TODO for Sprite-env Project

## Decisions Needed

### Base Environment
**Ideal**: Ubuntu with functional systemd, version managers for the top 10 languages

**Issues encountered**:
- Systemd logs are impossible to get at in VMs
- ubuntu-s6 is bad, gave up on s6
- ubuntu-openrc seems promising, may be able to give an llm.txt that shows an agent how to create a service
- Can launch without services, it will be fine

### Language Runtimes
**Problem**: Version managers are slow to install in a base image, and bloat the shit out of it (for things that most people won't use)

**Issues encountered**:
- Building during dev + test is really slow
- Tried on GHA, ran for 8 hours and never finished
- Hard problem: "what do we bake into image" vs "what do we distribute a different way"

**Options**:
- Massive base image built with all the languages and package managers
- Readonly JuiceFS layer under the image with all that stuff on it (bake the metadata sqlite into the image, let the rest come from object storage lazily)

---

## Future Enhancements

### Logging and Tracing
**Goal**: Comprehensive logging system for debugging and monitoring
- Add logging and tracing to a local sqlite database 
- Create API endpoint to query logs from the database
- Add a `sprite logs` command for CLI access to logs
- Consider adding tail functionality to `sprite logs` for real-time log streaming
- Store process output, API calls, checkpoint events, and system events

### Language SDKs
**Goal**: Easy programmatic access to sprite functionality from multiple languages

Create SDKs that provide a simple interface like:
```
sprite = sprites.Create("my-sprite");
cmd = sprite.Command("ls -la");
puts(cmd.stdoutSync())
```

**Features needed**:
- Synchronous and asynchronous command execution
- Easy access to stdout/stderr
- Connection management to sprite API
- Multiple language support (Python, Node.js, Go, etc.)
- Proper error handling and timeouts

### LLM Agent Integration  
**Goal**: Make sprite checkpointing accessible to AI agents during execution

- Add an in-sprite checkpoint call that LLM agents can use
- Allow agents to save state at arbitrary points during long-running tasks
- Provide simple API for agents to trigger checkpoints programmatically
- Enable agents to restore to previous checkpoints if needed 