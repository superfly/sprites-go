# Trace Validation Files

This directory contains files for validating execution traces against the sprite-env TLA+ specification.

## Files

- **`sprite_env_trace.tla`** - TLA+ trace specification that extends the main sprite-env spec to consume JSON traces
- **`sprite_env_trace.cfg`** - TLC configuration file for running trace validation  
- **`example_trace.ndjson`** - Example trace file showing the expected JSON format

## Usage

1. **Generate a trace** from your instrumented binary (see `../TRACE_VALIDATION.md` for details)

2. **Run validation** from the project root:
   ```bash
   ./validate_trace.py trace-validation/example_trace.ndjson --tla-dir /path/to/tla+/tools/
   ```

3. **For your own traces**:
   ```bash
   ./validate_trace.py your_trace.ndjson --tla-dir /path/to/tla+/tools/
   ```

## Customization

You may need to modify `sprite_env_trace.tla` if you:
- Add new variables to the main specification
- Use complex data structures  
- Need different event handling
- Want to validate additional invariants

See the main `TRACE_VALIDATION.md` for complete documentation. 