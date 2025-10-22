#!/bin/sh
#
# JuiceFS wrapper that translates SPRITE environment variables
# to JuiceFS-specific environment variables
#
# JuiceFS expects: ACCESS_KEY and SECRET_KEY
# This script maps from SPRITE_ prefixed vars:
#   SPRITE_S3_ACCESS_KEY -> ACCESS_KEY
#   SPRITE_S3_SECRET_ACCESS_KEY -> SECRET_KEY
#

# Only set ACCESS_KEY if not already set
if [ -z "$ACCESS_KEY" ]; then
    if [ -n "$SPRITE_S3_ACCESS_KEY" ]; then
        export ACCESS_KEY="$SPRITE_S3_ACCESS_KEY"
    fi
fi

# Only set SECRET_KEY if not already set
if [ -z "$SECRET_KEY" ]; then
    if [ -n "$SPRITE_S3_SECRET_ACCESS_KEY" ]; then
        export SECRET_KEY="$SPRITE_S3_SECRET_ACCESS_KEY"
    fi
fi

# Ensure JSON log format for JuiceFS tooling unless overridden
if [ -z "$JUICEFS_LOG_FORMAT" ]; then
    export JUICEFS_LOG_FORMAT="json"
fi

# Execute juicefs with all arguments passed through
exec juicefs "$@"

