#!/bin/bash

# Exit on error and print commands as they are executed
set -e

# Update the Fly machine with the machine-config.json file
TOKEN=$(fly auth token)
APP="flynet-users-2-scratch"
MACHINE_ID="080ee79b530998"

# This command:
# 1. Gets the auth token from Fly CLI
# 2. Uses jq to create the request body with the config file content
# 3. Sends the update request to the Fly API

# Format the JSON payload properly using jq
JSON_PAYLOAD=$(jq -n --argjson config "$(cat kurt-ide.json)" '{"config": $config}')

curl -X POST \
  "https://api.machines.dev/v1/apps/$APP/machines/$MACHINE_ID" \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d "$JSON_PAYLOAD"

echo "Machine update command sent." 