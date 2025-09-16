#!/bin/bash
# Test script to demonstrate --update-base functionality

# Colors for output
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo -e "${BLUE}=== Sprite-env Deploy with Base Image Updates ===${NC}"
echo

# Check for required environment variables
if [ -z "$FLY_APP_NAME" ]; then
    echo -e "${YELLOW}Warning: FLY_APP_NAME not set${NC}"
    echo "Usage: FLY_APP_NAME=your-app ./test-update-base.sh"
    exit 1
fi

if [ -z "$SPRITE_HTTP_API_TOKEN" ]; then
    echo -e "${YELLOW}Warning: SPRITE_HTTP_API_TOKEN not set${NC}"
    echo "This is required for the sprite service to function"
    exit 1
fi

echo -e "${GREEN}Configuration:${NC}"
echo "  App Name: $FLY_APP_NAME"
echo "  API Token: ${FLY_API_TOKEN:+[SET]}"
echo "  Sprite Token: ${SPRITE_HTTP_API_TOKEN:+[SET]}"
echo

# Build the deploy command if not already built
if [ ! -f "./deploy" ]; then
    echo -e "${BLUE}Building deploy command...${NC}"
    go build -o deploy deploy.go
fi

# Run with --update-base flag
echo -e "${BLUE}Running deploy with --update-base flag...${NC}"
echo "This will:"
echo "  1. Build and push main app image"
echo "  2. Build and push Ubuntu base image (with -ubuntu suffix)"
echo "  3. Build and push languages image (with -languages suffix)"
echo "  4. Update volume mounts in machine config"
echo

# Uncomment to actually run the deployment
# ./deploy --update-base

# Show what the command would do
echo -e "${YELLOW}Command that would be executed:${NC}"
echo "./deploy --update-base"
echo
echo "To run the actual deployment, uncomment the command in this script"
