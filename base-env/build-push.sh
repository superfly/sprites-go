#!/bin/sh

DOCKER_REPO="flyio/app-storage"
PLATFORM="linux/amd64"
TAG="latest"

echo "Building main Docker image for $PLATFORM..."
docker build --platform $PLATFORM -t $DOCKER_REPO:$TAG .

if [ $? -eq 0 ]; then
    echo "Main build successful. Pushing to Docker Hub..."
    docker push $DOCKER_REPO:$TAG
    
    if [ $? -eq 0 ]; then
        echo "Successfully pushed $DOCKER_REPO:$TAG"
    else
        echo "Failed to push main image"
        exit 1
    fi
else
    echo "Main build failed"
    exit 1
fi
