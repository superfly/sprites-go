# syntax=docker/dockerfile:1

# Build stage
FROM golang:1.24-alpine AS builder

# Install build dependencies
RUN apk add --no-cache git

WORKDIR /build

# Copy go mod files
COPY go.mod go.sum ./
RUN go mod download

# Copy source code
COPY . .

# Build the binary with version from build arg
ARG VERSION=dev
RUN CGO_ENABLED=0 GOOS=linux go build \
    -ldflags="-w -s -X main.version=${VERSION}" \
    -o sprite-env .

# Runtime stage
FROM alpine:3.19

# Install runtime dependencies
RUN apk add --no-cache ca-certificates bash

# Create non-root user
RUN addgroup -g 1000 sprite && \
    adduser -u 1000 -G sprite -s /bin/sh -D sprite

WORKDIR /app

# Copy binary from builder
COPY --from=builder /build/sprite-env /app/sprite-env

# Set ownership
RUN chown -R sprite:sprite /app

# Switch to non-root user
USER sprite

# Expose the default port (you may need to adjust this based on your config)
EXPOSE 8080

# Set the entrypoint
ENTRYPOINT ["/app/sprite-env"]