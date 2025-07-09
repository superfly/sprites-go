package main

import (
	"testing"
)

func TestConfigGetOverlayLowerPaths(t *testing.T) {
	// Test priority: OverlayLowerPaths takes precedence over OverlayLowerPath
	config := Config{
		OverlayLowerPath:  "/should/be/ignored",
		OverlayLowerPaths: []string{"/first/priority", "/second/priority"},
	}

	result := config.GetOverlayLowerPaths()
	expected := []string{"/first/priority", "/second/priority"}

	if len(result) != len(expected) {
		t.Errorf("Expected %d paths, got %d", len(expected), len(result))
	}

	for i, path := range expected {
		if i >= len(result) || result[i] != path {
			t.Errorf("Expected path %d to be %s, got %s", i, path, result[i])
		}
	}
}

func TestConfigGetOverlayLowerPathsFallback(t *testing.T) {
	// Test fallback to single path when array is empty
	config := Config{
		OverlayLowerPath:  "/fallback/path",
		OverlayLowerPaths: []string{}, // Empty array
	}

	result := config.GetOverlayLowerPaths()
	expected := []string{"/fallback/path"}

	if len(result) != len(expected) {
		t.Errorf("Expected %d paths, got %d", len(expected), len(result))
	}

	if result[0] != expected[0] {
		t.Errorf("Expected path to be %s, got %s", expected[0], result[0])
	}
}

func TestConfigGetOverlayLowerPathsDefault(t *testing.T) {
	// Test default fallback when both are empty
	config := Config{
		OverlayLowerPath:  "",
		OverlayLowerPaths: []string{}, // Empty array
	}

	result := config.GetOverlayLowerPaths()
	expected := []string{"/mnt/app-image"}

	if len(result) != len(expected) {
		t.Errorf("Expected %d paths, got %d", len(expected), len(result))
	}

	if result[0] != expected[0] {
		t.Errorf("Expected default path to be %s, got %s", expected[0], result[0])
	}
}

func TestConfigGetOverlayLowerPathsNilArray(t *testing.T) {
	// Test fallback to single path when array is nil
	config := Config{
		OverlayLowerPath:  "/fallback/path",
		OverlayLowerPaths: nil, // nil array
	}

	result := config.GetOverlayLowerPaths()
	expected := []string{"/fallback/path"}

	if len(result) != len(expected) {
		t.Errorf("Expected %d paths, got %d", len(expected), len(result))
	}

	if result[0] != expected[0] {
		t.Errorf("Expected path to be %s, got %s", expected[0], result[0])
	}
}

func TestConfigGetOverlayLowerPathsCompletelyEmpty(t *testing.T) {
	// Test default fallback when everything is empty/nil
	config := Config{
		OverlayLowerPath:  "",
		OverlayLowerPaths: nil,
	}

	result := config.GetOverlayLowerPaths()
	expected := []string{"/mnt/app-image"}

	if len(result) != len(expected) {
		t.Errorf("Expected %d paths, got %d", len(expected), len(result))
	}

	if result[0] != expected[0] {
		t.Errorf("Expected default path to be %s, got %s", expected[0], result[0])
	}
}
