package tests

import "testing"

func TestIntegration(t *testing.T) {
	// Run predefined tests first
	t.Run("PredefinedTests", func(t *testing.T) {
		RunTests(t)
	})

	// Then run dynamic tests
	t.Run("DynamicScenarios", func(t *testing.T) {
		RunDynamicTests(t)
	})
}
