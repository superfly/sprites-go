package resources

import (
	"math"
	"testing"
	"time"
)

func TestSeriesBasic(t *testing.T) {
	s := NewGaugeSeries(10)

	baseTime := time.Now()
	s.Add(baseTime, 10.0)
	s.Add(baseTime.Add(time.Second), 20.0)
	s.Add(baseTime.Add(2*time.Second), 30.0)

	if s.Count() != 3 {
		t.Errorf("Expected 3 samples, got %d", s.Count())
	}

	latest, ok := s.Latest()
	if !ok {
		t.Fatal("Expected latest sample")
	}
	if latest.Value != 30.0 {
		t.Errorf("Expected latest value 30.0, got %.1f", latest.Value)
	}

	avg, ok := s.Average()
	if !ok {
		t.Fatal("Expected average")
	}
	if avg != 20.0 {
		t.Errorf("Expected average 20.0, got %.1f", avg)
	}
}

func TestSeriesMaxSamples(t *testing.T) {
	s := NewGaugeSeries(3)

	baseTime := time.Now()
	for i := 0; i < 10; i++ {
		s.Add(baseTime.Add(time.Duration(i)*time.Second), float64(i))
	}

	// Should only keep last 3
	if s.Count() != 3 {
		t.Errorf("Expected 3 samples, got %d", s.Count())
	}

	samples := s.Samples()
	if samples[0].Value != 7.0 || samples[1].Value != 8.0 || samples[2].Value != 9.0 {
		t.Errorf("Expected samples [7,8,9], got [%.0f,%.0f,%.0f]",
			samples[0].Value, samples[1].Value, samples[2].Value)
	}
}

func TestSeriesMonotonic(t *testing.T) {
	s := NewCounterSeries(10)

	baseTime := time.Now()

	// Add monotonic counter values (raw values are stored now)
	s.Add(baseTime, 100.0)
	s.Add(baseTime.Add(time.Second), 110.0)   // +10 in 1s
	s.Add(baseTime.Add(2*time.Second), 125.0) // +15 in 1s
	s.Add(baseTime.Add(3*time.Second), 145.0) // +20 in 1s

	// Should have 4 raw counter samples
	if s.Count() != 4 {
		t.Errorf("Expected 4 counter samples, got %d", s.Count())
	}

	samples := s.Samples()
	t.Logf("Raw values: %.1f, %.1f, %.1f, %.1f", samples[0].Value, samples[1].Value, samples[2].Value, samples[3].Value)

	// Check raw values are stored
	if samples[0].Value != 100.0 {
		t.Errorf("Expected first value 100.0, got %.1f", samples[0].Value)
	}
	if samples[3].Value != 145.0 {
		t.Errorf("Expected last value 145.0, got %.1f", samples[3].Value)
	}

	// Test Increase() to get most recent delta
	delta, elapsed, ok := s.Increase()
	if !ok {
		t.Fatal("Expected Increase to succeed")
	}

	t.Logf("Most recent increase: %.1f in %v", delta, elapsed)

	// Most recent increase should be 145 - 125 = 20 in 1 second
	if math.Abs(delta-20.0) > 0.1 {
		t.Errorf("Expected delta 20.0, got %.1f", delta)
	}
	if elapsed != time.Second {
		t.Errorf("Expected elapsed 1s, got %v", elapsed)
	}
}

func TestSeriesMonotonicReset(t *testing.T) {
	s := NewCounterSeries(10)

	baseTime := time.Now()

	s.Add(baseTime, 100.0)
	s.Add(baseTime.Add(time.Second), 110.0)  // +10 in 1s
	s.Add(baseTime.Add(2*time.Second), 5.0)  // Counter reset! 5 < 110
	s.Add(baseTime.Add(3*time.Second), 15.0) // +10 in 1s

	samples := s.Samples()
	if len(samples) != 4 {
		t.Fatalf("Expected 4 samples, got %d", len(samples))
	}

	t.Logf("Raw values: %.1f, %.1f, %.1f, %.1f", samples[0].Value, samples[1].Value, samples[2].Value, samples[3].Value)

	// Check raw values are stored (including the reset)
	if samples[2].Value != 5.0 {
		t.Errorf("Expected reset value 5.0, got %.1f", samples[2].Value)
	}

	// Test Increase() after reset - should handle the decrease properly
	delta, elapsed, ok := s.Increase()
	if !ok {
		t.Fatal("Expected Increase to succeed")
	}

	t.Logf("Most recent increase after earlier reset: %.1f in %v", delta, elapsed)

	// Most recent increase should be 15 - 5 = 10 in 1 second
	if math.Abs(delta-10.0) > 0.1 {
		t.Errorf("Expected delta 10.0, got %.1f", delta)
	}
}

func TestSeriesIncreaseWithReset(t *testing.T) {
	s := NewCounterSeries(10)

	baseTime := time.Now()

	// Simulate a counter that resets
	s.Add(baseTime, 100.0)
	s.Add(baseTime.Add(time.Second), 110.0) // +10

	// Get increase before reset
	delta1, elapsed1, ok1 := s.Increase()
	if !ok1 {
		t.Fatal("Expected first Increase to succeed")
	}
	if math.Abs(delta1-10.0) > 0.1 {
		t.Errorf("Expected delta 10.0 before reset, got %.1f", delta1)
	}
	if elapsed1 != time.Second {
		t.Errorf("Expected elapsed 1s, got %v", elapsed1)
	}

	// Counter resets to near zero
	s.Add(baseTime.Add(2*time.Second), 3.0)

	// Get increase after reset - should detect reset and use new value
	delta2, elapsed2, ok2 := s.Increase()
	if !ok2 {
		t.Fatal("Expected second Increase to succeed")
	}

	t.Logf("Increase after reset: delta=%.1f, elapsed=%v", delta2, elapsed2)

	// After reset (3 < 110), delta should be 3 (the new value)
	if math.Abs(delta2-3.0) > 0.1 {
		t.Errorf("Expected delta 3.0 after reset, got %.1f", delta2)
	}
	if elapsed2 != time.Second {
		t.Errorf("Expected elapsed 1s, got %v", elapsed2)
	}
}

func TestClear(t *testing.T) {
	s := NewGaugeSeries(10)

	baseTime := time.Now()
	s.Add(baseTime, 10.0)
	s.Add(baseTime.Add(time.Second), 20.0)

	if s.Count() != 2 {
		t.Errorf("Expected 2 samples before clear, got %d", s.Count())
	}

	s.Clear()

	if s.Count() != 0 {
		t.Errorf("Expected 0 samples after clear, got %d", s.Count())
	}

	_, ok := s.Latest()
	if ok {
		t.Error("Expected no latest sample after clear")
	}
}
