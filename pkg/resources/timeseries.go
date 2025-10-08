package resources

import "time"

// Sample represents a single data point
type Sample struct {
	Time  time.Time
	Value float64
}

// Series tracks values over time with optional monotonic counter handling
type Series struct {
	samples    []Sample
	maxSamples int
	monotonic  bool // if true, stores raw counter values and handles resets
}

// NewGaugeSeries creates a time series for gauge metrics (values that can go up or down)
func NewGaugeSeries(maxSamples int) *Series {
	if maxSamples <= 0 {
		maxSamples = 100
	}
	return &Series{
		samples:    make([]Sample, 0, maxSamples),
		maxSamples: maxSamples,
		monotonic:  false,
	}
}

// NewCounterSeries creates a time series for monotonic counter metrics.
// Stores raw counter values and handles counter resets.
func NewCounterSeries(maxSamples int) *Series {
	if maxSamples <= 0 {
		maxSamples = 100
	}
	return &Series{
		samples:    make([]Sample, 0, maxSamples),
		maxSamples: maxSamples,
		monotonic:  true,
	}
}

// Add adds a new sample to the series
// For monotonic counters, this stores the raw counter value
func (s *Series) Add(t time.Time, value float64) {
	s.addSample(Sample{Time: t, Value: value})
}

// addSample adds a sample and maintains the max size
func (s *Series) addSample(sample Sample) {
	s.samples = append(s.samples, sample)
	if len(s.samples) > s.maxSamples {
		// Remove oldest sample
		s.samples = s.samples[1:]
	}
}

// Count returns the number of samples
func (s *Series) Count() int {
	return len(s.samples)
}

// Latest returns the most recent sample
func (s *Series) Latest() (Sample, bool) {
	if len(s.samples) == 0 {
		return Sample{}, false
	}
	return s.samples[len(s.samples)-1], true
}

// Increase returns the most recent increase in value for monotonic counters.
// Returns the delta between the last two samples, handling counter resets.
// If the counter decreased (reset to zero), returns the new value as the increase.
// Also returns elapsed time between samples and whether the operation succeeded.
func (s *Series) Increase() (delta float64, elapsed time.Duration, ok bool) {
	if len(s.samples) < 2 {
		return 0, 0, false
	}

	last := s.samples[len(s.samples)-1]
	prev := s.samples[len(s.samples)-2]

	elapsed = last.Time.Sub(prev.Time)
	if elapsed <= 0 {
		return 0, 0, false
	}

	delta = last.Value - prev.Value

	// Handle counter reset (monotonic counter decreased)
	if delta < 0 {
		// Counter reset to zero, treat the new value as the increase
		delta = last.Value
	}

	return delta, elapsed, true
}

// Samples returns a copy of all samples
func (s *Series) Samples() []Sample {
	result := make([]Sample, len(s.samples))
	copy(result, s.samples)
	return result
}

// Clear removes all samples
func (s *Series) Clear() {
	s.samples = s.samples[:0]
}

// Average returns the average value across all samples
func (s *Series) Average() (float64, bool) {
	if len(s.samples) == 0 {
		return 0, false
	}

	var sum float64
	for _, sample := range s.samples {
		sum += sample.Value
	}

	return sum / float64(len(s.samples)), true
}
