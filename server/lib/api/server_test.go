package api

// mockSystemState implements the SystemStateMachine interface for testing
type mockSystemState struct {
	fireCalls []struct {
		trigger string
		args    []any
	}
	fireError    error
	currentState interface{}
}

func (m *mockSystemState) MustState() interface{} {
	return m.currentState
}

func (m *mockSystemState) Fire(trigger string, args ...any) error {
	m.fireCalls = append(m.fireCalls, struct {
		trigger string
		args    []any
	}{trigger: trigger, args: args})
	return m.fireError
}
