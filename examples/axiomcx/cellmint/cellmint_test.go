package cellmint

import "testing"

// TestMain_panics runs Main once and records that it panics (the Snapshot read is 5,
// not 6, so the second check fires).
func TestMainPanics(t *testing.T) {
	defer func() {
		if r := recover(); r == nil {
			t.Fatal("Main did not panic")
		} else {
			t.Logf("Main panicked as expected: %v", r)
		}
	}()
	Main()
}
