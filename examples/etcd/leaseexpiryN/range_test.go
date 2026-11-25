package leaseexpiryN

import "testing"

// TestMainRange (rule 38's non-vacuity test for Main's range check, with TestMainRun, which runs
// Main(k) for real at a k drawn from {1, 2, 3, 5, 7}): sizes outside [1, 1000] return at once,
// starting nothing (a member's start would bind its peer address, which TestMainRun then finds free).
func TestMainRange(t *testing.T) {
	Main(0)
	Main(1001)
}
