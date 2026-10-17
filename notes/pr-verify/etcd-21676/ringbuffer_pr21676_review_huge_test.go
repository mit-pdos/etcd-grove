package cache

import "testing"

// TestReviewEnsureCapacityHugeNonPow2: for a non-power-of-two length the doubling does
// not overflow before reaching minCapacity > 2^62, and make panics instead of hanging.
func TestReviewEnsureCapacityHugeNonPow2(t *testing.T) {
	rb := newRingBuffer(3, func(x int64) int64 { return x })
	defer func() {
		if r := recover(); r != nil {
			t.Logf("ensureCapacity(1<<62+1) on capacity 3 panicked: %v", r)
			return
		}
		t.Fatalf("no panic")
	}()
	rb.ensureCapacity(1<<62 + 1)
}
