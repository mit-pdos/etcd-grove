package workqueue_test

import (
	"testing"
	"time"

	"k8s.io/client-go/util/workqueue"
)

// With a base delay of a power of two nanoseconds, the 64-log2(base)'th
// failure gives a backoff of exactly 2^63 ns, which passes the overflow cap
// (backoff > math.MaxInt64, where float64(math.MaxInt64) is 2^63) and converts
// to a negative Duration on amd64.
func TestExponentialWhenAt2to63(t *testing.T) {
	maxDelay := 1000 * time.Second
	r := workqueue.NewTypedItemExponentialFailureRateLimiter[string](time.Nanosecond, maxDelay)
	for i := 0; i <= 63; i++ {
		if d := r.When("x"); d < 0 || d > maxDelay {
			t.Fatalf("When after %d failures = %v, want between 0 and %v", i+1, d, maxDelay)
		}
	}
}
