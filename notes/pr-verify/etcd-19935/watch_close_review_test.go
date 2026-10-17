// Review tests for etcd#19935 (watcher.Close). Package-internal: uses closedStream and
// watcherWith from watch_close_errors_test.go.
package clientv3

import (
	"context"
	"errors"
	"fmt"
	"testing"
)

// Every stream reports context.Canceled: Close returns nil, whatever the order.
func TestReviewCloseAllCanceled(t *testing.T) {
	for i := 0; i < 200; i++ {
		w := watcherWith(closedStream("a", context.Canceled), closedStream("b", context.Canceled), closedStream("c", nil))
		if err := w.Close(); err != nil {
			t.Fatalf("iteration %d: Close() = %v, want nil", i, err)
		}
	}
}

// Two real errors and a Canceled: both real errors are reported, Canceled is not.
func TestReviewCloseJoinsAllRealErrors(t *testing.T) {
	e1, e2 := fmt.Errorf("e1"), fmt.Errorf("e2")
	for i := 0; i < 200; i++ {
		w := watcherWith(closedStream("a", e1), closedStream("b", context.Canceled), closedStream("c", e2))
		err := w.Close()
		if !errors.Is(err, e1) || !errors.Is(err, e2) || errors.Is(err, context.Canceled) {
			t.Fatalf("iteration %d: Close() = %v, want e1 and e2 joined, without Canceled", i, err)
		}
	}
}

// Behavior change (any errors.Join version): one stream's real error comes back wrapped,
// so `err == e` no longer holds although errors.Is(err, e) does.
func TestReviewCloseSingleErrorIdentity(t *testing.T) {
	e := fmt.Errorf("boom")
	w := watcherWith(closedStream("a", e))
	err := w.Close()
	t.Logf("err == e: %v, errors.Is: %v, type %T", err == e, errors.Is(err, e), err)
	if !errors.Is(err, e) {
		t.Fatalf("Close() = %v, want an error wrapping %v", err, e)
	}
}
