package lease

import (
	"os"
	"sync"
	"testing"

	"go.uber.org/zap"
)

// TestRevokeSetRangeDeleterRace: Revoke reads le.rd after releasing le.mu, while
// SetRangeDeleter writes it under le.mu. Run with -race. etcd's server sets the
// range deleter once, at the store's construction, and calls Recover and Revoke
// on the apply goroutine, so it never runs them concurrently. Uses
// NewTestBackend, newFakeDeleter, clusterLatest and minLeaseTTL from
// lessor_test.go.
func TestRevokeSetRangeDeleterRace(t *testing.T) {
	lg := zap.NewNop()
	dir, be := NewTestBackend(t)
	defer os.RemoveAll(dir)
	defer be.Close()
	le := newLessor(lg, be, clusterLatest(), LessorConfig{MinLeaseTTL: minLeaseTTL})
	defer le.Stop()
	le.SetRangeDeleter(func() TxnDelete { return newFakeDeleter(be) })
	for i := 1; i <= 100; i++ {
		if _, err := le.Grant(LeaseID(i), 10); err != nil {
			t.Fatal(err)
		}
	}
	var wg sync.WaitGroup
	wg.Add(2)
	go func() {
		defer wg.Done()
		for i := 1; i <= 100; i++ {
			le.SetRangeDeleter(func() TxnDelete { return newFakeDeleter(be) })
		}
	}()
	go func() {
		defer wg.Done()
		for i := 1; i <= 100; i++ {
			if err := le.Revoke(LeaseID(i)); err != nil {
				t.Error(err)
			}
		}
	}()
	wg.Wait()
}
