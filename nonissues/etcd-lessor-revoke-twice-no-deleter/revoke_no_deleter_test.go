package lease

import (
	"os"
	"testing"

	"go.uber.org/zap"
)

// TestLessorRevokeWithoutRangeDeleter: without a range deleter, Revoke returns
// nil but keeps the lease (the Lessor interface says the lease is revoked), and
// a second Revoke closes revokec again and panics. etcd's server sets the range
// deleter (mvcc.New) before any revocation. Uses NewTestBackend, clusterLatest
// and minLeaseTTL from lessor_test.go.
func TestLessorRevokeWithoutRangeDeleter(t *testing.T) {
	dir, be := NewTestBackend(t)
	defer os.RemoveAll(dir)
	defer be.Close()
	le := newLessor(zap.NewNop(), be, clusterLatest(), LessorConfig{MinLeaseTTL: minLeaseTTL})
	defer le.Stop()
	if _, err := le.Grant(1, 100); err != nil {
		t.Fatal(err)
	}
	if err := le.Revoke(1); err != nil {
		t.Fatal(err)
	}
	if le.Lookup(1) != nil {
		t.Errorf("after Revoke(1) returned nil, the lease is still there")
	}
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("second Revoke(1) panicked: %v", r)
		}
	}()
	if err := le.Revoke(1); err != ErrLeaseNotFound {
		t.Errorf("second Revoke(1) = %v, want ErrLeaseNotFound", err)
	}
}
