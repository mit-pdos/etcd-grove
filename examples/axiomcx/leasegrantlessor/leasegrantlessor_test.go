// Package leasegrantlessor holds the Go checks of the axiom review of the lease-grant stage's
// lessor statements (notes/axiom-review/lease-grant-lessor.md): tests only, no Goose project.
package leasegrantlessor

import (
	"testing"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
)

func newLessor(t *testing.T, minTTL int64) lease.Lessor {
	be := backend.NewDefaultBackend(zap.NewNop(), t.TempDir()+"/db")
	t.Cleanup(func() { be.Close() })
	le := lease.NewLessor(zap.NewNop(), be, nil, lease.LessorConfig{MinLeaseTTL: minTTL})
	t.Cleanup(le.Stop)
	return le
}

// TestStandaloneExpiry: a lessor outside any cluster (NewLessor's axiom holds for every lessor),
// promoted, grants a lease of TTL 1 s; the loop sends it on ExpiredLeasesC within ~1.5 s. A
// program that panics on that receive is "proved" not to panic under leasesNoExpiry if the
// premise is read per cluster (this program has none).
func TestStandaloneExpiry(t *testing.T) {
	le := newLessor(t, 0)
	le.Promote(0)
	if _, err := le.Grant(1, 1); err != nil {
		t.Fatal(err)
	}
	select {
	case ls := <-le.ExpiredLeasesC():
		t.Logf("received %d expired lease(s), id %d: a program would panic here", len(ls), ls[0].ID)
	case <-time.After(5 * time.Second):
		t.Fatal("no expiry")
	}
}

// TestExpiryOnlyLater: Grant (primary or not), the minimum TTL, Promote (with and without the
// overlap adjustment), Demote and Renew never set a lease's expiry earlier than the grant's TTL
// from the grant; no operation but Revoke/Recover removes it from the map (the monotone mode).
func TestExpiryOnlyLater(t *testing.T) {
	for _, primary := range []bool{false, true} {
		le := newLessor(t, 5)
		if primary {
			le.Promote(0)
		}
		// many leases, so that Promote runs the overlap adjustment (leaseRevokeRate 1000)
		for id := lease.LeaseID(1); id <= 2000; id++ {
			ttl := int64(600)
			if id%2 == 0 {
				ttl = 1 // raised to the minimum TTL, 5
			}
			if _, err := le.Grant(id, ttl); err != nil {
				t.Fatal(err)
			}
		}
		for round := 0; round < 3; round++ {
			le.Demote()
			le.Promote(time.Duration(round) * time.Second)
			if _, err := le.Renew(3); err != nil {
				t.Fatal(err)
			}
		}
		for id := lease.LeaseID(1); id <= 2000; id++ {
			l := le.Lookup(id)
			if l == nil {
				t.Fatalf("lease %d removed", id)
			}
			min := 600 * time.Second
			if id%2 == 0 {
				min = 5 * time.Second
			}
			if r := l.Remaining(); r < min-time.Second {
				t.Fatalf("lease %d: remaining %v < %v", id, r, min)
			}
		}
		if n := len(le.Leases()); n != 2000 {
			t.Fatalf("Leases: %d", n)
		}
	}
	t.Log("2000 leases, Demote/Promote x3 and Renew, primary and not: every expiry >= TTL from now, none removed")
}
