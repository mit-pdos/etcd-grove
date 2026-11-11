// Package expiredc holds the Go checks of the axiom review of the lessor's expired-leases channel,
// `lessorExpiredC` and its payload `expiredLeases` (notes/axiom-review/expiredc.md): tests only, no
// Goose project.
package expiredc

import (
	"testing"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
)

func newBackend(t *testing.T) backend.Backend {
	be := backend.NewDefaultBackend(zap.NewNop(), t.TempDir()+"/db")
	t.Cleanup(func() { be.Close() })
	return be
}

func newLessor(t *testing.T, be backend.Backend) lease.Lessor {
	le := lease.NewLessor(zap.NewNop(), be, nil, lease.LessorConfig{
		MinLeaseTTL: 0, ExpiredLeasesRetryInterval: 300 * time.Millisecond})
	t.Cleanup(le.Stop)
	return le
}

type sent struct {
	ls   []*lease.Lease
	copy []*lease.Lease
	ids  []lease.LeaseID
}

// collect receives from ExpiredLeasesC for d, checking each slice as it arrives: non-empty, no nil
// element, each ID one of ok's; it keeps a copy of the slice and of its leases' IDs.
func collect(t *testing.T, le lease.Lessor, d time.Duration, ok map[lease.LeaseID]bool) []sent {
	var out []sent
	deadline := time.After(d)
	for {
		select {
		case ls := <-le.ExpiredLeasesC():
			if len(ls) == 0 {
				t.Fatalf("empty slice sent")
			}
			s := sent{ls: ls, copy: append([]*lease.Lease(nil), ls...)}
			for _, l := range ls {
				if l == nil {
					t.Fatalf("nil lease sent")
				}
				if !ok[l.ID] {
					t.Fatalf("lease %d sent, never granted", l.ID)
				}
				s.ids = append(s.ids, l.ID)
			}
			out = append(out, s)
		case <-deadline:
			return out
		}
	}
}

// recheck: every slice received still holds the same pointers, and every lease the same ID.
func recheck(t *testing.T, ss []sent) {
	for i, s := range ss {
		for j := range s.ls {
			if s.ls[j] != s.copy[j] {
				t.Fatalf("slice %d written after the send at %d", i, j)
			}
			if s.ls[j].ID != s.ids[j] {
				t.Fatalf("lease ID changed after the send")
			}
		}
	}
}

// TestExpiredSlices: a promoted lessor, 40 leases of TTL 1 (the revoke rate is unexported: from
// outside the package always 0, defaulted to 1000, so the limit is 500); the loop keeps resending the unrevoked leases (retry 300 ms) for 3 s, interleaved with
// Renew, Demote/Promote, Revoke of some, and Grant of more. Every slice is non-empty, of non-nil
// granted leases, and none is written (nor any lease's ID) after the send.
func TestExpiredSlices(t *testing.T) {
	for _, rate := range []int{1000} {
		le := newLessor(t, newBackend(t))
		le.Promote(0)
		ok := map[lease.LeaseID]bool{}
		for id := lease.LeaseID(1); id <= 40; id++ {
			if _, err := le.Grant(id, 1); err != nil {
				t.Fatal(err)
			}
			ok[id] = true
		}
		if _, err := le.Grant(100, 600); err != nil {
			t.Fatal(err)
		}
		done := make(chan struct{})
		go func() {
			defer close(done)
			time.Sleep(1200 * time.Millisecond)
			// (Renew of an expired lease blocks until it is revoked: renew a live one)
			le.Renew(100)
			le.Demote()
			le.Promote(0)
			for id := lease.LeaseID(2); id <= 10; id++ {
				le.Revoke(id)
			}
		}()
		ss := collect(t, le, 3*time.Second, ok)
		<-done
		time.Sleep(500 * time.Millisecond)
		recheck(t, ss)
		n := 0
		for _, s := range ss {
			n += len(s.ls)
		}
		t.Logf("rate %d: %d slices, %d leases, all non-empty, non-nil, granted, unchanged", rate, len(ss), n)
		if len(ss) == 0 {
			t.Fatal("nothing sent")
		}
	}
}

// TestRecoverEmpties: a promoted lessor with expired leases, Recover onto a fresh backend: the
// expiry notifier keeps the old ids (initAndRecover's Init does not clear it), but expireExists
// looks them up in the new map and skips them, so no old lease is sent after the Recover (once the
// channel's buffer, sent before, is drained).
func TestRecoverEmpties(t *testing.T) {
	le := newLessor(t, newBackend(t))
	le.Promote(0)
	ok := map[lease.LeaseID]bool{}
	for id := lease.LeaseID(1); id <= 5; id++ {
		le.Grant(id, 1)
		ok[id] = true
	}
	time.Sleep(1700 * time.Millisecond)
	le.Recover(newBackend(t), nil)
	for len(le.ExpiredLeasesC()) > 0 {
		<-le.ExpiredLeasesC()
	}
	time.Sleep(600 * time.Millisecond) // a send in flight at the Recover
	for len(le.ExpiredLeasesC()) > 0 {
		<-le.ExpiredLeasesC()
	}
	ss := collect(t, le, 2*time.Second, map[lease.LeaseID]bool{})
	if len(ss) != 0 {
		t.Fatalf("%d slices after Recover", len(ss))
	}
	t.Logf("after Recover onto an empty backend: nothing sent in 2 s")
}

// TestRecoverReloaded: leases reloaded by Recover (a backend another lessor granted them into)
// expire only after a Promote (their expiry is forever until then), and are sent with their IDs.
func TestRecoverReloaded(t *testing.T) {
	be2 := newBackend(t)
	src := newLessor(t, be2)
	ok := map[lease.LeaseID]bool{}
	for id := lease.LeaseID(7); id <= 9; id++ {
		src.Grant(id, 1)
		ok[id] = true
	}
	le := newLessor(t, newBackend(t))
	le.Promote(0)
	le.Recover(be2, nil)
	if ss := collect(t, le, 2*time.Second, map[lease.LeaseID]bool{}); len(ss) != 0 {
		t.Fatalf("reloaded leases sent before a Promote")
	}
	le.Promote(0)
	ss := collect(t, le, 2500*time.Millisecond, ok)
	recheck(t, ss)
	if len(ss) == 0 {
		t.Fatal("reloaded leases never sent after Promote")
	}
	t.Logf("reloaded leases: none before Promote, %d slices after, IDs among the reloaded", len(ss))
}
