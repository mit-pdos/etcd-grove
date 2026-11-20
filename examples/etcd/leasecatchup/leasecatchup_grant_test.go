package leasecatchup

// lease-mono3 step 2 (notes/lease-mono3-plan.md, "Step 2 Scope", S2.2's Go test): on three members
// whose ids are distinct in their 15 low bits (`leaseIdsApart`, cluster3.StartCluster's premise in
// the revocable lease mode), grants with no ID through every member, followers included, are
// ordinary: each gets a lease ID of its member's generator (the member id's 15 low bits in bits
// 48-62), no two collide, every member lists all of them, and a revocation through any member
// removes the lease at every member. issues/etcd-lease-id-mask-member-prefix.md shows the failure
// when the premise does not hold.
//
// One run per process: the members' listeners outlive HardStop, so a second run in the same
// process (-count=2) cannot start its cluster. Measured 2026-11-14: 20 of 20 runs passed, each in its
// own process (the leader was member 1 eleven times, member 2 seven, member 3 twice).

import (
	"context"
	"strconv"
	"testing"
	"time"

	"go.uber.org/zap"

	clientv3 "go.etcd.io/etcd/client/v3"

	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

const grantRounds = 10

func TestGrantEveryMember(t *testing.T) {
	t.Chdir(t.TempDir())
	cfg := configAt(24600, "lcgrant")
	walarea.Reset(t, cfg.Name1, cfg.Name2, cfg.Name3) // the members' WAL areas (wal-link P2)
	// the configuration's ids, and the premise on them
	var low15 [3]uint64
	seen := map[uint64]bool{}
	for i, s := range memberIDsOf(t, cfg) {
		id, err := strconv.ParseUint(s, 16, 64)
		if err != nil {
			t.Fatal(err)
		}
		low15[i] = id & 0x7fff
		t.Logf("member %d: id %s, low 15 bits %#x", i+1, s, low15[i])
		if seen[low15[i]] {
			t.Fatalf("configuration violates leaseIdsApart: low 15 bits %#x repeated", low15[i])
		}
		seen[low15[i]] = true
	}
	srvs, _, ok := cluster3.StartCluster(cfg, zap.NewNop())
	if !ok {
		t.Fatal("StartCluster failed")
	}
	t.Cleanup(func() {
		for _, s := range srvs {
			s.HardStop()
		}
	})
	var clis [3]*clientv3.Client
	for i, a := range []string{cfg.Client1, cfg.Client2, cfg.Client3} {
		c, err := etcdstart.NewClients([]string{a}, zap.NewNop())
		if err != nil {
			t.Fatal(err)
		}
		t.Cleanup(func() { c.Close() })
		clis[i] = c
	}
	// wait (bounded) for a leader, so that grants and the revocation below are known to go
	// through followers
	leader := -1
	for p := 0; p < polls && leader < 0; p++ {
		for i, s := range srvs {
			if s.Leader() == s.MemberID() {
				leader = i
			}
		}
		if leader < 0 {
			time.Sleep(pollDelay)
		}
	}
	if leader < 0 {
		t.Fatal("no leader")
	}
	t.Logf("leader: member %d", leader+1)

	// grants with no ID, interleaved across the members
	by := map[clientv3.LeaseID]int{}
	var first [3]clientv3.LeaseID
	for r := 0; r < grantRounds; r++ {
		for i, c := range clis {
			g, err := grant(c)
			if err != nil {
				t.Fatalf("round %d: grant through member %d: %v", r, i+1, err)
			}
			if j, dup := by[g.ID]; dup {
				t.Fatalf("lease %x granted through members %d and %d", int64(g.ID), j+1, i+1)
			}
			if p := uint64(g.ID) >> 48; p != low15[i] {
				t.Fatalf("lease %x through member %d: bits 48-62 %#x, not the member's %#x",
					int64(g.ID), i+1, p, low15[i])
			}
			by[g.ID] = i
			if r == 0 {
				first[i] = g.ID
			}
		}
	}
	// every member lists every lease (a follower's listing is its own lessor's: poll until applied)
	listsAll := func(i int, want func(clientv3.LeaseID) bool) bool {
		for p := 0; p < polls; p++ {
			ls, err := leases(clis[i])
			if err == nil {
				got := map[clientv3.LeaseID]bool{}
				for _, l := range ls.Leases {
					got[l.ID] = true
				}
				okAll := true
				for id := range by {
					if got[id] != want(id) {
						okAll = false
					}
				}
				if okAll {
					return true
				}
			}
			time.Sleep(pollDelay)
		}
		return false
	}
	for i := range clis {
		if !listsAll(i, func(clientv3.LeaseID) bool { return true }) {
			t.Fatalf("member %d does not list all %d leases", i+1, len(by))
		}
	}
	// revoke member 1's first lease through a follower other than member 1 (member 2, or member 3
	// when member 2 leads)
	via := 1
	if leader == 1 {
		via = 2
	}
	gone := first[0]
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err := clis[via].Lease.Revoke(ctx, gone)
	cancel()
	if err != nil {
		t.Fatalf("revoke %x through member %d: %v", int64(gone), via+1, err)
	}
	for i := range clis {
		if !listsAll(i, func(id clientv3.LeaseID) bool { return id != gone }) {
			t.Fatalf("member %d: after the revocation of %x through member %d, its listing is not "+
				"the other leases", i+1, int64(gone), via+1)
		}
	}
	t.Logf("%d leases granted through all three members, distinct; %x revoked through member %d",
		len(by), int64(gone), via+1)
}
