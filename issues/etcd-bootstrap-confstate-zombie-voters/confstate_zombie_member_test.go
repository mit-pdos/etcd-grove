// Mechanism check for issues/etcd-bootstrap-confstate-zombie-voters.md (a hazard found by the
// triage of etcd-io/etcd#20967; unconfirmed end to end).
//
// Drop into go.etcd.io/etcd/server/v3/etcdserver (repository etcd-io/etcd, or the fork
// upamanyus/etcd at the pinned revision 107edf7e492a5cd7e8d958ed8a7ac9dbf1ecf81f), then run, from
// the module directory server/:
//
//	go test ./etcdserver/ -run TestBuildConfStateFromV3storeZombieMember -v
//
// Passes at the pin: the ConfState built from the members bucket has the zombie as a voter. This
// shows only the mechanism (bootstrap.go:112 then puts that ConfState into the raft snapshot every
// restart with a WAL starts from); it does not show that a real upgrade reaches a bucket with
// zombies, nor the cluster-level consequence.
package etcdserver

import (
	"slices"
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

func TestBuildConfStateFromV3storeZombieMember(t *testing.T) {
	lg := zaptest.NewLogger(t)
	be, _ := betesting.NewDefaultTmpBackend(t)
	defer betesting.Close(t, be)

	mb := schema.NewMembershipBackend(lg, be)
	mb.MustCreateBackendBuckets()
	// raft's configuration: voters 1, 2, 3 (the members the cluster added through conf changes).
	for i, u := range []string{"http://m1:2380", "http://m2:2380", "http://m3:2380"} {
		mb.MustSaveMemberToBackend(&membership.Member{
			ID:             types.ID(i + 1),
			RaftAttributes: membership.RaftAttributes{PeerURLs: []string{u}},
		})
	}
	// A zombie as in etcd-io/etcd#20967: a member under a new ID with a real member's peer URL, in
	// the members bucket but in neither members_removed nor raft's configuration.
	const zombie = types.ID(0xbeb11f483a7b51c5)
	mb.MustSaveMemberToBackend(&membership.Member{
		ID:             zombie,
		RaftAttributes: membership.RaftAttributes{PeerURLs: []string{"http://m1:2380"}},
	})
	be.ForceCommit()

	cs := buildConfStateFromV3store(lg, be)
	t.Logf("ConfState built from the members bucket: voters %x, learners %x", cs.Voters, cs.Learners)
	if !slices.Contains(cs.Voters, uint64(zombie)) {
		t.Fatalf("zombie %s not among the voters %x", zombie, cs.Voters)
	}
	if len(cs.Voters) != 4 {
		t.Fatalf("voters = %x, want the 3 members and the zombie", cs.Voters)
	}
}
