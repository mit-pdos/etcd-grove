// Reproduction for issues/etcd-membership-attrset-unknown-member-panic.md (etcd-io/etcd#16002).
//
// Drop into go.etcd.io/etcd/server/v3/etcdserver/api/membership (repository etcd-io/etcd, or the
// fork upamanyus/etcd at the pinned revision 107edf7e492a5cd7e8d958ed8a7ac9dbf1ecf81f), then run,
// from the module directory server/:
//
//	go test ./etcdserver/api/membership/ -run TestUpdateAttributesUnknownMemberPanics -v
//
// Passes at the pin: UpdateAttributes panics ("failed to update; member unknown").
package membership

import (
	"testing"

	"go.etcd.io/etcd/client/pkg/v3/types"
)

// A ClusterMemberAttrSet for a member id that is neither a member nor removed panics every
// member that applies it (RaftCluster.UpdateAttributes, cluster.go:482).
func TestUpdateAttributesUnknownMemberPanics(t *testing.T) {
	c := newTestCluster(t, []*Member{newTestMember(1, nil, "", nil)})
	defer func() {
		if r := recover(); r == nil {
			t.Fatal("expected a panic")
		} else {
			t.Logf("panicked: %v", r)
		}
	}()
	c.UpdateAttributes(types.ID(0xbeb11f483a7b51c5), Attributes{Name: "x"}, true)
}
