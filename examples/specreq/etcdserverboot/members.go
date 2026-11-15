package etcdserverboot

import (
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// Go test of a trusted model (not a proof obligation: the functions it calls are trusted, or have
// no spec here); run it to check the model against the code.
// REQ etcdserverboot/members: the apply thread's writes and the request path's reads of the
// membership view agree: a member added is listed (once), a member removed is not listed and stays
// removed, the local member's learner flag is its record's.
// Users: apply (applyConfChange: AddMember, RemoveMember at shouldApplyV3), the request path
// (MemberList: Members; Process: IsIDRemoved; the interceptors: IsMemberExist, IsLearner).
// Assumes: be is an open backend; the cluster of the initial map has two distinct non-zero ids.
// Specs: RaftCluster.AddMember.spec, RemoveMember.spec, Members.spec, IsIDRemoved.spec,
// IsMemberExist.spec, IsLocalMemberLearner.spec, SetBackend.spec; laws: clusterSt_excl.
func ReqMembers(lg *zap.Logger, be backend.Backend, token string, urls types.URLsMap,
	newPeer types.URLs) {
	cl, err := membership.NewClusterFromURLsMap(lg, token, urls)
	if err != nil {
		return
	}
	mb := schema.NewMembershipBackend(lg, be)
	mb.MustCreateBackendBuckets()
	cl.SetBackend(mb)
	n := len(cl.Members())

	now := time.Now()
	m := membership.NewMember("new", newPeer, token, &now)
	cl.AddMember(m, true)
	if len(cl.Members()) != n+1 || !cl.IsMemberExist(m.ID) {
		panic("members: an added member not listed")
	}
	cl.RemoveMember(m.ID, true)
	if len(cl.Members()) != n || cl.IsMemberExist(m.ID) || !cl.IsIDRemoved(m.ID) {
		panic("members: a removed member listed, or not recorded as removed")
	}
	_ = cl.IsLocalMemberLearner() // no panic, also for a local member not in the view
}
