// Package promotenobucket is the Go evidence for the widened premise of the trust-boundary axiom
// `membership.clusterImageOk_restModel` (route B, 2026-11-25, notes/etcd-dist-plan.md §17.3): a
// committed log may hold promotion conf changes (`AddNode` whose context has `isPromote` true,
// `ccApplyOk`'s promotion disjunct), and the membership buckets, so the cluster image `Recover`
// loads, are what they would be without them, because every saved member is a voter.
//
//   - (a) TestPromoteVoter, first run: the real server (etcdstart.BuildServer, one member) applies
//     a promotion of itself, a voter (EtcdServer.PromoteMember proposes it: its raft progress
//     passes isLearnerReady). applyConfChange (etcdserver/server.go:2036-2050 at the pin
//     6b942d23f) runs ValidateConfigurationChange with shouldApplyV3 (the entry is above the
//     consistent index), which returns ErrMemberNotLearner (api/membership/cluster.go:324-330),
//     logged as "Validation on configuration change failed"; applyConfChange then returns before
//     PromoteMember. The members, members_removed and cluster buckets are byte for byte as before.
//   - (b) TestPromoteVoter, restart: the same data directory, a new server. The rejection set the
//     consistent index (server.go:2045-2048), so the WAL replay applies the promotion with
//     shouldApplyV3 false: ValidateConfigurationChange returns nil at once (cluster.go:307-309)
//     and applyConfChange calls RaftCluster.PromoteMember(id, false), which logs "ignore already
//     promoted member" (cluster.go:526-531) and writes no bucket. The buckets are byte for byte
//     as before the promotion.
//   - (c) TestPromoteVoter: the image read from the backend (MustReadMembersFromBackend's members
//     with their learner flags and peer URLs, the removed ids, ClusterVersionFromBackend,
//     DowngradeInfoFromBackend) after (a) and after (b) equals the one before the promotion.
//   - (d) TestPromoteUnsaved: a promotion of an id not saved yet (a promotion among the boot log's
//     entries, before its member's AddNode is applied) is rejected with ErrIDNotFound
//     (cluster.go:325-327) and writes no bucket; replayed (shouldApplyV3 false), PromoteMember
//     writes none either.
package promotenobucket

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"net"
	"reflect"
	"sort"
	"strings"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/raft/v3/raftpb"
	"go.uber.org/zap"
	"go.uber.org/zap/zaptest/observer"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

// buckets is the contents of the membership buckets (members, members_removed, cluster), in key
// order, as one string.
func buckets(be backend.Backend) string {
	tx := be.ReadTx()
	tx.RLock()
	defer tx.RUnlock()
	var b strings.Builder
	for _, bk := range []backend.Bucket{schema.Members, schema.MembersRemoved, schema.Cluster} {
		fmt.Fprintf(&b, "[%s]", bk.String())
		var kvs []string
		tx.UnsafeForEach(bk, func(k, v []byte) error {
			kvs = append(kvs, fmt.Sprintf("%q=%q", k, v))
			return nil
		})
		sort.Strings(kvs)
		b.WriteString(strings.Join(kvs, ","))
	}
	return b.String()
}

// image is the cluster image Recover loads from the backend: the members (id, peer URLs, learner
// flag), the removed ids, the cluster version and the downgrade record.
func image(be backend.Backend) string {
	mb := schema.NewMembershipBackend(zap.NewNop(), be)
	ms, rm := mb.MustReadMembersFromBackend()
	var ls []string
	for id, m := range ms {
		ls = append(ls, fmt.Sprintf("%v:%v:learner=%v", id, m.PeerURLs, m.IsLearner))
	}
	sort.Strings(ls)
	var rs []string
	for id := range rm {
		rs = append(rs, id.String())
	}
	sort.Strings(rs)
	d, _ := json.Marshal(mb.DowngradeInfoFromBackend())
	return fmt.Sprintf("members %v removed %v version %v downgrade %s", ls, rs,
		mb.ClusterVersionFromBackend(), d)
}

func logged(obs *observer.ObservedLogs, msg string) []observer.LoggedEntry {
	return obs.FilterMessage(msg).All()
}

func TestPromoteVoter(t *testing.T) {
	walarea.ResetFamily(t, "pnb")
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	l.Close()
	peer := types.URLs{{Scheme: "http", Host: l.Addr().String()}}
	cl := types.URLsMap{"pnb-1": peer}
	ctx := context.Background()

	core, obs := observer.New(zap.InfoLevel)
	s, err := etcdstart.BuildServer("pnb-1", peer, "127.0.0.1:33898", cl, "pnb",
		etcdstart.NoSnapCount, etcdstart.NoSnapCatchUp, zap.New(core))
	if err != nil {
		t.Fatal(err)
	}
	s.Start()
	<-s.ReadyNotify()
	// the monitor's cluster version saved, so no other write to the buckets is pending
	for s.ClusterVersion() == nil || !strings.Contains(image(s.Backend()), "version 3.") {
		time.Sleep(50 * time.Millisecond)
	}
	id := s.MemberID()
	bk0, im0 := buckets(s.Backend()), image(s.Backend())
	t.Logf("before: %s", im0)

	// (a) the promotion of a voter, applied with shouldApplyV3
	a0 := s.AppliedIndex()
	cctx, cancel := context.WithTimeout(ctx, 10*time.Second)
	_, err = s.PromoteMember(cctx, uint64(id))
	cancel()
	if !errors.Is(err, membership.ErrMemberNotLearner) {
		t.Fatalf("(a) PromoteMember of the voter %v: %v, want ErrMemberNotLearner", id, err)
	}
	if s.AppliedIndex() <= a0 {
		t.Fatalf("(a) no entry applied (%d -> %d)", a0, s.AppliedIndex())
	}
	var sawReject bool
	for _, e := range logged(obs, "Validation on configuration change failed") {
		f := e.ContextMap()
		if f["shouldApplyV3"] == true && strings.Contains(fmt.Sprint(f["error"]), membership.ErrMemberNotLearner.Error()) {
			sawReject = true
		}
	}
	if !sawReject {
		t.Fatal("(a) applyConfChange did not log the validation's ErrMemberNotLearner with shouldApplyV3")
	}
	if n := len(logged(obs, "promote member")); n != 0 {
		t.Fatalf("(a) PromoteMember(id, true) ran %d times", n)
	}
	bk1, im1 := buckets(s.Backend()), image(s.Backend())
	if bk1 != bk0 {
		t.Fatalf("(a) buckets changed:\n%s\n->\n%s", bk0, bk1)
	}
	if im1 != im0 {
		t.Fatalf("(c) image changed after (a): %s -> %s", im0, im1)
	}
	t.Logf("(a) rejected with ErrMemberNotLearner at index %d; buckets and image unchanged", s.AppliedIndex())
	s.Stop()

	// (b) restart: the WAL replay applies the promotion again, with shouldApplyV3 false
	core2, obs2 := observer.New(zap.InfoLevel)
	s2, err := etcdstart.BuildServer("pnb-1", peer, "127.0.0.1:33898", cl, "pnb",
		etcdstart.NoSnapCount, etcdstart.NoSnapCatchUp, zap.New(core2))
	if err != nil {
		t.Fatal(err)
	}
	s2.Start()
	defer s2.Stop()
	<-s2.ReadyNotify()
	// PromoteMember's no-v3 branch logs no member id (cluster.go:526-531); the log's only promotion
	// is this one
	if n := len(logged(obs2, "ignore already promoted member")); n != 1 {
		t.Fatalf("(b) the replay ran PromoteMember(_, false) %d times, want 1", n)
	}
	if n := len(logged(obs2, "Validation on configuration change failed")); n != 0 {
		t.Fatalf("(b) the replay validated with shouldApplyV3 and failed %d times", n)
	}
	if n := len(logged(obs2, "promote member")); n != 0 {
		t.Fatalf("(b) PromoteMember(id, true) ran %d times", n)
	}
	bk2, im2 := buckets(s2.Backend()), image(s2.Backend())
	if bk2 != bk0 {
		t.Fatalf("(b) buckets changed:\n%s\n->\n%s", bk0, bk2)
	}
	if im2 != im0 {
		t.Fatalf("(c) image changed after (b): %s -> %s", im0, im2)
	}
	t.Logf("(b) replayed with PromoteMember(%v, false); buckets and image unchanged", id)
	t.Logf("(c) image: %s", im2)
}

// promoteCC is the conf change EtcdServer.PromoteMember proposes for id (server.go's
// promoteMember: an AddNode whose context is the ConfigChangeContext with IsPromote).
func promoteCC(t *testing.T, id types.ID) *raftpb.ConfChange {
	ctx, err := json.Marshal(&membership.ConfigChangeContext{
		Member:    membership.Member{ID: id},
		IsPromote: true,
	})
	if err != nil {
		t.Fatal(err)
	}
	ty := raftpb.ConfChangeAddNode
	nid := uint64(id)
	return &raftpb.ConfChange{Type: &ty, NodeId: &nid, Context: ctx}
}

func TestPromoteUnsaved(t *testing.T) {
	be, _ := betesting.NewDefaultTmpBackend(t)
	defer betesting.Close(t, be)
	mb := schema.NewMembershipBackend(zap.NewNop(), be)
	mb.MustCreateBackendBuckets()
	core, obs := observer.New(zap.InfoLevel)
	c := membership.NewCluster(zap.New(core))
	c.SetBackend(mb)
	m := membership.NewMember("pnb-u", types.MustNewURLs([]string{"http://127.0.0.1:2380"}), "pnb", nil)
	cc := promoteCC(t, m.ID)
	bk0, im0 := buckets(be), image(be)

	// (d) with shouldApplyV3: no member saved under the id
	if err := c.ValidateConfigurationChange(cc, membership.ApplyBoth); !errors.Is(err, membership.ErrIDNotFound) {
		t.Fatalf("(d) validation: %v, want ErrIDNotFound", err)
	}
	if b := buckets(be); b != bk0 {
		t.Fatalf("(d) buckets changed: %s -> %s", bk0, b)
	}
	// (d) replayed: validation skipped, PromoteMember(id, false)
	if err := c.ValidateConfigurationChange(cc, membership.ApplyV2storeOnly); err != nil {
		t.Fatalf("(d) validation without v3: %v", err)
	}
	c.PromoteMember(m.ID, membership.ApplyV2storeOnly)
	if len(logged(obs, "ignore already promoted member")) != 1 {
		t.Fatal("(d) PromoteMember(id, false) did not take its no-v3 branch")
	}
	if b, im := buckets(be), image(be); b != bk0 || im != im0 {
		t.Fatalf("(d) buckets or image changed: %s -> %s / %s -> %s", bk0, b, im0, im)
	}

	// and a voter saved by AddMember: the promotion is ErrMemberNotLearner, writing nothing
	c.AddMember(m, membership.ApplyBoth)
	bk1, im1 := buckets(be), image(be)
	if err := c.ValidateConfigurationChange(cc, membership.ApplyBoth); !errors.Is(err, membership.ErrMemberNotLearner) {
		t.Fatalf("validation of a saved voter's promotion: %v, want ErrMemberNotLearner", err)
	}
	c.PromoteMember(m.ID, membership.ApplyV2storeOnly)
	if b, im := buckets(be), image(be); b != bk1 || im != im1 {
		t.Fatalf("buckets or image changed: %s -> %s / %s -> %s", bk1, b, im1, im)
	}
	if !bytes.Contains([]byte(im1), []byte("learner=false")) || reflect.DeepEqual(im0, im1) {
		t.Fatalf("the voter was not saved: %s", im1)
	}
	t.Logf("(d) unsaved id: ErrIDNotFound, nothing written; saved voter: ErrMemberNotLearner, nothing written (%s)", im1)
}
