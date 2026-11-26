// Copyright 2026 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package etcdserver

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/pkg/v3/pbutil"
	"go.etcd.io/etcd/pkg/v3/wait"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/etcdserver/cindex"
	serverstorage "go.etcd.io/etcd/server/v3/storage"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/raft/v3/raftpb"
)

// commitBeforeSaveMember is the cluster's membership backend with one change: before
// the first MustSaveMemberToBackend after arm, it commits the backend (what the
// backend's batch-interval timer does when it fires at that instant) and copies the
// database file, which is what a power loss right after that commit leaves on disk.
type commitBeforeSaveMember struct {
	membership.MembershipBackend
	be      backend.Backend
	path    string
	armed   bool
	imgPath string
}

func (m *commitBeforeSaveMember) MustSaveMemberToBackend(mem *membership.Member) {
	if m.armed {
		m.armed = false
		m.be.ForceCommit()
		copyFile(m.path, m.imgPath)
	}
	m.MembershipBackend.MustSaveMemberToBackend(mem)
}

// copyFile copies a committed database file: bbolt syncs at commit, so its bytes are what
// survives a power loss at that point.
func copyFile(from, to string) {
	b, err := os.ReadFile(from)
	if err != nil {
		panic(err)
	}
	if err := os.WriteFile(to, b, 0o600); err != nil {
		panic(err)
	}
}

type confTestNode struct {
	srv *EtcdServer
	be  backend.Backend
	ci  cindex.ConsistentIndexer
}

// openConfTestNode opens the backend at path as bootstrapBackend does (consistent index
// and hooks wired to it) and raft from snap (nil: an empty log), with a batch interval long enough that the timer never fires
// on its own, loads the membership from it, and builds a server around them.
func openConfTestNode(t *testing.T, lg *zap.Logger, path string, snap *raftpb.Snapshot, wrap func(membership.MembershipBackend, backend.Backend) membership.MembershipBackend) *confTestNode {
	ci := cindex.NewConsistentIndex(nil)
	beHooks := serverstorage.NewBackendHooks(lg, ci)
	bcfg := backend.DefaultBackendConfig(lg)
	bcfg.Path = path
	bcfg.BatchInterval = time.Hour
	bcfg.BatchLimit = 1 << 30
	bcfg.Hooks = beHooks
	be := backend.New(bcfg)
	ci.SetBackend(be)
	schema.CreateMetaBucket(be.BatchTx())

	var mb membership.MembershipBackend = schema.NewMembershipBackend(lg, be)
	if wrap != nil {
		mb = wrap(mb, be)
	}
	cl := membership.NewCluster(lg)
	cl.SetBackend(mb)
	cl.UnsafeLoad()

	srv := &EtcdServer{
		lgMu:         new(sync.RWMutex),
		lg:           lg,
		memberID:     1,
		r:            *realisticRaftNode(lg, 1, snap),
		cluster:      cl,
		w:            wait.New(),
		consistIndex: ci,
		beHooks:      beHooks,
		be:           be,
	}
	be.SetTxPostLockInsideApplyHook(srv.getTxPostLockInsideApplyHook())
	t.Cleanup(func() {
		srv.r.raftNodeConfig.Stop()
		be.Close()
	})
	return &confTestNode{srv: srv, be: be, ci: ci}
}

func addMemberEntry(t *testing.T, index, id uint64) *raftpb.Entry {
	m := membership.NewMember("", types.MustNewURLs([]string{fmt.Sprintf("http://member%d:2380", id)}), "", nil)
	m.ID = types.ID(id)
	ctx, err := json.Marshal(m)
	require.NoError(t, err)
	cc := &raftpb.ConfChange{Type: raftpb.ConfChangeAddNode.Enum(), NodeId: new(id), Context: ctx, Id: new(100 + index)}
	return &raftpb.Entry{
		Index: new(index),
		Term:  new(uint64(1)),
		Type:  raftpb.EntryConfChange.Enum(),
		Data:  pbutil.MustMarshalMessage(cc),
	}
}

// applyConf applies the entries as the apply loop does and returns each conf change's error.
func (n *confTestNode) applyConf(ents []*raftpb.Entry, ep *etcdProgress) []error {
	var chs []<-chan any
	for _, e := range ents {
		var cc raftpb.ConfChange
		pbutil.MustUnmarshalMessage(&cc, e.Data)
		chs = append(chs, n.srv.w.Register(cc.GetId()))
	}
	adv := make(chan struct{}, 1)
	adv <- struct{}{}
	n.srv.apply(ents, ep, adv)
	var errs []error
	for _, ch := range chs {
		errs = append(errs, (<-ch).(*confChangeResponse).err)
	}
	return errs
}

type backendImage struct {
	ci        uint64
	voters    []uint64
	memberIDs []uint64
}

func readImage(lg *zap.Logger, path string) backendImage {
	bcfg := backend.DefaultBackendConfig(lg)
	bcfg.Path = path
	be := backend.New(bcfg)
	defer be.Close()
	ci, _ := schema.ReadConsistentIndex(be.ReadTx())
	tx := be.ReadTx()
	tx.RLock()
	cs := schema.UnsafeConfStateFromBackend(lg, tx)
	tx.RUnlock()
	members, _ := schema.NewMembershipBackend(lg, be).MustReadMembersFromBackend()
	img := backendImage{ci: ci}
	if cs != nil {
		img.voters = append(img.voters, cs.GetVoters()...)
		sort.Slice(img.voters, func(i, j int) bool { return img.voters[i] < img.voters[j] })
	}
	for id := range members {
		img.memberIDs = append(img.memberIDs, uint64(id))
	}
	sort.Slice(img.memberIDs, func(i, j int) bool { return img.memberIDs[i] < img.memberIDs[j] })
	return img
}

// TestConfChangeCommitBetweenSetConfStateAndLockInsideApply: applyConfChange records the
// new ConfState in the backend hooks (SetConfState) before the member write takes the
// batch lock and moves the consistent index (AddMember -> MustSaveMemberToBackend ->
// LockInsideApply). A backend commit in between (the batch-interval timer) makes durable
// a database whose stored ConfState is that of entry k while its consistent index is
// still k-1. The test reaches that image, then restarts from it: the replay reapplies
// entry k, and the result must be the same as without the crash.
func TestConfChangeCommitBetweenSetConfStateAndLockInsideApply(t *testing.T) {
	lg := zaptest.NewLogger(t)
	dir := t.TempDir()
	imgPath := filepath.Join(dir, "crash-image.db")
	e1, e2 := addMemberEntry(t, 1, 1), addMemberEntry(t, 2, 2)

	// Run 1: entry 1 (add member 1) applied and committed; entry 2 (add member 2) applied
	// with the timer's commit firing between SetConfState and the member write.
	var hook *commitBeforeSaveMember
	n := openConfTestNode(t, lg, filepath.Join(dir, "run1.db"), nil, func(mb membership.MembershipBackend, be backend.Backend) membership.MembershipBackend {
		hook = &commitBeforeSaveMember{MembershipBackend: mb, be: be, path: filepath.Join(dir, "run1.db"), imgPath: imgPath}
		return hook
	})
	ep := &etcdProgress{confState: &raftpb.ConfState{}}
	require.Equal(t, []error{nil}, n.applyConf([]*raftpb.Entry{e1}, ep))
	n.be.ForceCommit()
	hook.armed = true
	require.Equal(t, []error{nil}, n.applyConf([]*raftpb.Entry{e2}, ep))
	require.False(t, hook.armed, "the injected commit did not run")

	// The crash image: ConfState of entry 2, consistent index 1, members of entry 1.
	img := readImage(lg, imgPath)
	t.Logf("crash image: consistent index %d, stored ConfState voters %v, members %v", img.ci, img.voters, img.memberIDs)
	require.Equal(t, backendImage{ci: 1, voters: []uint64{1, 2}, memberIDs: []uint64{1}}, img)

	// Run 2: restart from the crash image, raft from a snapshot at index 1 (configuration
	// {1}); the replay hands entry 2 to apply again, above the stored consistent index 1,
	// so it is applied to the backend a second time, on top of the stored ConfState that
	// already holds it.
	snap := &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{
		Index: new(uint64(1)), Term: new(uint64(1)), ConfState: &raftpb.ConfState{Voters: []uint64{1}},
	}}
	n2 := openConfTestNode(t, lg, imgPath, snap, nil)
	require.Equal(t, uint64(1), n2.ci.ConsistentIndex())
	ep2 := &etcdProgress{confState: &raftpb.ConfState{Voters: []uint64{1}}}
	errs := n2.applyConf([]*raftpb.Entry{e2}, ep2)
	t.Logf("replay errors: %v", errs)
	require.Equal(t, []error{nil}, errs, "reapplying the conf change failed")
	require.NotNil(t, n2.srv.cluster.Member(types.ID(2)), "member 2 missing after the replay")
	n2.be.ForceCommit()
	afterPath := filepath.Join(dir, "after-replay.db")
	copyFile(imgPath, afterPath)

	after := readImage(lg, afterPath)
	t.Logf("after the replay: consistent index %d, stored ConfState voters %v, members %v", after.ci, after.voters, after.memberIDs)
	require.Equal(t, backendImage{ci: 2, voters: []uint64{1, 2}, memberIDs: []uint64{1, 2}}, after)
}
