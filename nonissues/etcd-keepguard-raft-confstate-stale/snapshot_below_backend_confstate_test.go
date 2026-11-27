// Copyright 2026 The etcd Authors
// SPDX-License-Identifier: Apache-2.0

package etcdserver

import (
	"context"
	"encoding/json"
	"fmt"
	"sort"
	"sync"
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/pkg/v3/wait"
	"go.etcd.io/etcd/server/v3/etcdserver/api"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/etcdserver/cindex"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/mock/mockstorage"
	serverstorage "go.etcd.io/etcd/server/v3/storage"
	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

func confMember(id uint64) *membership.Member {
	return &membership.Member{
		ID:             types.ID(id),
		RaftAttributes: membership.RaftAttributes{PeerURLs: []string{fmt.Sprintf("http://m%d:2380", id)}},
		Attributes:     membership.Attributes{Name: fmt.Sprintf("m%d", id)},
	}
}

// addNodeEntry is the committed entry of etcd's MemberAdd of member id at index i.
func addNodeEntry(t *testing.T, i, term, id uint64) *raftpb.Entry {
	m := confMember(id)
	ctx, err := json.Marshal(&membership.ConfigChangeContext{Member: *m})
	require.NoError(t, err)
	cc := &raftpb.ConfChange{Type: raftpb.ConfChangeAddNode.Enum(), NodeId: new(id), Context: ctx, Id: new(uint64(1000 + i))}
	data, err := proto.Marshal(cc)
	require.NoError(t, err)
	return &raftpb.Entry{Type: raftpb.EntryType_EntryConfChange.Enum(), Index: new(i), Term: new(term), Data: data}
}

func voters(t *testing.T, n raft.Node) []uint64 {
	st := n.Status()
	var vs []uint64
	for id := range st.Config.Voters.IDs() {
		vs = append(vs, id)
	}
	sort.Slice(vs, func(i, j int) bool { return vs[i] < vs[j] })
	return vs
}

// readyOnce handles one Ready as raftNode.start does: snapshot and entries to
// storage, the committed entries to apply, then Advance.
func readyOnce(t *testing.T, n raft.Node, ms *raft.MemoryStorage, apply func([]*raftpb.Entry)) raft.Ready {
	rd := <-n.Ready()
	if !raft.IsEmptySnap(rd.Snapshot) {
		require.NoError(t, ms.ApplySnapshot(rd.Snapshot))
	}
	if !raft.IsEmptyHardState(rd.HardState) {
		require.NoError(t, ms.SetHardState(rd.HardState))
	}
	require.NoError(t, ms.Append(rd.Entries))
	if len(rd.CommittedEntries) > 0 && apply != nil {
		apply(rd.CommittedEntries)
	}
	n.Advance()
	return rd
}

// TestKeptSnapshotLeavesRaftConfStateStale: member 1 restarts with its backend at
// consistent index 7, ahead of its WAL (index 3). Bootstrap gives raft the backend's
// configuration, voters 1..5 (members 4 and 5 were added by entries 6 and 7). The
// leader (2, term 2) sends a snapshot at 5, whose configuration is voters 1..3, and
// then entries 6 and 7. applySnapshot keeps the backend (5 <= 7); the apply loop
// replays 6 and 7 as ApplyV2storeOnly (6, 7 <= 7), so it never calls
// raft's ApplyConfChange. raft's tracker and ep.confState stay at voters 1..3
// while the cluster (and every other member) has voters 1..5; member 1 then wins
// an election with the votes of 1 and 2 only, two of five voters.
func TestKeptSnapshotLeavesRaftConfStateStale(t *testing.T) {
	lg := zaptest.NewLogger(t)
	be, _ := betesting.NewDefaultTmpBackend(t)
	defer betesting.Close(t, be)
	mbe := schema.NewMembershipBackend(lg, be)
	mbe.MustCreateBackendBuckets()
	for id := uint64(1); id <= 5; id++ {
		mbe.MustSaveMemberToBackend(confMember(id))
	}
	cl := membership.NewCluster(lg)
	cl.SetBackend(mbe)
	s, n, ms := newConfGapServer(t, lg, be, cl, 7, &raftpb.ConfState{Voters: []uint64{1, 2, 3, 4, 5}})
	defer n.Stop()
	defer s.kv.Close()
	require.Equal(t, []uint64{1, 2, 3, 4, 5}, voters(t, n), "bootstrap configuration")

	ep := etcdProgress{appliedi: 3, appliedt: 1, diskSnapshotIndex: 3, memorySnapshotIndex: 3,
		confState: &raftpb.ConfState{Voters: []uint64{1, 2, 3, 4, 5}}}
	apply := func(es []*raftpb.Entry) {
		done := make(chan struct{})
		close(done)
		s.applyEntries(&ep, &toApply{entries: es, notifyc: done})
	}

	// The leader's snapshot at 5, configuration 1..3.
	cs5 := &raftpb.ConfState{Voters: []uint64{1, 2, 3}}
	snap5 := &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: new(uint64(5)), Term: new(uint64(2)), ConfState: cs5}}
	require.NoError(t, n.Step(context.TODO(), &raftpb.Message{
		Type: raftpb.MessageType_MsgSnap.Enum(), From: new(uint64(2)), To: new(uint64(1)), Term: new(uint64(2)), Snapshot: snap5,
	}))
	rd := readyOnce(t, n, ms, nil)
	require.False(t, raft.IsEmptySnap(rd.Snapshot), "raft did not accept the snapshot")
	done := make(chan struct{})
	close(done)
	s.applySnapshot(&ep, &toApply{snapshot: rd.Snapshot, notifyc: done})
	require.Same(t, be, s.be, "the keep branch was not taken")
	require.Equal(t, uint64(7), s.consistIndex.ConsistentIndex())

	// The leader then sends entries 6 (add 4) and 7 (add 5), committed.
	require.NoError(t, n.Step(context.TODO(), &raftpb.Message{
		Type: raftpb.MessageType_MsgApp.Enum(), From: new(uint64(2)), To: new(uint64(1)), Term: new(uint64(2)),
		LogTerm: new(uint64(2)), Index: new(uint64(5)), Commit: new(uint64(7)),
		Entries: []*raftpb.Entry{addNodeEntry(t, 6, 2, 4), addNodeEntry(t, 7, 2, 5)},
	}))
	rd = readyOnce(t, n, ms, apply)
	require.Len(t, rd.CommittedEntries, 2, "raft re-delivers entries 6 and 7 after the snapshot")
	require.Equal(t, uint64(7), ep.appliedi)

	require.Equal(t, []uint64{1, 2, 3, 4, 5}, idsOf(cl.VotingMemberIDs()), "cluster members")
	require.Equal(t, []uint64{1, 2, 3}, voters(t, n), "raft's tracker")
	require.Equal(t, []uint64{1, 2, 3}, ep.confState.GetVoters(), "ep.confState")
	// The replay's SetConfState also writes it into the backend's meta, beside
	// consistent index 7: the configuration a merged snapshot at the backend's
	// index reads (createMergedSnapshotMessage) when replayConf does not apply.
	// (This test's backend has no hooks: run the pre-commit hook as etcd's does.)
	btx := be.BatchTx()
	btx.LockOutsideApply()
	s.beHooks.OnPreCommitUnsafe(btx)
	btx.Unlock()
	be.ForceCommit()
	rtx := be.ReadTx()
	rtx.RLock()
	beCS := schema.UnsafeConfStateFromBackend(lg, rtx)
	rtx.RUnlock()
	require.Equal(t, []uint64{1, 2, 3}, beCS.GetVoters(), "backend meta ConfState")

	// A consequence: member 1 campaigns, asks only 2 and 3, and wins with 2's vote.
	require.NoError(t, n.Campaign(context.TODO()))
	rd = readyOnce(t, n, ms, nil)
	var asked []uint64
	for _, m := range rd.Messages {
		if m.GetType() == raftpb.MessageType_MsgVote {
			asked = append(asked, m.GetTo())
		}
	}
	sort.Slice(asked, func(i, j int) bool { return asked[i] < asked[j] })
	require.Equal(t, []uint64{2, 3}, asked, "vote requests")
	require.NoError(t, n.Step(context.TODO(), &raftpb.Message{
		Type: raftpb.MessageType_MsgVoteResp.Enum(), From: new(uint64(2)), To: new(uint64(1)), Term: new(uint64(3)),
	}))
	readyOnce(t, n, ms, nil)
	st := n.Status()
	require.Equal(t, raft.StateLeader, st.RaftState, "leader with 2 of the cluster's 5 voters")
	t.Logf("member 1: leader of term %d with votes {1,2}; cluster voters %v; raft voters %v",
		st.GetTerm(), idsOf(cl.VotingMemberIDs()), voters(t, n))
}

// TestReappliedConfChangesUpdateRaft is the replacing path's counterpart: with the
// backend at the snapshot's index 5 (as after upstream's backend replacement), the
// same entries are applied with ApplyBoth and raft's tracker reaches voters 1..5.
func TestReappliedConfChangesUpdateRaft(t *testing.T) {
	lg := zaptest.NewLogger(t)
	be, _ := betesting.NewDefaultTmpBackend(t)
	defer betesting.Close(t, be)
	mbe := schema.NewMembershipBackend(lg, be)
	mbe.MustCreateBackendBuckets()
	for id := uint64(1); id <= 3; id++ {
		mbe.MustSaveMemberToBackend(confMember(id))
	}
	cl := membership.NewCluster(lg)
	cl.SetBackend(mbe)
	cs5 := &raftpb.ConfState{Voters: []uint64{1, 2, 3}}
	s, n, ms := newConfGapServer(t, lg, be, cl, 5, cs5)
	defer n.Stop()
	defer s.kv.Close()
	ep := etcdProgress{appliedi: 5, appliedt: 2, diskSnapshotIndex: 5, memorySnapshotIndex: 5, confState: cs5}
	apply := func(es []*raftpb.Entry) {
		done := make(chan struct{})
		close(done)
		s.applyEntries(&ep, &toApply{entries: es, notifyc: done})
	}
	require.NoError(t, n.Step(context.TODO(), &raftpb.Message{
		Type: raftpb.MessageType_MsgApp.Enum(), From: new(uint64(2)), To: new(uint64(1)), Term: new(uint64(2)),
		LogTerm: new(uint64(2)), Index: new(uint64(5)), Commit: new(uint64(7)),
		Entries: []*raftpb.Entry{addNodeEntry(t, 6, 2, 4), addNodeEntry(t, 7, 2, 5)},
	}))
	readyOnce(t, n, ms, apply)
	require.Equal(t, []uint64{1, 2, 3, 4, 5}, voters(t, n), "raft's tracker")
	require.Equal(t, []uint64{1, 2, 3, 4, 5}, ep.confState.GetVoters(), "ep.confState")
}

// newConfGapServer returns a server over be at consistent index ci (term 2), its
// raft node started from a storage snapshot whose configuration is cs: at index 3
// when ci > 5 (the crash case: WAL at 3, bootstrap configuration from the backend),
// at 5 otherwise.
func newConfGapServer(t *testing.T, lg *zap.Logger, be backend.Backend, cl *membership.RaftCluster, ci uint64, cs *raftpb.ConfState) (*EtcdServer, raft.Node, *raft.MemoryStorage) {
	tx := be.BatchTx()
	tx.LockOutsideApply()
	schema.UnsafeCreateMetaBucket(tx)
	schema.UnsafeUpdateConsistentIndex(tx, ci, 2)
	tx.Unlock()
	be.ForceCommit()
	cl.Recover(api.UpdateCapability)

	snapi, snapt := uint64(3), uint64(1)
	if ci <= 5 {
		snapi, snapt = 5, 2
	}
	ms := raft.NewMemoryStorage()
	require.NoError(t, ms.ApplySnapshot(&raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: new(snapi), Term: new(snapt), ConfState: cs}}))
	require.NoError(t, ms.SetHardState(&raftpb.HardState{Term: new(uint64(2)), Commit: new(snapi)}))
	n := raft.RestartNode(&raft.Config{ID: 1, ElectionTick: 10, HeartbeatTick: 1, Storage: ms,
		MaxSizePerMsg: 1 << 20, MaxInflightMsgs: 256, Logger: NewRaftLoggerZap(lg)})

	cindexer := cindex.NewConsistentIndex(be)
	r := newRaftNode(raftNodeConfig{lg: lg, Node: n, raftStorage: ms, transport: newPeerTransporter(),
		storage: mockstorage.NewStorageRecorder(t.TempDir())})
	s := &EtcdServer{
		lgMu: new(sync.RWMutex), lg: lg, be: be, consistIndex: cindexer, r: *r, cluster: cl, memberID: 1,
		applyWait: wait.NewTimeList(), stopping: make(chan struct{}), w: wait.New(),
		beHooks: serverstorage.NewBackendHooks(lg, cindexer),
	}
	s.kv = mvcc.New(lg, be, &lease.FakeLessor{}, mvcc.StoreConfig{})
	return s, n, ms
}

func idsOf[T ~uint64](ids []T) []uint64 {
	out := make([]uint64, len(ids))
	for i, id := range ids {
		out[i] = uint64(id)
	}
	sort.Slice(out, func(i, j int) bool { return out[i] < out[j] })
	return out
}
