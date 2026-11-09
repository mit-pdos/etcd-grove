package raftnode

import (
	"context"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

// REQ raftnode/deliver: a transport steps each message a node of the cluster sent, at the member it
// is addressed to, at most once (or any number of times with persistent credits); it reports a
// failed send. Step's error is a node error only.
// Users: server/etcdserver/server.go:721 (EtcdServer.Process, from rafthttp's stream and pipeline
// handlers), server/etcdserver/server.go:726 (ReportUnreachable, from rafthttp's peers),
// examples/raft/kvdurable/cluster.go:387-394.
// Assumes: m was handed out in a Ready of a node of the cluster whose update permitted sending it
// (msgSent), with its credit; dst is the node m.To names; ok says the network delivered it.
// Specs: node.Step.spec, node.ReportUnreachable.spec; laws: msgCredit_intro.spec, msgCredit_dup.spec.
func ReqDeliver(ctx context.Context, src, dst raft.Node, m *pb.Message, ok bool) {
	if !ok {
		src.ReportUnreachable(m.GetTo())
		return
	}
	if err := dst.Step(ctx, m); err != nil && err != raft.ErrStopped && ctx.Err() == nil {
		panic("step: unexpected error")
	}
}

// REQ raftnode/merged-snapshot: etcd's leader sends a MsgSnap whose snapshot it replaces by its
// own at its applied index (createMergedSnapshotMessage), and reports the send's fate.
// Users: server/etcdserver/snapshot_merge.go:32-53, server/etcdserver/api/rafthttp/snapshot_sender.go:118-128.
// Assumes: m is a MsgSnap handed out to the leader src; (index, term, cs) is a snapshot made of the
// committed log at the leader's applied index index ≥ m's snapshot's (snap_make), with term its
// last entry's and cs its configuration.
// Specs: node.Step.spec, node.ReportSnapshot.spec; laws: msgSent_snap.spec, msgSent_replaceSnap.spec.
func ReqSendSnapshot(ctx context.Context, src, dst raft.Node, m *pb.Message, index, term uint64,
	cs *pb.ConfState, ok bool) {
	if m.GetType() != pb.MsgSnap {
		return
	}
	if m.GetSnapshot().GetMetadata().GetIndex() > index {
		panic("merged snapshot older than raft's")
	}
	m.Snapshot = &pb.Snapshot{Metadata: &pb.SnapshotMetadata{
		Index: proto.Uint64(index), Term: proto.Uint64(term),
		ConfState: proto.Clone(cs).(*pb.ConfState)}}
	if !ok {
		src.ReportUnreachable(m.GetTo())
		src.ReportSnapshot(m.GetTo(), raft.SnapshotFailure)
		return
	}
	_ = dst.Step(ctx, m)
	src.ReportSnapshot(m.GetTo(), raft.SnapshotFinish)
}
