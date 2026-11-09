//go:build ignore

// Requirement snippets for etcd's raft node driver (batch 2d): what the request path, the read
// loop and the transport rely on. In package etcdserver (unexported members).
package etcdserver

import (
	"context"

	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/raftpb"
)

// REQ etcdserverapply/read-index: a read context passed to ReadIndex comes back on ReadState with
// an index at which the cluster confirmed the read (R1's readState), and only registered contexts
// come back.
// Users: server/etcdserver/read/read.go (requestCurrentIndex: s.r.ReadIndex, <-s.r.ReadState()).
// Assumes: rctx was registered with raft (readCtx_register, the server's), fresh.
// Specs: raftNode.ReadIndex.spec, raftNode.ReadState.spec, readStateC_recv; R1's readState_fire.
func ReqReadIndex(ctx context.Context, r *raftNode, rctx []byte) uint64 {
	if err := r.ReadIndex(ctx, rctx); err != nil {
		return 0
	}
	select {
	case rs := <-r.ReadState():
		return rs.Index
	case <-ctx.Done():
		return 0
	}
}

// REQ etcdserverapply/propose: the request path's proposal: nil, ErrStopped, ErrProposalDropped or
// the context's error (R1's propErr); the entry may commit even after an error.
// Users: server/etcdserver/v3_server.go (processInternalRaftRequestOnce).
// Assumes: the proposal update (2c's) is supplied.
// Specs: raftNode.Propose.spec.
func ReqPropose(ctx context.Context, r *raftNode, data []byte) {
	err := r.Propose(ctx, data)
	if err != nil && err != raft.ErrStopped && err != raft.ErrProposalDropped && ctx.Err() == nil {
		panic("propose: unexpected error")
	}
}

// REQ etcdserverapply/process: the transport steps each message it delivers into the member's raft
// node; a message to another member or from a removed one is refused with an error, never a
// panic.
// Users: server/etcdserver/api/rafthttp (stream, pipeline, snapshot handlers: Raft.Process).
// Assumes: m was sent by a node of the cluster (msgSent, msgCredit: 2f's delivery).
// Specs: EtcdServer.Process.spec, raftNode.Step.spec.
func ReqProcess(ctx context.Context, s *EtcdServer, m *raftpb.Message) {
	_ = s.Process(ctx, m)
}

// REQ etcdserverapply/driver-loop: the driver's loop runs and stops: after stop() the node is
// stopped and the WAL closed (the member's durable state returned for a restart).
// Users: server/etcdserver/server.go:808 (run: s.r.start), 807 (s.r.stop in run's shutdown).
// Assumes: r was placed by NewServer (rnInit_place), its loop not started yet.
// Specs: raftNode.start.spec, raftNode.stop.spec, raftNode.onStop.spec.
func ReqDriverLoop(r *raftNode, rh *raftReadyHandler) {
	r.start(rh)
	r.stop()
	if _, err := r.raftStorage.FirstIndex(); err != nil {
		panic("driver-loop: storage unreadable after stop")
	}
}

// REQ etcdserverapply/write-before-send: a follower's messages (its acknowledgements) leave only
// after the batch's hard state and entries were saved; a leader's may leave before.
// Users: server/etcdserver/raft.go:240-306.
// Assumes: rd is a Ready of r's node; islead its role after rd.
// Specs: raftNode.start.spec (R1's readyEnter fired at the WAL's Save; readyCheck for the leader).
func ReqWriteBeforeSend(r *raftNode, rd raft.Ready, islead bool) {
	if islead {
		r.transport.Send(r.processMessages(rd.Messages))
	}
	if err := r.storage.Save(rd.HardState, rd.Entries); err != nil {
		panic("write-before-send: save failed")
	}
	if !islead {
		r.transport.Send(r.processMessages(rd.Messages))
	}
}
