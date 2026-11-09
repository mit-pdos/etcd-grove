//go:build ignore

// Requirement snippets for raft's log (batch R3): the read-index queue (ReadOnlySafe).
package raft

import (
	"go.etcd.io/raft/v3/quorum"
	pb "go.etcd.io/raft/v3/raftpb"
)

// REQ raftlog/read-index-quorum: a leader queues a read at its commit index and broadcasts the
// queue's position; once a quorum of voters acknowledged a position at or past the read's, the
// read is returned (in queue order, with its message and commit index), exactly once.
// Users: raft.go:2159-2166 (stepLeader MsgReadIndex), raft.go:725 (bcastHeartbeat),
// raft.go:1611-1625 (MsgHeartbeatResp: recvAck, maybeAdvance).
// Assumes: voters is the leader's non-empty voter configuration, the leader among them; every
// acknowledgement is a context this queue produced (followers echo heartbeat contexts), so at most
// the queue's position.
// Specs: newReadOnly.spec, readOnly.addRequest.spec, readOnly.heartbeatCtx.spec,
// readOnly.recvAck.spec, readOnly.maybeAdvance.spec, readOnly.AckedIndex.spec.
func ReqReadIndexQuorum(voters quorum.JointConfig, self uint64, others []uint64, req *pb.Message, commit uint64) {
	ro := newReadOnly(ReadOnlySafe)
	ro.addRequest(commit, req)
	ctx := ro.heartbeatCtx()
	if len(ctx) != 8 {
		panic("read-index: no position to broadcast")
	}
	ro.recvAck(self, ctx)
	for _, id := range others {
		ro.recvAck(id, ctx) // each follower's echo
	}
	rss := ro.maybeAdvance(voters)
	if len(rss) != 1 || rss[0].req != req || rss[0].index != commit {
		panic("read-index: confirmed read lost")
	}
	if again := ro.maybeAdvance(voters); len(again) != 0 {
		panic("read-index: confirmed twice")
	}
	if len(ro.heartbeatCtx()) != 0 {
		panic("read-index: queue not empty")
	}
}
