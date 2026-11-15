package raftnode

import (
	"context"

	"go.etcd.io/raft/v3"
)

// REQ raftnode/linearizable-read: a read by read index sees every write applied before the read
// was requested: the read state's index is at least the write's index, and once the node has
// applied up to it the state machine answers the read.
// Users: server/etcdserver/read/read.go:236 (a fresh request id per attempt, ErrStopped ends the
// loop), examples/raft/kvdurable/kv.go:811 (cluster-wide unique contexts).
// Assumes: rctx was never used before in the cluster (readCtx_register); writeIndex is the index
// of a write the caller saw applied before calling; states delivers the read states of n's
// Readys (in order) and applied reports the index applied so far.
// Specs: node.ReadIndex.spec, readyChan_recv.spec (readState), node.Advance.spec;
// laws: readCtx_register.spec, readState_fire.spec, readState_registered.spec,
// committedLb_agree.spec.
func ReqLinearizableRead(ctx context.Context, n raft.Node, rctx []byte, writeIndex uint64,
	states <-chan raft.ReadState, applied func() uint64, read func()) {
	if err := n.ReadIndex(ctx, rctx); err != nil {
		return // stopped or the context's error: the caller retries with a fresh context
	}
	for {
		select {
		case rs := <-states:
			if string(rs.RequestCtx) != string(rctx) {
				continue // another read's
			}
			if rs.Index < writeIndex {
				panic("read index below a write applied before the read")
			}
			for applied() < rs.Index {
			}
			read()
			return
		case <-ctx.Done():
			return
		}
	}
}
