// Package raftnode holds the requirement snippets of raft's node API (batch R1,
// Spec/go_etcd_io/raft/v3/): minimal uses of the patterns etcd's server, rafthttp and this
// repository's examples rely on, each reliance an explicit panic.
package raftnode

import (
	"context"
	"errors"

	"go.etcd.io/raft/v3"
)

// REQ raftnode/propose-errors: Propose returns nil, ErrStopped, ErrProposalDropped or the
// context's error, nothing else (etcd maps exactly these; v3_server.go:1114).
// Users: server/etcdserver/v3_server.go:1114 (processInternalRaftRequestOnce),
// examples/raft/kvdurable/kv.go:776.
// Assumes: n is a running or stopped node of the cluster; the client's proposal update is
// supplied (one-shot credit: rafthttp delivers a message at most once).
// Specs: node.Propose.spec; laws: errs_init.spec, errIs_agree.spec.
func ReqProposeOnce(ctx context.Context, n raft.Node, data []byte) error {
	err := n.Propose(ctx, data)
	if err != nil && !errors.Is(err, raft.ErrStopped) && !errors.Is(err, raft.ErrProposalDropped) &&
		!errors.Is(err, context.Canceled) && !errors.Is(err, context.DeadlineExceeded) {
		panic("propose: unexpected error")
	}
	return err
}

// REQ raftnode/propose-retry: a client may propose the same data again after an error (the
// examples' retry loop): with persistent credits every copy may commit, and each commit fires
// the persistent update once; the client's apply deduplicates by an id in the data.
// Users: examples/raft/kvdurable/kv.go:776, examples/raft/kvreconf.
// Assumes: the cluster was allocated with dup = true (the examples' lossy, duplicating network).
// Specs: node.Propose.spec (the update under □?γ.dup); laws: msgCredit_dup.spec.
func ReqProposeRetry(ctx context.Context, n raft.Node, data []byte) {
	for n.Propose(ctx, data) != nil && ctx.Err() == nil {
	}
}
