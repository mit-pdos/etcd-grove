package rafthttp

import (
	"context"
	"net"
	"net/http"
	"sync"

	httptypes "go.etcd.io/etcd/server/v3/etcdserver/api/etcdhttp/types"
	rh "go.etcd.io/etcd/server/v3/etcdserver/api/rafthttp"
	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/raftpb"
)

// Receiver is a member's Raft as etcd's server is: it refuses a message for another member, and
// steps the others into its node.
type Receiver struct {
	Self uint64
	Node raft.Node

	mu   sync.Mutex
	seen map[string]bool
}

var _ rh.Raft = (*Receiver)(nil)

// REQ rafthttp/receive: Process is called with a fresh message some member's transport was given
// by Send (or SendSnapshot) with its raft facts, each at most once: a message addressed here is
// stepped with node.Step, whose only errors are node errors; a proposal is never delivered twice.
// Users: server/etcdserver/server.go:702-722 (EtcdServer.Process: removed sender, To mismatch:
// 403; else node.Step), rafthttp's pipeline and snapshot handlers and the peers' Process loops.
// Assumes: every proposal's data is unique (etcd's request ids), and raft forwards a proposal at
// most once; the network is the cluster's (raft's msgSent of what Process gets).
// Specs: raftOk's Process (the receiver side of Transport.Send.spec), node.Step.spec.
func (r *Receiver) Process(ctx context.Context, m *raftpb.Message) error {
	if m.GetTo() != r.Self {
		return httptypes.NewHTTPError(http.StatusForbidden, "cannot process message to mismatch member")
	}
	if m.GetType() == raftpb.MsgProp {
		r.mu.Lock()
		if r.seen == nil {
			r.seen = map[string]bool{}
		}
		for _, e := range m.GetEntries() {
			k := string(e.GetData())
			if r.seen[k] {
				panic("receive: a proposal delivered twice")
			}
			r.seen[k] = true
		}
		r.mu.Unlock()
	}
	if err := r.Node.Step(ctx, m); err != nil && err != raft.ErrStopped && ctx.Err() == nil {
		panic("receive: step failed")
	}
	return nil
}

// IsIDRemoved: no member is removed in this snippet.
func (r *Receiver) IsIDRemoved(id uint64) bool { return false }

// ReportUnreachable passes the report to the node.
func (r *Receiver) ReportUnreachable(id uint64) { r.Node.ReportUnreachable(id) }

// ReportSnapshot passes the report to the node.
func (r *Receiver) ReportSnapshot(id uint64, status raft.SnapshotStatus) {
	r.Node.ReportSnapshot(id, status)
}

// REQ rafthttp/serve-peer: the transport's handler serves /raft and its subtree on the member's
// peer listener (beside the server's other peer endpoints).
// Users: server/etcdserver/api/etcdhttp/peer.go:64-65 (NewPeerHandler), embed/etcd.go (serving
// the peer listeners), server/etcdserver/server.go:646 (RaftHandler).
// Assumes: l is bound at a peer address of the cluster's network that this member reserved, with
// a protocol agreeing with rafthttp's under /raft (and allowing the mux's 404 elsewhere).
// Specs: Transport.Handler.spec; net/http's NewServeMux, ServeMux.Handle, Serve.
func ReqServePeer(tr *rh.Transport, l net.Listener) error {
	mux := http.NewServeMux()
	h := tr.Handler()
	mux.Handle(rh.RaftPrefix, h)
	mux.Handle(rh.RaftPrefix+"/", h)
	return http.Serve(l, mux)
}
