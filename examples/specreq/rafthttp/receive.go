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

	mu        sync.Mutex
	snapIndex uint64 // the index of the last MsgSnap processed (ReqInstallReceived)
}

var _ rh.Raft = (*Receiver)(nil)

// REQ rafthttp/receive: Process is called with a fresh message some member's transport was given
// by Send (or SendSnapshot) with its raft facts (msgSent, its credit), each message at most once:
// a message addressed here is stepped with node.Step's precondition (raftOk hands Process the
// message as msgRecv: fresh, owned with its Entries capacity, as node.Step takes it), whose only
// errors are node errors. (A proposal may still reach a member twice as two messages: raft re-forwards a forwarded
// proposal, each hop with the credit it received; the transport only never duplicates a message.)
// Users: server/etcdserver/server.go:702-722 (EtcdServer.Process: removed sender, To mismatch:
// 403; else node.Step), rafthttp's pipeline and snapshot handlers and the peers' Process loops.
// Assumes: the network is the cluster's (raft's msgSent of what Process gets).
// Specs: raftOk's Process (the receiver side of Transport.Send.spec), node.Step.spec.
func (r *Receiver) Process(ctx context.Context, m *raftpb.Message) error {
	if m.GetTo() != r.Self {
		return httptypes.NewHTTPError(http.StatusForbidden, "cannot process message to mismatch member")
	}
	if m.GetType() == raftpb.MsgSnap {
		r.mu.Lock()
		r.snapIndex = m.GetSnapshot().GetMetadata().GetIndex()
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
// peer listener, beside the server's other peer endpoints.
// Users: server/etcdserver/api/etcdhttp/peer.go:62-79 (NewPeerHandler: /raft, /raft/ and eight
// other patterns), examples/etcd/lease/leasekv_cluster_test.go:35-39 (mounted at / beside lease
// handlers), embed/etcd.go (serving the peer listeners).
// Assumes: l is a listener bound at a peer address of the cluster's network, whose protocol is
// compatible with rafthttp's (raftCompat: rafthttp's under /raft, the other endpoints' elsewhere,
// the mux's 404 allowed); other is a handler of that protocol at /members; a pool of the caller's
// thread tokens is lent to the handler runs (handlerPool).
// Specs: Transport.Handler.spec; net/http's NewServeMux, ServeMux.Handle, Serve; laws
// Http.handlerOk_narrow, Http.mux_handlerOk.
func ReqServePeer(tr *rh.Transport, l net.Listener, other http.Handler) error {
	mux := http.NewServeMux()
	h := tr.Handler()
	mux.Handle("/members", other)
	mux.Handle(rh.RaftPrefix, h)
	mux.Handle(rh.RaftPrefix+"/", h)
	return http.Serve(l, mux)
}

// REQ rafthttp/serve-root: the transport's handler served at the root of the peer listener.
// Users: examples/lib/etcdstart/common.go:172, examples/etcd/restart/restart3.go:79.
// Assumes: as ReqServePeer, the address's protocol rafthttp's (raftCompat_self).
// Specs: Transport.Handler.spec, Serve.spec.
func ReqServeRoot(tr *rh.Transport, l net.Listener) error {
	return http.Serve(l, tr.Handler())
}

// REQ rafthttp/restart-serve: a member's peer address is served again after a restart: the old
// listener closed, a new one bound at the same address, and a new transport of the same member
// (same network) served on it.
// Users: examples/etcd/restart/restart3.go:76-79,102-104; the tests framework's Member.Restart
// (framework/integration/cluster.go:1265-1269).
// Assumes: addr is a peer address of the network (protoAt addr P, P compatible, persistent);
// Listen may fail (the port not yet free): returned.
// Specs: Http's Listen.spec, Listener.Close.spec, Serve.spec; Transport.Handler.spec.
func ReqRestartServe(old, fresh *rh.Transport, addr string) error {
	l1, err := net.Listen("tcp", addr)
	if err != nil {
		return err
	}
	done := make(chan error, 1)
	go func() { done <- http.Serve(l1, old.Handler()) }()
	l1.Close()
	<-done
	l2, err := net.Listen("tcp", addr)
	if err != nil {
		return err
	}
	return http.Serve(l2, fresh.Handler())
}
