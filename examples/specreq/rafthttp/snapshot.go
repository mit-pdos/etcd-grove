package rafthttp

import (
	"io"

	rh "go.etcd.io/etcd/server/v3/etcdserver/api/rafthttp"
	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	"go.etcd.io/raft/v3/raftpb"
)

// REQ rafthttp/merged-snapshot: SendSnapshot of a merged message closes it exactly once, so the
// sender's wait on CloseNotify ends (once the send ends); the receiver gets the message with its
// database saved first.
// Users: server/etcdserver/server.go:1874-1905 (sendMergedSnap: SendSnapshot, then a goroutine
// waiting on CloseNotify to release the inflight snapshot), snapshot_merge.go:32-53.
// Assumes: m is a MsgSnap a node handed out (msgSent, its credit), its snapshot replaced by the
// server's (raft's msgSent_replaceSnap); every complete stream of rc is an image of the committed
// state at the snapshot's index (snapImg); size is rc's length.
// Specs: Transport.SendSnapshot.spec; snap's NewMessage and CloseNotify (2e).
func ReqSendMergedSnapshot(tr *rh.Transport, m *raftpb.Message, rc io.ReadCloser, size int64) bool {
	merged := snap.NewMessage(m, rc, size)
	tr.SendSnapshot(merged)
	return <-merged.CloseNotify()
}

// REQ rafthttp/install-received: once a MsgSnap was processed, its database file is in the
// snapshotter's directory (rafthttp saved it before Process), so the apply thread finds it by
// index.
// Users: server/etcdserver/server.go:1068-1071 (applySnapshot: OpenSnapshotBackend, which panics
// if <index>.snap.db is missing), rafthttp's snapshot handler (http.go:275, SaveDBFrom before
// Process).
// Assumes: the network's dbIn i is the server's "a file of index i is in the directory until the
// apply thread installs an index >= i" (its invariant over snap's snapDbs); r processed a MsgSnap
// of index i and nothing was installed or released since.
// Specs: Transport.Handler.spec (snapshotHandler: saveOk's update fired, then Process with dbIn),
// Snapshotter.DBFilePath (2e).
func ReqInstallReceived(r *Receiver, ss *snap.Snapshotter) string {
	r.mu.Lock()
	i := r.snapIndex
	r.mu.Unlock()
	if i == 0 {
		return ""
	}
	fn, err := ss.DBFilePath(i)
	if err != nil {
		panic("install: received snapshot's database missing")
	}
	return fn
}
