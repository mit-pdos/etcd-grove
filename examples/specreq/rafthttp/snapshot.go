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
