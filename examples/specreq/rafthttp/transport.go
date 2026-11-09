// Package rafthttp holds the requirement snippets of etcd's raft transport
// (go.etcd.io/etcd/server/v3/etcdserver/api/rafthttp), batch 2f: how etcd's server uses it.
package rafthttp

import (
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	rh "go.etcd.io/etcd/server/v3/etcdserver/api/rafthttp"
	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	stats "go.etcd.io/etcd/server/v3/etcdserver/api/v2stats"
	"go.etcd.io/raft/v3/raftpb"
)

// Member is a cluster member as the server's membership holds it.
type Member struct {
	ID       types.ID
	PeerURLs []string
}

// REQ rafthttp/start: the server's literal starts (or fails with an error, which the server
// returns); then a remote for each remote and a peer for each other member are added.
// Users: server/etcdserver/server.go:412-438 (NewServer).
// Assumes: r is the server's Raft for member id (raftOk); the local urls and every member's
// PeerURLs parse (types.NewURLs) and name peer addresses of the cluster's network (the closed
// world: they were reserved for rafthttp's protocol); errorc is the server's error channel.
// Specs: Transport.Start.spec, Transport.AddRemote.spec, Transport.AddPeer.spec.
func ReqStartTransport(lg *zap.Logger, id, cid types.ID, urls types.URLs, r rh.Raft,
	ss *snap.Snapshotter, errorc chan error, remotes, members []Member) (*rh.Transport, error) {
	tr := &rh.Transport{
		Logger:      lg,
		DialTimeout: time.Second,
		ID:          id,
		URLs:        urls,
		ClusterID:   cid,
		Raft:        r,
		Snapshotter: ss,
		ServerStats: stats.NewServerStats("", id.String()),
		LeaderStats: stats.NewLeaderStats(lg, id.String()),
		ErrorC:      errorc,
	}
	if err := tr.Start(); err != nil {
		return nil, err
	}
	for _, m := range remotes {
		if m.ID != id {
			tr.AddRemote(m.ID, m.PeerURLs)
		}
	}
	for _, m := range members {
		if m.ID != id {
			tr.AddPeer(m.ID, m.PeerURLs)
		}
	}
	return tr, nil
}

// REQ rafthttp/send: a Ready's messages, the MsgSnaps diverted to the snapshot merger, are handed
// to Send, which returns (whatever the peers' state: unknown targets and full queues drop).
// Users: server/etcdserver/raft.go:250 (leader, before the write), raft.go:329 (follower),
// raft.go:374 (processMessages).
// Assumes: each message was handed out in a Ready of member id's raft node whose update permitted
// sending it (msgSent), with its credit; a MsgApp is raft's (from id, its other fields zero).
// Specs: Transport.Send.spec.
func ReqSendReady(tr *rh.Transport, msgs []*raftpb.Message, snapc chan<- *raftpb.Message) {
	out := make([]*raftpb.Message, 0, len(msgs))
	for _, m := range msgs {
		if m.GetType() == raftpb.MsgSnap {
			select {
			case snapc <- m:
			default:
			}
			continue
		}
		out = append(out, m)
	}
	tr.Send(out)
}

// REQ rafthttp/membership: a committed conf change adds, updates or removes a peer; a snapshot
// replaces every peer by its members. None of these panics.
// Users: server/etcdserver/server.go:2075 (add), 2085 (remove), 2101 (update), 1157-1166
// (applySnapshot).
// Assumes: the transport is not stopped (AddPeer panics after Stop: the server applies no conf
// change after its raft node stopped); the URLs as in ReqStartTransport.
// Specs: Transport.AddPeer.spec, Transport.UpdatePeer.spec, Transport.RemovePeer.spec,
// Transport.RemoveAllPeers.spec.
func ReqMembership(tr *rh.Transport, self types.ID, add, upd Member, rm types.ID, snapMembers []Member) {
	tr.AddPeer(add.ID, add.PeerURLs)
	tr.UpdatePeer(upd.ID, upd.PeerURLs)
	tr.RemovePeer(rm)
	tr.RemovePeer(rm) // a second removal is a no-op ("etcd may remove a member again on startup")
	tr.RemoveAllPeers()
	for _, m := range snapMembers {
		if m.ID != self {
			tr.AddPeer(m.ID, m.PeerURLs)
		}
	}
}

// REQ rafthttp/connected: ActiveSince and ActivePeers are health heuristics: they return (any
// time; a non-negative count).
// Users: server/etcdserver/util.go:52-100 (isConnectedSince, numConnectedSince,
// longestConnected), server.go:504 (adjustTicks), server.go:1655 (mayRemoveMember).
// Assumes: nothing.
// Specs: Transport.ActiveSince.spec, Transport.ActivePeers.spec.
func ReqConnected(tr *rh.Transport, ids []types.ID, since time.Time) int {
	n := 0
	for _, id := range ids {
		if t := tr.ActiveSince(id); !t.IsZero() && t.Before(since) {
			n++
		}
	}
	if tr.ActivePeers() < 0 {
		panic("connected: negative peer count")
	}
	return n
}

// REQ rafthttp/stop: the test hooks pause and resume traffic; Stop stops the transport, after
// which sends and removals are harmless no-ops.
// Users: server/etcdserver/server.go:2197-2210 (CutPeer, MendPeer), raft.go:449-456
// (pauseSending, resumeSending), raft.go:440 (onStop).
// Assumes: no AddPeer after Stop (trRunning).
// Specs: Transport.CutPeer.spec, Transport.MendPeer.spec, Transport.Pause.spec,
// Transport.Resume.spec, Transport.Stop.spec, Transport.Send.spec, Transport.RemovePeer.spec.
func ReqStop(tr *rh.Transport, id types.ID) {
	tr.CutPeer(id)
	tr.MendPeer(id)
	tr.Pause()
	tr.Resume()
	tr.Stop()
	tr.Send(nil)
	tr.RemovePeer(id)
}
