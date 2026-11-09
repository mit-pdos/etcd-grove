package raftnode

import (
	"context"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

// Durable is what a client makes durable before relying on a Ready (etcd's WAL and snapshotter,
// the examples' file). Its implementation is the client's; raft's spec hands the client the
// update to fire at Save's commit point.
type Durable interface {
	SaveSnap(snap *pb.Snapshot)
	Save(hs *pb.HardState, ents []*pb.Entry)
}

// REQ raftnode/ready-loop: the Ready loop as etcd runs it (raftNode.start). What it relies on:
//   - committed entries follow the ones applied, contiguously (no gap, no repeat), and a snapshot
//     lies past them;
//   - the batch's snapshot installs in the MemoryStorage (no ErrSnapOutOfDate) and its entries
//     append (no panic);
//   - a leader may send before its durable write; others send after it;
//   - every committed conf change is applied (or refused) before Advance;
//   - ApplyConfChange returns a ConfState while the node runs.
//
// Users: server/etcdserver/raft.go:176-354 (raftNode.start), examples/raft/kvdurable/kv.go:437,
// examples/raft/kvreconf, examples/raft/kv.
// Assumes: ms is the storage n was started on; applied is the index the node started at, and its
// configuration view starts there too (a = applied in RestartNode.spec; a client restarting with a
// view ahead skips the entries below it, as etcd does through its consistent index); decide is the
// client's cluster-wide conf decision (confDecide); n.Stop is called only after stop is closed (the
// loop holds a nodeRunning share while it runs, so a nil ConfState cannot come back to it).
// Specs: node.Ready.spec, readyChan_recv.spec, node.Advance.spec, node.ApplyConfChange.spec,
// MemoryStorage.ApplySnapshot.spec, MemoryStorage.Append.spec, MemoryStorage.SetHardState.spec,
// IsEmptySnap.spec, IsEmptyHardState.spec; laws: readyStor_install.spec, readyStor_append.spec,
// stor_setHardState.spec, nodeDriver_delivered.spec.
func ReqReadyLoop(n raft.Node, ms *raft.MemoryStorage, d Durable, applied uint64,
	send func([]*pb.Message), apply func(*pb.Entry), install func(*pb.Snapshot),
	decide func(*pb.Entry) pb.ConfChangeI, stop <-chan struct{}) {
	lead := false
	for {
		var rd raft.Ready
		select {
		case rd = <-n.Ready():
		case <-stop:
			return
		}
		if rd.SoftState != nil {
			lead = rd.RaftState == raft.StateLeader
		}
		if lead {
			send(rd.Messages) // before the write: the Ready's check update
		}
		if !raft.IsEmptySnap(rd.Snapshot) {
			if rd.Snapshot.GetMetadata().GetIndex() <= applied {
				panic("ready: snapshot not past the applied index")
			}
			d.SaveSnap(rd.Snapshot)
		}
		d.Save(rd.HardState, rd.Entries) // the commit point: the Ready's enter update fires here
		if !raft.IsEmptySnap(rd.Snapshot) {
			if err := ms.ApplySnapshot(rd.Snapshot); err != nil {
				panic("ready: snapshot out of date")
			}
			install(rd.Snapshot)
			applied = rd.Snapshot.GetMetadata().GetIndex()
		}
		if !raft.IsEmptyHardState(rd.HardState) {
			_ = ms.SetHardState(rd.HardState)
		}
		_ = ms.Append(rd.Entries)
		if !lead {
			send(rd.Messages)
		}
		for _, e := range rd.CommittedEntries {
			if e.GetIndex() != applied+1 {
				panic("ready: committed entries not contiguous")
			}
			applied = e.GetIndex()
			switch e.GetType() {
			case pb.EntryConfChange, pb.EntryConfChangeV2:
				if cc := decide(e); cc != nil {
					if n.ApplyConfChange(cc) == nil {
						panic("ready: no ConfState from a running node")
					}
				}
			default:
				apply(e)
			}
		}
		n.Advance()
	}
}

// REQ raftnode/durable-loop: a durable client writes a Ready before relying on it only when
// raft needs it (MustSync, a snapshot, entries); a commit-only hard state may be written late.
// Users: examples/raft/kvdurable/kv.go:465.
// Assumes: as ReqReadyLoop.
// Specs: MustSync.spec, node.Ready.spec (the enter update fired at the write or at once).
func ReqMustSync(rd raft.Ready, prev *pb.HardState) bool {
	return !raft.IsEmptySnap(rd.Snapshot) || len(rd.Entries) != 0 ||
		(!raft.IsEmptyHardState(rd.HardState) && raft.MustSync(rd.HardState, prev, 0))
}

// REQ raftnode/disrupt: leadership disruptions never fail beyond the hand-off: Campaign and
// ForgetLeader return a node error; TransferLeadership and Status return.
// Users: examples/raft/kvdurable/reconf.go:110-118, server/etcdserver/server.go:1285, 2471.
// Assumes: n is a node of the cluster.
// Specs: node.Campaign.spec, node.ForgetLeader.spec, node.TransferLeadership.spec, node.Status.spec,
// node.Tick.spec.
func ReqDisrupt(ctx context.Context, n raft.Node, to uint64) {
	n.Tick()
	n.TransferLeadership(ctx, n.Status().Lead, to)
	if err := n.Campaign(ctx); err != nil && err != raft.ErrStopped && ctx.Err() == nil {
		panic("campaign: unexpected error")
	}
	if err := n.ForgetLeader(ctx); err != nil && err != raft.ErrStopped && ctx.Err() == nil {
		panic("forget leader: unexpected error")
	}
}
