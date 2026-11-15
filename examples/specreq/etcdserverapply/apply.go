//go:build ignore

// Requirement snippets for etcd's apply thread (batch 2d): what the request path, the read path
// and configure rely on. In package etcdserver (unexported members).
package etcdserver

import (
	"context"

	"go.etcd.io/etcd/server/v3/etcdserver/apply"
	"go.etcd.io/raft/v3/raftpb"
)

// REQ etcdserverapply/write-answered: a proposed request's waiter is answered with the apply
// thread's result for its entry, which is the answer the cluster fixed at the entry's commit
// (answered γ k id res); the waiter gets a *apply.Result, never another value, unless the
// requester gave up itself.
// Users: server/etcdserver/v3_server.go (processInternalRaftRequestOnce: Register, Propose, wait),
// server/etcdserver/server.go:1970-2030 (applyEntryNormal: Trigger).
// Assumes: id is fresh (idutil); the requester does not trigger id itself; data is the marshalled
// request with id; the member keeps running until the entry is applied.
// Specs: EtcdServer.run.spec, applyAll, applyEntries, apply, applyEntryNormal; 2c's Wait specs;
// laws: answered_agree, srvApplied_hist.
func ReqWriteAnswered(ctx context.Context, s *EtcdServer, id uint64, data []byte) *apply.Result {
	ch := s.w.Register(id)
	if err := s.r.Propose(ctx, data); err != nil {
		s.w.Trigger(id, nil) // GC wait
		return nil
	}
	x := <-ch
	if x == nil {
		panic("write-answered: waiter answered nil without the requester giving up")
	}
	return x.(*apply.Result)
}

// REQ etcdserverapply/read-after-applywait: once applyWait fires at index k, a read of the member's
// KV store sees every write committed at or before k: the store's revision is at least that of an
// acknowledged put whose entry is at k (srvApplied s γ k, srvReadAt). (Not the applied-index atomic:
// applySnapshot does not store it, nonissues/etcd-applied-index-stale-after-snapshot.md.)
// Users: server/etcdserver/read/read.go (LinearizableReadLoop: ApplyWait(confirmedIndex), then the
// readers read s.KV()), server/etcdserver/v3_server.go (waitAppliedIndex before the lease reads),
// server/lease/leasehttp (ApplyWaitCommit), auth/simple_token.go:240 (from start on).
// Assumes: the put that produced revision rev was answered at its entry's commit at index k
// (answered γ k id (.ok (.put rev _))); no compaction is involved (Rev is the current revision).
// Specs: applyAll.spec (applyWait.Trigger with srvApplied), srvApplied_read; 3e's Rev over srvReadAt.
func ReqReadAfterApplyWait(s *EtcdServer, k uint64, rev int64) {
	<-s.applyWait.Wait(k)
	if s.KV().Rev() < rev {
		panic("read-after-applywait: a write committed before the waited index is missing")
	}
}

// REQ etcdserverapply/confchange-answered: a conf change's waiter gets a confChangeResponse whose
// raftAdvanceC closes once raft has applied the change (so the next ProposeConfChange is not
// refused as "pending"); a nil error means the change was accepted at its commit and membs is the
// membership after it (answered γ k id res, histAt γ k σ, membs = σ's members).
// Users: server/etcdserver/server.go:1779-1821 (configure).
// Assumes: cc.ID fresh; cc an AddNode of a member not in the cluster.
// Specs: apply.spec (the trigger: answered, histAt, advancedAt), applyConfChange.spec; 2c's wait
// predicate for conf-change ids (req/go_etcd_io_etcd_server_v3_etcdserver.md, from 2d (round 1)).
func ReqConfChangeAnswered(ctx context.Context, s *EtcdServer, cc *raftpb.ConfChange) {
	ch := s.w.Register(cc.GetId())
	if err := s.r.ProposeConfChange(ctx, cc); err != nil {
		s.w.Trigger(cc.GetId(), nil)
		return
	}
	x := <-ch
	resp, ok := x.(*confChangeResponse)
	if !ok {
		panic("confchange-answered: not a conf change response")
	}
	<-resp.raftAdvanceC
	if resp.err == nil {
		for _, m := range resp.membs {
			if uint64(m.ID) == cc.GetNodeId() {
				return
			}
		}
		panic("confchange-answered: accepted AddNode not in the membership")
	}
}

// REQ etcdserverapply/replay-below-ci: after a restart whose backend is ahead of the raft log's
// snapshot (a crash after the backend committed), the entries up to the consistent index are
// replayed for the membership only, and the consistent index never falls below the applied index
// (snapshot's verifyConsistentIndexIsLatest).
// Users: server/etcdserver/server.go:1917-1968 (apply), 2108-2160 (snapshot).
// Assumes: ep is the apply thread's progress after a batch.
// Specs: apply.spec (applyV3), applyEntryNormal.spec, applyConfChange.spec, snapshot.spec.
func ReqReplayBelowCI(s *EtcdServer, ep *etcdProgress) {
	if s.consistIndex.ConsistentIndex() < ep.appliedi {
		panic("replay-below-ci: consistent index behind the applied index")
	}
}

// REQ etcdserverapply/nospace-alarm: a write refused for lack of space while no NOSPACE alarm is
// raised raises one (an environment step through envUpd, at its commit) and is answered with the
// refusal (ErrNoSpace: a Step with no change).
// Users: server/etcdserver/server.go:2006-2029.
// Assumes: the quota is exceeded by this write (the applier answers ErrNoSpace).
// Specs: applyEntryNormal.spec; 2c's raftRequest.spec; W0's envUpd (EnvStep.alarm).
func ReqNoSpaceAlarm(ctx context.Context, s *EtcdServer, id uint64, data []byte) {
	// What the caller relies on: no panic on this path, and the answer is the refusal.
	if r := ReqWriteAnswered(ctx, s, id, data); r != nil && r.Err == nil {
		panic("nospace-alarm: a write over the quota answered without an error")
	}
}
