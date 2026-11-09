package concurrency

import (
	"context"
	"strings"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
)

// REQ concurrency/campaign-proclaim: after Campaign, the election leads with the session's key
// under the prefix, created at Rev(); a successful Proclaim put the value on that key at that
// create revision (a Get right after sees the value or a later write); Resign clears the key.
// Users: server/etcdserver/api/v3election/election.go:39-60 (Campaign; Key, Rev, Header, Lease
// returned), etcd's tests (election_test.go).
// Assumes: the caller's invariant: keys under pfx+"/" with this session's lease are written only
// through this election's lent permission (its token P, which the caller holds between calls),
// and the lease does not expire during the snippet (EnvCfg.leaseExpiry = false), else a Get may
// see the key re-created by a later Campaign.
// Specs: NewSession.spec, NewElection.spec, Election.Campaign.spec, Election.Key.spec,
// Election.Rev.spec, Election.Header.spec, Election.Proclaim.spec, Election.Resign.spec,
// Client.Get.spec.
func ReqCampaignProclaim(ctx context.Context, s *concurrency.Session, pfx string) {
	e := concurrency.NewElection(s, pfx)
	if err := e.Campaign(ctx, "a"); err != nil {
		return
	}
	if !strings.HasPrefix(e.Key(), pfx+"/") || e.Rev() <= 0 || e.Header() == nil {
		panic("campaign: no leader key, revision or header")
	}
	if e.Header().Revision < e.Rev() {
		panic("campaign: header older than the key")
	}
	if err := e.Proclaim(ctx, "b"); err != nil {
		return
	}
	resp, err := s.Client().Get(ctx, e.Key())
	if err != nil {
		return
	}
	if len(resp.Kvs) == 1 && resp.Kvs[0].CreateRevision == e.Rev() && string(resp.Kvs[0].Value) != "b" {
		panic("proclaim: value lost")
	}
	_ = e.Resign(ctx)
	if e.Key() != "" {
		panic("resign: key kept")
	}
}

// REQ concurrency/resumed-proclaim: v3election's Proclaim and Resign on a resumed election: the
// fence decides (ErrElectionNotLeader when the key is not at that create revision), never a panic.
// Users: server/etcdserver/api/v3election/election.go:62-75, 111-124.
// Assumes: none (the key and revision come from a remote client).
// Specs: ResumeElection.spec, Election.Proclaim.spec, Election.Resign.spec, Election.Header.spec.
func ReqResumedProclaim(ctx context.Context, s *concurrency.Session, name, key string, rev int64) {
	e := concurrency.ResumeElection(s, name, key, rev)
	err := e.Proclaim(ctx, "v")
	if err == nil && e.Header() == nil {
		panic("proclaim: no header")
	}
	e2 := concurrency.ResumeElection(s, name, key, rev)
	if err := e2.Resign(ctx); err == nil && e2.Header() == nil {
		panic("resign: no header")
	}
}

// REQ concurrency/leader: Leader returns one key-value under the prefix, with a header; or
// ErrElectionNoLeader.
// Users: server/etcdserver/api/v3election/election.go:96-108 (l.Kvs[0] returned).
// Assumes: none.
// Specs: NewElection.spec, Election.Leader.spec.
func ReqLeader(ctx context.Context, s *concurrency.Session, pfx string) {
	l, err := concurrency.NewElection(s, pfx).Leader(ctx)
	if err != nil {
		return
	}
	if l.Header == nil || len(l.Kvs) != 1 || !strings.HasPrefix(string(l.Kvs[0].Key), pfx+"/") {
		panic("leader: not one key-value under the prefix")
	}
}

// REQ concurrency/leader-fenced: a write fenced by the leader's key at its create revision
// succeeds only where that key is the oldest under the prefix (the election's exclusion).
// Users: etcd's tests (election_test.go), v3election's clients (Proclaim's fence).
// Assumes: other is not under pfx+"/".
// Specs: Election.Campaign.spec, Election.Key.spec, Election.Rev.spec, Client.Txn.spec and the
// Txn contract; laws: fence.spec.
func ReqLeaderFenced(ctx context.Context, s *concurrency.Session, pfx, other string) {
	e := concurrency.NewElection(s, pfx)
	if err := e.Campaign(ctx, "a"); err != nil {
		return
	}
	resp, err := s.Client().Txn(ctx).
		If(clientv3.Compare(clientv3.CreateRevision(e.Key()), "=", e.Rev())).
		Then(clientv3.OpPut(other, "x"), clientv3.OpGet(pfx+"/", clientv3.WithFirstCreate()...)).
		Commit()
	if err != nil || !resp.Succeeded {
		return
	}
	first := resp.Responses[1].GetResponseRange().Kvs
	if len(first) != 1 || first[0].CreateRevision != e.Rev() {
		panic("election: fenced write while an older key led")
	}
}

// REQ concurrency/observe: Observe's channel, received in a select with the context (v3election's
// loop), yields responses with one key-value under the prefix and a header no older than the
// value, until closed (no order between successive headers: a reconnect may reach a lagging member).
// Users: server/etcdserver/api/v3election/election.go:77-94 (resp.Header, resp.Kvs[0] sent).
// Assumes: none.
// Specs: NewElection.spec, Election.Observe.spec; laws: observeAt_recvAu.spec, Context.doneRecv.
func ReqObserve(ctx context.Context, s *concurrency.Session, pfx string) {
	ch := concurrency.NewElection(s, pfx).Observe(ctx)
	for ctx.Err() == nil {
		select {
		case <-ctx.Done():
		case resp, ok := <-ch:
			if !ok {
				return
			}
			if resp.Header == nil || len(resp.Kvs) != 1 ||
				!strings.HasPrefix(string(resp.Kvs[0].Key), pfx+"/") {
				panic("observe: not one leader key-value")
			}
			if resp.Kvs[0].ModRevision > resp.Header.Revision {
				panic("observe: a value newer than its header")
			}
		}
	}
}
