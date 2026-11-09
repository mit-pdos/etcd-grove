package concurrency

import (
	"context"
	"strings"
	"sync/atomic"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
)

// REQ concurrency/campaign-proclaim: after Campaign, the election leads with the session's key
// under the prefix, created at Rev(); a successful Proclaim put the value on that key at that
// create revision (a Get right after sees the value or a later write); Resign clears the key.
// Users: server/etcdserver/api/v3election/election.go:39-60 (Campaign; Key, Rev, Header, Lease
// returned), etcd's tests (election_test.go).
// Assumes: the caller's invariant: keys under pfx+"/" with this session's lease are written only
// through this election's lent permission (its token P, which the caller holds between calls; a
// lease expiry deletes the key, and a re-creation has a later create revision).
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
// Assumes: the compaction condition (W0's exactFrom: no revision from the call on, up to the
// compaction revision, changes one key twice: a workload with no transaction that puts and
// deletes one key, or no compaction); without it a watch's events say nothing (1b's watchStep).
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

// REQ concurrency/election-no-two-leaders: with no lease expiry, a second campaigner does not
// return from Campaign while the first leads (before its Resign).
// Users: etcdctl elect (the leader runs while elected), etcd's tests
// (tests/integration/v3_election_test.go:32 (TestElectionWait: one leader at a time, each resigns
// before the next is elected), :114 (TestElectionFailover), v3election's remote clients.
// Assumes: no lease expiry (W0's EnvCfg.leaseExpiry = false); pfx+"/" owned, empty at the start;
// no other client revokes the two sessions' leases.
// Specs: NewSession.spec (the grant's pre-state: id1 != id2), NewElection.spec,
// Election.Campaign.spec (k = sessKey pfx id; waitedFor; k present at sigma_v with create revision
// cr), Election.Resign.spec; campaignEff (each election writes only its session's key).
// Proof idea: e1's key k1, created at r1 <= sigma1's revision, stays until e1.Resign; e2's key is
// absent at sigma1, so its cr is above r1; e2's waitedFor (noOlder pfx cr) at its state excludes
// k1, so resigned was set before it.
func ReqElectionNoTwoLeaders(ctx context.Context, cli *clientv3.Client, pfx string) {
	s1, err := concurrency.NewSession(cli)
	if err != nil {
		return
	}
	defer s1.Close()
	s2, err := concurrency.NewSession(cli)
	if err != nil {
		return
	}
	defer s2.Close()
	e1 := concurrency.NewElection(s1, pfx)
	if err := e1.Campaign(ctx, "a"); err != nil {
		return
	}
	var resigned atomic.Bool
	done := make(chan struct{})
	go func() {
		defer close(done)
		e2 := concurrency.NewElection(s2, pfx)
		if err := e2.Campaign(ctx, "b"); err != nil {
			return
		}
		if !resigned.Load() {
			panic("election: two leaders at once")
		}
		_ = e2.Resign(ctx)
	}()
	resigned.Store(true)
	_ = e1.Resign(ctx)
	<-done
}
