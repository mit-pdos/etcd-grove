---
upstream: none
checked: 2026-10-20
links:
  - etcd-io/etcd#20729 pr merged: related, not this bug (ours: the 2^48 event window comment in idutil; no cross-member collision)
---

# etcdserver: request ids of two members collide when their member ids agree in the low 16 bits

- **Status**: open (not filed; a robustness issue of low probability).
- **Where**: `pkg/idutil/id.go` (`NewGenerator(memberID uint16, now)`: `prefix = memberID << 48`,
  `suffix = lowbit(unixMilli, 40) << 8`, `Next = prefix | lowbit(suffix++, 48)`);
  `server/etcdserver/server.go:331` (`idutil.NewGenerator(uint16(b.cluster.nodeID), time.Now())`);
  `applyEntryNormal` (`server.go`: `s.w.Trigger(id, ar)` for every applied entry, whoever proposed it).
- **What happens**: request ids are meant to be unique in the cluster: the apply thread of every
  member triggers its wait registry with the id of every committed entry. The prefix is the
  member id truncated to 16 bits, so two members whose 64-bit ids agree in their low 16 bits
  share a prefix (for three random member ids, a chance of about 1 in 20000), and their suffixes
  are millisecond timestamps shifted by 8 plus a counter: a member that started earlier reaches
  the later member's ids after 256 requests per millisecond of the start difference. If member
  A's request `id` commits while member B has a pending request with the same `id`, B's
  waiter receives A's result: B's `Put` returns A's response (or panics in the type assertion
  `resp.(*pb.PutResponse)` if A's request was of another kind), and B's own entry later
  triggers nothing. Reproduction of the id collision (`pkg/idutil`, `go test -overlay`):

```go
package idutil

import (
	"testing"
	"time"
)

// Two members whose 64-bit ids agree in their low 16 bits get the same prefix; the later
// member's ids are reached by the earlier one's counter.
func TestProbeCrossMemberCollision(t *testing.T) {
	t0 := time.Unix(1700000000, 0)
	var idA, idB uint64 = 0x1234_0000_0000_beef, 0x9876_0000_0000_beef // two member ids
	a := NewGenerator(uint16(idA), t0)
	b := NewGenerator(uint16(idB), t0.Add(time.Millisecond))
	first := b.Next()
	for i := 0; i < 1000; i++ {
		if a.Next() == first {
			t.Errorf("member A's request %d has the id %x of member B's first request", i+1, first)
			return
		}
	}
}
```

  prints `member A's request 257 has the id beef8bcfe5680101 of member B's first request`.
  Within one process ids are distinct for `2^48` requests (the plan's suspect 1: the dup-id
  panic of `wait.Register` needs a wrap of the 48-bit suffix).
- **How it happens**: every member's apply loop triggers its wait registry with the id of every
  committed entry, whichever member proposed it, and a member's waiting `Put` takes whatever
  result is triggered under its request id. The generator puts the member id in the top 16 bits
  to make ids unique across members, but it truncates the 64-bit member id to 16 bits. The
  reproduction above, step by step:

  1. Member A (id `0x1234_0000_0000_beef`) starts at `t0`; member B (id `0x9876_0000_0000_beef`)
     starts 1 ms later. Both prefixes are `0xbeef << 48`.
  2. A's suffix starts at `ms(t0) << 8`, B's at `(ms(t0) + 1) << 8`: 256 apart.
  3. B's first request gets `prefix | ((ms(t0) + 1) << 8) + 1` = `beef8bcfe5680101`.
  4. A's 257th request gets `prefix | (ms(t0) << 8) + 257`, the same id.
  5. If A's entry with that id commits while B's request is still waiting, B's apply loop runs
     `s.w.Trigger(id, ar)` with A's result: B's `Put` returns A's response, or panics in
     `resp.(*pb.PutResponse)` if A's request was of another kind.

  ```go
  // pkg/idutil/id.go:56-71 and server/etcdserver/server.go:331 (etcd main f061acd09)
  func NewGenerator(memberID uint16, now time.Time) *Generator {
  	prefix := uint64(memberID) << suffixLen // <-
  	unixMilli := uint64(now.UnixNano()) / uint64(time.Millisecond/time.Nanosecond)
  	suffix := lowbit(unixMilli, tsLen) << cntLen
  	// ...
  }

  // Next generates a id that is unique.
  func (g *Generator) Next() uint64 {
  	suffix := atomic.AddUint64(&g.suffix, 1)
  	id := g.prefix | lowbit(suffix, suffixLen) // <-
  	return id
  }
  // server.go
  		reqIDGen:              idutil.NewGenerator(uint16(b.cluster.nodeID), time.Now()), // <-
  ```

  ```go
  // server/etcdserver/server.go:1940-1978 and v3_server.go:303-307 (etcd main f061acd09)
  func (s *EtcdServer) applyEntryNormal(e *raftpb.Entry, shouldApplyV3 membership.ShouldApplyV3) {
  	// ...
  	ar, id := apply.Apply(s.lg, e, s.uberApply, s.w, shouldApplyV3)
  	// ...
  	if !errorspkg.Is(ar.Err, errors.ErrNoSpace) || len(s.alarmStore.Get(pb.AlarmType_NOSPACE)) > 0 {
  		s.w.Trigger(id, ar) // <- any member's entry
  		return
  // v3_server.go, EtcdServer.Put
  	resp, err := s.raftRequest(ctx, &pb.InternalRaftRequest{Put: r})
  	if err != nil {
  		return nil, err
  	}
  	return resp.(*pb.PutResponse), nil // <-
  ```
- **Expected**: cluster-wide unique request ids (the design of the prefix).
- **How the proof handles it**: a premise of the raft contract's apply side
  (`batchCommitted`, `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRequest.lean`): every
  committed entry's id is claimed (`idClaim`) in one cluster-wide map, i.e. the members'
  prefixes differ; and `idGen`'s `2^48 - 1` credits per process.
- **Possible fixes**: reject member ids that collide in the low 16 bits at member add, or
  derive the prefix from a cluster-unique small index; or check the result's request type /
  include the member id in the request header and ignore other members' entries in `Trigger`.
- **Found**: 2026-10-12, the request path's unit 0 (the wait registry's contract needs the
  entry's id to determine the proposer's request).
