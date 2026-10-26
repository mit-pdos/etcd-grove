---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#20729 pr merged: related, not this bug (the 2^48 event window comment in idutil)
---

# etcdserver: a member can issue the request id 0, which raft's bootstrap conf changes carry

- **Status**: a reachable panic of negligible probability, found while trying to prove the server's
  workload clause (`clusterWorkloadOk`, unit N3; `notes/decisions.md`, D19c). A single-member
  cluster is enough; a variant of `etcd-request-id-member-prefix.md` (ids not unique), not covered
  by it (that one needs two members).
- **Where** (etcd `goose-lean` fork, the pinned revision of `etc/goose.py`; same on main
  f061acd09): `pkg/idutil/id.go` (`NewGenerator`: `prefix = uint64(memberID) << 48`,
  `suffix = lowbit(unixMilli, 40) << 8`; `Next = prefix | lowbit(++suffix, 48)`);
  `server/etcdserver/server.go:331` (`idutil.NewGenerator(uint16(b.cluster.nodeID), time.Now())`);
  raft's `RawNode.Bootstrap` (`bootstrap.go:55`, raft v3.7.0: `&pb.ConfChange{Type: AddNode,
  NodeId: …, Context: …}`, no `Id`, so `GetId() = 0`); `applyEntries`'s conf-change case
  (`server.go:1925`: `s.w.Trigger(cc.GetId(), &confChangeResponse{…})`);
  `processInternalRaftRequestOnce` (`v3_server.go:1126`: `return x.(*apply2.Result), nil`).
- **What happens**: the generator's ids are `prefix | lowbit(s0 + j, 48)` for its `j`-th id, so
  it issues `0` when the member id's low 16 bits are `0` and `s0 + j ≡ 0 (mod 2^48)`: the
  `256·(2^40 - (unixMilli mod 2^40))`-th id. A member started in the last millisecond of a
  `2^40` ms period (next: 2039-09-07, `unixMilli = 2·2^40 - 1`) issues `0` as its 256th id.
  The bootstrap conf changes of a new cluster (and of a member that replays its WAL from index
  1, having no snapshot) have id `0`; applying one triggers the wait registry at `0` with a
  `*confChangeResponse`. A request waiting under id `0` then panics in
  `x.(*apply2.Result)` (a `configure` waiting under `0` would get a wrong answer instead).
  The window is narrow: the request must be registered when the boot entries are applied, at
  the member's start, before `ReadyNotify` (so not through embed's gRPC listeners, which serve
  after it); `publishV3` and direct `EtcdServer` calls can be. Reproduction of the id
  (`pkg/idutil`, `go test -overlay`):

```go
package idutil

import (
	"testing"
	"time"
)

// A member whose id has 0 low 16 bits, started at a millisecond whose low 40 bits are all
// ones, issues the request id 0 (the id of raft's bootstrap conf changes) as its 256th id.
func TestProbeIdZero(t *testing.T) {
	ms := int64(2<<40 - 1) // 2039-09-07: unixMilli mod 2^40 = 2^40 - 1
	g := NewGenerator(0, time.UnixMilli(ms))
	for i := 1; i <= 256; i++ {
		if id := g.Next(); id == 0 {
			t.Logf("request %d has the id 0", i)
			return
		}
	}
	t.Errorf("no id 0")
}
```

  prints `request 256 has the id 0` (run 2026-10-18, `go1.27.1`).
- **Expected**: request ids distinct from every conf change's id (the wait registry is keyed by
  both).
- **How the proof handles it**: the apply side of the raft contract asks, of every committed
  conf change, that no KV request is registered under its id (`entryWaitOk`,
  `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRequest.lean:1671`), a part of the workload
  clause `clusterWorkloadOk` (`InvBuild.lean`). Since D19c (2026-10-18) a generator whose prefix
  is not `0` reserves the id `0` (`idReserved`, `idNoZero`, `pkg/v3/idutil/Defs.lean`), and
  `NewServer.spec` takes the premise `uint.Z id % 2 ^ 16 ≠ 0` (the member id's low 16 bits), with
  a conf-change policy (`srvCCPolicy`) of id-`0` conf changes only.
- **Possible fixes**: skip `0` in `Next` (and the prefix's wrap generally); or give the bootstrap
  conf changes no wait trigger (`Trigger` only for an id the member registered: the registry
  ignores unknown ids already, the collision is with a registered `0`).
- **Found**: 2026-10-18, unit N3 (D19c), trying to establish `batchWaitOk` for the bootstrap log.
