---
upstream: fixed
checked: 2026-11-01
links:
  - etcd-io/raft#533 issue closed: this bug, reported 2026-10-19; closed by #535
  - etcd-io/raft#535 pr merged: the fix, merged 2026-10-19 (ahrtr: no backport, "usually it won't happen in production")
  - etcd-io/raft@1d3216d84: #535's merge commit, on `main`
  - etcd-io/raft#392 issue closed: related, not this bug: ReadIndex retries with a reused rctx
  - etcd-io/raft#397 pr merged: related, not this bug: unique heartbeat ctxes for read-only requests
  - etcd-io/raft#398 pr merged: related, not this bug: document not retrying ReadIndex with the same rctx
  - etcd-io/raft#83 issue open: related, not this bug: make StepDownOnRemoval the default
blocks-proof: yes
---

# raft: a new leader of a configuration reduced to itself answers `ReadOnlySafe` read index with a stale index

With `ReadOnlySafe`, a node that becomes the only voter through a removal and then wins an election
answers a read index request at once from its commit index, before it has committed an entry in
its term, so the read can miss an entry the previous leader committed (and acknowledged) before the
read was issued.

**Reproduction:** `TestReadOnlyForNewSingleVoterLeader` in
[`issues/raft-readindex-singleton-stale/readindex_singleton_test.go`](raft-readindex-singleton-stale/readindex_singleton_test.go)
(the test of #535, as a standalone file; through `network`), copied into the module root at
etcd-io/raft@638f42739b77 (2026-10-16, the commit before the fix), go1.27.3 linux/amd64. At
`main` it is part of `raft_test.go`.

```
$ go test . -run '^TestReadOnlyForNewSingleVoterLeader$' -count=1
--- FAIL: TestReadOnlyForNewSingleVoterLeader (0.00s)
    readindex_singleton_test.go:60:
        	Error:      	"2" is not greater than or equal to "3"
        	Messages:   	read index
FAIL
```

## Proof

yes: the verified raft (the fork's `raft37-goose-lean-a1`, `etc/goose.py`) carries the fork's fix
(`509271dac`, the single-voter shortcut moved after the first-commit check and taken only when the
leader is the voter); before it, `raft.Step.spec` needed the premise of more than one voter, which
a configuration change can break (`Spec/go_etcd_io/raft/v3/raft__Step.lean`,
`Spec/go_etcd_io/raft/v3/stepLeader.lean`).

## Notes

Not backported (v3.7.0, which etcd `main` uses, still has the shortcut). In etcd it needs a scale
down to one member, a lost commit message and a linearizable read reaching the new leader before
its first `Ready`; not reproduced on a cluster.
