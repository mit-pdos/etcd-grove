---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#4203 issue closed: related, flagged: asked in 2016 whether a Ready's conf change must be applied before Advance (maintainer: 'probably fair'); closed by etcd-io/etcd#4049, whose Advance comment allows Advance while applying without that exception; the safety consequence was not raised
  - etcd-io/raft#80 issue open: related, not this bug: the pendingConfIndex > applied proposal check gives false positives; proposes tracking the configuration explicitly
  - etcd-io/raft#234 issue closed: related, not this bug: split brain with a stalled apply; closed citing hasUnappliedConfChanges (which assumes conf changes are applied before the applied index moves)
  - etcd-io/raft#456 issue open: related, not this bug: the TLA+ spec lacks the hasUnappliedConfChanges guard
  - etcd-io/etcd#12136 issue closed: related, not this bug: pendingConfIndex vs applied with AutoLeave (liveness), fixed by etcd-io/etcd#12137
  - etcd-io/raft#469 pr open: related, not this bug: adds the unapplied-conf-change campaign guard to the TLA+ spec
blocks-proof: no
---

# raft: calling `Advance` before applying a conf change, as `Node.Advance` allows, lets two nodes commit different entries at one index

A leader whose application calls `Advance` before it has applied a committed conf change accepts a
second conf change while the first is still unapplied, and commits it under the old configuration;
with a partition, two nodes then commit different entries at the same index. With voters 1, 2, 3
and node 1 leading: node 1 commits "remove 2" (index 2) and calls `Advance` without applying it;
it then accepts and commits "remove 1" (index 3) under `{1,2,3}`; nodes 2 and 3 apply both and
node 3 becomes the only voter of their configuration; node 1 commits `x` at index 4 with node 2,
and node 3, cut off, elects itself and commits its own entry at index 4.

**Expected:** an index should never be committed with two different entries; if the order
matters, [`Node.Advance`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/node.go#L166-L177)
("the application may call Advance while it is applying the commands") and
[doc.go's step 4](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/doc.go#L101-L103)
("at any time after step 1") should say that conf changes must be applied first.

**Impact:** any application that calls `Advance` before `ApplyConfChange` and makes two membership
changes in a row, followed by a partition. etcd's leader does so (it calls `Advance` without
waiting for its apply loop, which applies the conf change later), and on an etcd cluster this
loses an acknowledged write (reproduced 2026-11-02 at etcd `main`, with a failpoint slowing the
leader's apply loop, two concurrent `MemberAdd`s through different members and a partition): the
etcd half is [`etcd-leader-advance-before-applyconfchange`](etcd-leader-advance-before-applyconfchange.md).
Applications that apply each `Ready` before `Advance`, as doc.go's examples and
`contrib/raftexample` do, are not affected. Same code in v3.7.0.

**Reproduction:** `TestNodeAdvanceBeforeApplyConfChange` in
[`issues/raft-advance-before-applyconfchange/advance_before_applyconfchange_test.go`](raft-advance-before-applyconfchange/advance_before_applyconfchange_test.go)
(three `Node`s through `newNodeTestHarness`; node 1's application calls `Advance` and applies its
committed entries at the end, the others apply before `Advance`), copied into the module root at
etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3 linux/amd64:

```
$ go test . -run '^TestNodeAdvanceBeforeApplyConfChange$' -count=1
--- FAIL: TestNodeAdvanceBeforeApplyConfChange (1.03s)
    advance_before_applyconfchange_test.go:114:
        	Error:      	Not equal:
        	            	expected: "1/4 EntryNormal \"x\""
        	            	actual  : "2/4 EntryNormal \"\""
        	Messages:   	index 4 committed on nodes 1 and 3
FAIL
```

**Cause:** `Advance` moves raft's applied index whether or not `ApplyConfChange` has been called.
Raft's checks for a pending conf change, [before accepting a conf change proposal](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L1326)
and [before campaigning](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L995-L998),
treat every conf change up to the applied index as applied. So node 1 accepts "remove 1" while its
configuration still has three voters, and node 3 may campaign as soon as its applied index reaches
its commit index.

## Proof

no: the top-level adequacy proof needs no fix on the goosed fork for it; the reconfiguration specs take the order as a premise (`node.Advance.dynamicSpec`'s
`NoConfChangeIn`, `Spec/go_etcd_io/raft/v3/node__Advance.lean`; `RawNode.ApplyConfChange.spec`,
`Spec/go_etcd_io/raft/v3/RawNode__ApplyConfChange.lean`), which raft's documentation does not
require and etcd's leader does not meet upstream (the verified etcd fork makes its leader wait).

## Fix

**Branch**: `fix/raft-advance-before-applyconfchange` in `~/etcd-fixes/raft-advance-before-applyconfchange` (upamanyus/etcd-raft, not pushed): 3dcedb6 test (on its own branch, `repro/raft-advance-before-applyconfchange`, in `~/etcd-fixes/raft-advance-before-applyconfchange-repro`), fd30b41 fix
**Base**: etcd-io/raft@1931ff5beacc1e2539003c0c70f096285f04c425

**PR draft**:

Title: raft: document that conf changes must be applied before Advance

[`Node.Advance`](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/node.go#L166-L177) lets the application call `Advance` while it is still applying the last `Ready`, and [doc.go's step 4](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/doc.go#L101-L103) allows it "at any time after step 1". Raft's checks for a pending conf change, [before campaigning](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/raft.go#L995-L998) and [before accepting a conf change proposal](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/raft.go#L1326), assume that every conf change up to the applied index has been applied; `Advance` moves the applied index whether or not `ApplyConfChange` has been called. This PR documents that a `Ready`'s conf changes must be applied before `Advance` (with `AsyncStorageWrites`, before a `MsgStorageApply`'s responses are delivered).

Documentation only (`doc.go`, `README.md`, `node.go`, `raft.go`'s `Config.AsyncStorageWrites`), so
the test is on a branch of its own, linked from the issue: it fails with and without the PR. The
alternative a reviewer may ask about, raft tracking which conf changes were passed to
`ApplyConfChange` ([`raft-track-confchange-application`](../nonissues/raft-track-confchange-application.md),
prototype in `notes/raft-conf-lag-model/guard-fix.patch`), can only be opt-in: applications that
skip `ApplyConfChange` for rejected changes, or for entries replayed after a restart (etcd), would
never campaign again.

## Notes

The same window also lets a node campaign with its own removal committed but not applied; if it
wins after `ApplyConfChange` removes it, `becomeLeader` dereferences its missing progress (a nil
pointer panic; reproduced through `RawNode` by
`notes/raft-conf-lag-model/removed_candidate_rawnode_test.go`, at raft `40f8be7`). The abstract
model and traces of both executions are in `notes/raft-conf-lag-model/`.
