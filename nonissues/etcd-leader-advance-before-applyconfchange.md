---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/raft#354 issue open: related, not this bug (a rejected ConfChange becomes a silent no-op; same pendingConfIndex guard, no Advance/apply ordering)
blocks-proof: yes
---

# etcdserver: the leader calls raft's `Advance` before its apply loop has applied a membership change

When a Ready commits a membership change, a follower's raft loop waits for the apply loop to apply
it before calling raft's `Advance`; the leader's does not. In that window the leader's raft
accepts a second membership change while it still uses the configuration before the first, since
raft's guard (`pendingConfIndex > applied`) reads the applied index `Advance` moves; on raft alone
that lets two different entries commit at the same index (`raft-advance-before-applyconfchange`).

**Why not an issue:** no test shows a wrong result on etcd: the failing test asserts only the
ordering (the leader does not wait), which raft's `Node.Advance` documentation allows ("the
application may call Advance while it is applying the commands"); the bad execution needs a
stalled leader apply loop, two concurrent membership changes from different clients and a
partition, and was not reproduced on a cluster (investigated 2026-10-23: possible in principle, no
etcd check prevents it, only timing). The raft side carries the bug.

## Proof

yes: the verified fork carries the leader's wait (`goose-lean-leaderwait` `4d9282b0f`,
`etc/goose.py`): raft's dynamic mode needs a Ready's conf changes applied before `Advance`.

## Notes

Test: `TestLeaderConfigChangeBlocksApply` in
[`etcd-leader-advance-before-applyconfchange/leader_conf_change_test.go`](etcd-leader-advance-before-applyconfchange/leader_conf_change_test.go)
(`TestConfigChangeBlocksApply` with a leader's Ready; package `etcdserver`) fails at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-11-01): `unexpected execution: raft
routine should block waiting for toApply`. It becomes a valid reproduction if raft documents that
a Ready's conf changes must be applied before `Advance` (the raft candidate), or with an
integration test of the bad execution: a `beforeApplyOneConfChange` failpoint holding the
leader's apply, `MemberAdd(4)` and a concurrent `MemberRemove(2)`, then the partition `{1,2} |
{3,4}` and an election on member 3. The fix (the follower's second `notifyc` send in the leader
branch of `raftNode.start`) is on `fix/etcd-leader-advance-before-applyconfchange` in
`~/etcd-fixes/etcd-leader-advance-before-applyconfchange` (upamanyus/etcd, not pushed; 06f2a0238
test, 18ed639bc fix, on etcd-io/etcd@7ff040cb84c9944d0c38a9f0dc9f12ed9c58223b), held until the raft
documentation PR. Its cost: on a batch with a membership change the leader hands out no new Ready
until the batch is applied, as followers already do. The INDEX-reviewed Plan was "investigate and
see if a bad execution is actually possible": possible, not shown.
