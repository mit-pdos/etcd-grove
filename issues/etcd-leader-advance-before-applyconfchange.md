---
upstream: none
checked: 2026-11-02
links:
  - etcd-io/raft#80 issue open: related, not this bug (the pendingConfIndex > applied check gives false positives; proposes tracking the configuration explicitly)
  - etcd-io/raft#354 issue open: related, not this bug (a rejected ConfChange becomes a silent no-op; same pendingConfIndex guard, no Advance/apply ordering)
blocks-proof: yes
---

# etcdserver: two membership changes while the leader's apply loop lags can lose an acknowledged write

When the leader's apply loop is behind, it accepts a second membership change before it has applied
the first, and keeps counting quorums in the configuration before both. Two `MemberAdd`s through
different members, followed by a partition that leaves the old leader with one follower, then let
both sides commit and acknowledge writes at the same index: a write acknowledged by the old leader is
absent from a linearizable read through the new majority.

**Expected:** an acknowledged write should be visible to every later linearizable read, as etcd's
[API guarantees](https://etcd.io/docs/v3.6/learning/api_guarantees/) state (durability and
linearizability); a member that has a membership change committed but unapplied should refuse
another, as followers already do.

**Impact:** default configuration (strict reconfiguration checks, `CheckQuorum`, pre-vote), three
or more members. It needs the leader's apply loop to be behind while two membership changes are made
concurrently through different members (two administrators or automation), then a partition
separating the old leader and one follower from the rest, with the new members started on the far
side. The apply loop is behind whenever it has a backlog (up to 5000 entries are allowed), a slow
backend commit or a defragmentation; the test widens that window with a failpoint. How often a real
deployment meets all of these was not measured. Present at `main` (raft v3.7.0); release branches
not checked.

**Reproduction:** `TestLeaderAdvanceBeforeApplyConfChangeLosesWrite`, added with a failpoint
(`beforeApplyOneConfChangeOnMember`, a 2 s sleep before each conf-change apply on one member) by
[`issues/etcd-leader-advance-before-applyconfchange/repro.patch`](etcd-leader-advance-before-applyconfchange/repro.patch),
applied at etcd-io/etcd@a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5 (2026-11-02), go1.27.3, after
`gofail enable server/etcdserver/` and `(cd server && go get go.etcd.io/gofail@v0.2.0)`. Members
`{L, F2, F3}`: `MemberAdd(A)` through `L` commits; `MemberAdd(B)` through `F3` is accepted by `L`
before `L` applies the first; partition `{L, F2} | {F3}`; `Put(x)` through `L` is acknowledged; `A`
and `B` start, reaching only `F3`, and `{F3, A, B}` elects `F3`:

```
$ (cd tests && go test ./integration/ -run '^TestLeaderAdvanceBeforeApplyConfChangeLosesWrite$' -count=1 -v)
    leader_advance_confchange_test.go:114: A=9da3560896e3243d B=2cf4eec97050f03d; C1 committed by index 9; C2 applied on F3 (applied 10) while L has applied neither (applied 8)
    leader_advance_confchange_test.go:137: L commits index 11 (was 10) with {L, F2} at term 2
    leader_advance_confchange_test.go:141: put x acknowledged by L at revision 2
    leader_advance_confchange_test.go:172: {F3, A, B} elected 8c4dab4914aa276c at term 4
    leader_advance_confchange_test.go:178: put y acknowledged by the new leader at revision 2
        	Error:      	Should NOT be empty, but was []
        	Messages:   	lost acknowledged write: x acknowledged at revision 2 by 643ae30b654b325d, absent in a linearizable read at revision 2 through 8c4dab4914aa276c
--- FAIL: TestLeaderAdvanceBeforeApplyConfChangeLosesWrite (37.04s)
FAIL	go.etcd.io/etcd/tests/v3/integration	37.212s
```

With the fix below the second `MemberAdd` is refused (raft logs `ignoring conf change ... possible
unapplied conf change`) and the test passes.

**Cause:** for a `Ready` that commits a conf change, a follower's raft loop waits for the apply loop
to apply it before calling `Advance`; the leader's does not
([raft.go#L296-L331](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/raft.go#L296-L331)).
`Advance` moves raft's applied index, and raft's guard against a second pending conf change compares
against it
([raft.go#L1326](https://github.com/etcd-io/raft/blob/b867cf13f6bc0dae21204302df97bc2355c3af55/raft.go#L1326)),
so the leader's raft accepts the second change while its configuration, changed only by the apply
loop's `ApplyConfChange`, is still the one before the first. raft's `Node.Advance` documentation
allows calling `Advance` while applying; the raft half is
[`raft-advance-before-applyconfchange`](raft-advance-before-applyconfchange.md).

## Proof

yes: the verified fork carries the leader's wait (`goose-lean-leaderwait` `4d9282b0f`,
`etc/goose.py`): raft's dynamic mode needs a Ready's conf changes applied before `Advance`.

## Fix

**Branch**: `fix/etcd-leader-advance-before-applyconfchange` in `~/etcd-fixes/etcd-leader-advance-before-applyconfchange` (upamanyus/etcd, not pushed): 06f2a0238 test, 18ed639bc fix
**Base**: etcd-io/etcd@7ff040cb84c9944d0c38a9f0dc9f12ed9c58223b

**PR draft**:

Title: etcdserver: apply conf changes before Advance on the leader too

For a `Ready` with a committed conf change, a follower's raft loop waits for the apply loop to apply
it before calling `Advance`, but the leader's does not ([raft.go](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/raft.go#L296-L331)). `Advance` moves raft's applied index, which raft's check for a pending conf change compares against, so a leader whose apply loop lags accepts a second membership change while it still counts quorums in the configuration before the first. With a partition, that loses an acknowledged write. This PR makes the leader wait as followers do. On a batch with a membership change the leader then hands out no new `Ready` until the batch is applied, as followers already do.

The first commit runs `TestConfigChangeBlocksApply` for a leader too, which fails on `main`; the second, the fix, makes it pass.

**If a reviewer asks**: the branch's test checks the ordering only; the end-to-end test of
`repro.patch` needs a new failpoint, and could be added to the PR. The other place to fix it is raft
(track the configuration, not the applied index; etcd-io/raft#80), which needs every application to
follow.

## Notes

Earlier a non-issue (2026-10-23): the only failing test asserted the ordering, which raft's
documentation allows, and no wrong result had been reproduced; the 2026-10-23 review's plan was
"investigate and see if a bad execution is actually possible". The integration test (2026-11-02)
shows one: moved to `issues/`. `TestLeaderConfigChangeBlocksApply` in
[`leader_conf_change_test.go`](etcd-leader-advance-before-applyconfchange/leader_conf_change_test.go)
(package `etcdserver`, the ordering only) fails at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef:
`unexpected execution: raft routine should block waiting for toApply`. The fix had been held until
raft's documentation PR; the end-to-end failure makes the etcd bug stand on its own. The test must not
`CutPeer` a joining member's rafthttp remote
([`etcd-rafthttp-cutpeer-twice-remote-panic`](../nonissues/etcd-rafthttp-cutpeer-twice-remote-panic.md)).
