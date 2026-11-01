---
upstream: fixed
checked: 2026-11-01
links:
  - etcd-io/raft#534 issue open: this bug, reported 2026-10-19; closed by #536, then reopened by ahrtr "to track the backport effort" (release-3.7, release-3.6, etcd's release-3.5); still open 2026-11-01
  - etcd-io/raft#536 pr merged: the fix (`IsVoter(r.id) && IsSingleton()`, the reviewer's form); the bot's cherry-picks to release-3.7 and release-3.6 conflict, and ahrtr asked us to backport by hand
  - etcd-io/raft@1931ff5be: #536's merge commit, on `main`
  - etcd-io/raft#83 issue open: related, not this bug: make StepDownOnRemoval the default (would avoid it)
blocks-proof: yes
---

# raft: a leader that removed itself answers `ReadOnlySafe` read index requests at once, with a stale index

With `ReadOnlySafe` and `StepDownOnRemoval` unset, a leader that removed itself stays leader of a
configuration whose only voter is another node, takes the single-voter shortcut and answers read
index requests at once from its own commit index, missing entries the remaining voter has committed
since as leader.

**Reproduction:** `TestReadOnlyForRemovedLeader` in
[`issues/raft-readindex-removed-leader/readindex_removed_leader_test.go`](raft-readindex-removed-leader/readindex_removed_leader_test.go)
(the test of #536, as a standalone file; through `network`), copied into the module root at
etcd-io/raft@1d3216d845a7 (2026-10-19, the commit before the fix), go1.27.3 linux/amd64. At
`main` it is part of `raft_test.go`.

```
$ go test . -run '^TestReadOnlyForRemovedLeader$' -count=1
--- FAIL: TestReadOnlyForRemovedLeader (0.00s)
    readindex_removed_leader_test.go:57:
        	Error:      	"2" is not greater than or equal to "4"
        	Messages:   	read index
FAIL
```

## Proof

yes: the verified raft (the fork's `raft37-goose-lean-a1`, `etc/goose.py`) carries the fork's
fix of the single-voter shortcut (`509271dac`, which also covers
[`raft-readindex-singleton-stale`](raft-readindex-singleton-stale.md)); `raft.Step.spec` takes a
`MsgReadIndex` at any configuration only with it (`Spec/go_etcd_io/raft/v3/sendMsgReadIndexResponse.lean`).

## Notes

Open action: the backports ahrtr asked for (raft release-3.7, release-3.6, etcd's release-3.5
`raft/`), not done. v3.7.0 still has the shortcut in `stepLeader`, so a release-3.7 cherry-pick
needs #535 first. In etcd the window is about a second: a member that removes itself stops after
a 1 s delay, and CheckQuorum deposes it.
