---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/raft#11 issue open: this bug (filed 2022-12 from etcd-io/etcd#14627's review); no fix PR
---

# raft: `MaxUncommittedEntriesSize` does not bound a leader's uncommitted log across terms

**Status**: a bug against `Config.MaxUncommittedEntriesSize`'s documentation, present at the pin.
The limit is enforced per leadership term only.

**Where** (etcd-io/raft as pinned in `etc/goose.py`, fork `upamanyus/etcd` commit `509271dac`,
raft v3.7.0 plus the fork's fix):

- `raft.go:202-206`: "`MaxUncommittedEntriesSize` limits the aggregate byte size of the
  uncommitted entries that may be appended to a leader's log. Once this limit is exceeded,
  proposals will begin to return ErrProposalDropped errors."
- `raft.go:808`: `reset` sets `r.uncommittedSize = 0`. `reset` runs at every term change
  and at `becomeLeader` (`raft.go:938`).
- `raft.go:2090-2103`: `increaseUncommittedSize` compares `r.uncommittedSize`, not the size of
  the log's uncommitted tail, against the limit.

**What happens**: a node leads, appends up to the limit without committing, loses leadership,
and wins again with those entries still uncommitted in its log. `uncommittedSize` starts again
at 0, so it accepts another limit's worth. Each term adds one limit's worth, so the leader's
uncommitted tail is `k × MaxUncommittedEntriesSize` after `k` terms. The leader may also have
inherited uncommitted entries from earlier leaders.

Reproduction: `issues/raft-uncommitted-size-reset-across-terms/uncommitted_reset_test.go`. It
uses three nodes, drops every `MsgApp`, and alternates leadership between nodes 1 and 2. With
a limit of 128 bytes, at the pin:

```
round 0: term 1, uncommitted tail 128 bytes (limit 128), uncommittedSize 128
round 1: term 3, uncommitted tail 256 bytes (limit 128), uncommittedSize 128
...
round 4: term 9, uncommitted tail 640 bytes (limit 128), uncommittedSize 128
--- FAIL: TestUncommittedTailUnboundedAcrossTerms
```

etcd's server never sets `MaxUncommittedEntriesSize`: nothing in `server/` at `107edf7e4`
mentions it. `Config.validate` maps 0 to `noLimit` (`raft.go:313-315`), so etcd itself is not
affected. Applications
that set the limit to bound memory are affected, CockroachDB being the case the issue was
raised for.

**Expected**: the uncommitted tail of a leader's log stays within the limit, up to one
proposal past it, as documented. Alternatively, the documentation says the limit applies to
entries appended in the current term.

**How the proof handles it**: the specs do not mention the size. The field `uncommittedSize`
is in `raftOwn` (`Proof/go_etcd_io/raft/v3/InvRaftPhys.lean:319`), but `NState` does not
record it. `raft.increaseUncommittedSize.spec`
(`Spec/go_etcd_io/raft/v3/raft__increaseUncommittedSize.lean:64-75`) returns a bare `ok`,
stating only that an all-empty batch is accepted. `stepLeader`'s `LeaderProposeResult`
allows a drop (`dropped = true`) at any time and constrains nothing about accepted sizes. So
the specs admit the behavior (class C-perf, `notes/bug-triage/raft-11.md`).

**Possible fixes** (from the issue thread): keep `uncommittedSize` across terms, or recompute
it at `becomeLeader` from the log's tail `(committed, lastIndex]`. Recomputing needs a scan,
which may be expensive, and with async storage writes part of the tail may be unstable. A
third option is to track the size on followers too.

**Found**: 2026-10-16, bug triage of etcd-io/raft#11 (reproduced at the pin).
