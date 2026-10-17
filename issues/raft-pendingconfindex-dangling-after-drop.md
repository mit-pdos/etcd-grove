---
upstream: unchecked
checked: 2026-10-16
links:
  - etcd-io/raft#44 pr open: related, makes it worse: with the PR, a refused conf change is dropped instead of appended as an empty entry, so the dangling index is never filled by the retries themselves; the PR adds a second way to create it (a batch whose later conf change is refused)
  - etcd-io/raft#80 issue open: related, not this bug: false positives of the `pendingConfIndex > applied` check in general
  - etcd-io/raft#354 issue open: related, not this bug: a refused conf change is silently turned into an empty entry
---

# raft: a dropped proposal can leave `pendingConfIndex` past the last index

- **Status**: a bug (a wrong result, low severity): after a conf change proposal is dropped,
  the leader may still believe a conf change is pending at an index that holds none, and
  refuse the next conf change proposal although every entry is applied.
- **Where** (the raft `etc/goose.py` pins: branch `raft37-goose-lean` of `upamanyus/etcd`,
  `509271dac`, upstream v3.7.0 plus the read-index fix):
  - `raft.go:1326-1346` (`stepLeader`, `MsgProp`): the conf-change loop accepts a conf change
    by setting `r.pendingConfIndex = r.raftLog.lastIndex() + uint64(i) + 1` (line 1343), its
    index-to-be, before the batch is appended;
  - `raft.go:1349` (`if !r.appendEntry(m.GetEntries()...) { return ErrProposalDropped }`):
    `appendEntry` (`raft.go:812-830`) drops the whole batch when it would exceed
    `MaxUncommittedEntriesSize` (`increaseUncommittedSize`, `raft.go:2090`), and
    `pendingConfIndex` is not restored.
- **What happens**: a leader with some uncommitted payload is proposed a conf change whose
  size exceeds the remaining budget. The loop accepts it (`pendingConfIndex = lastIndex + 1`),
  `appendEntry` drops it, and `Step` returns `ErrProposalDropped`. Now `pendingConfIndex >
  lastIndex`: no entry is at that index. Once everything is committed and applied
  (`applied = lastIndex`), the next conf change proposal is refused (`alreadyPending`:
  `pendingConfIndex > applied`), which at this revision replaces it by an empty normal entry
  and returns `nil`: the caller is told nothing (`RawNode.ProposeConfChange` returns `nil`,
  `Node.ProposeConfChange` too), and the change never takes effect. That empty entry fills
  the dangling index, so the retry after it is accepted. Reproduction:
  `notes/pr-verify/raft-44/pending_conf_index_test.go`,
  `TestConfChangeDroppedBySizeLeavesPendingConfIndex` (in package `raft`; output at this
  revision in `notes/pr-verify/raft-44/base.log`: `pendingConfIndex 3 > lastIndex 2`, then the
  first retry silently becomes an empty entry, the second is appended).

  With etcd-io/raft#44 (a refused conf change returns `ErrProposalDropped` and is not
  appended), the dangling index is never filled by the retries: every conf change proposal is
  refused until some other proposal is appended at that index and applied, so on an idle
  leader conf changes are refused indefinitely (`notes/pr-verify/raft-44/pr.log`).
- **Expected**: `pendingConfIndex` names the index of a conf change in the log (or one at or
  below `applied`); a dropped proposal leaves the leader's state as it was.
- **How the proof handles it**: `stepLeader`'s spec allows it: a dropped proposal's result is
  `s' = s` or `pendingConfIndex` moved by the loop (`LeaderProposeResult`,
  `Spec/go_etcd_io/raft/v3/stepLeader.lean`), and the dynamic model has the stuttering step
  `StepR.propDrop` (`Proof/go_etcd_io/raft/v3/Protocol/StepR.lean`) for it; the safety results
  do not depend on `pendingConfIndex ≤ lastIndex` (the check only makes the leader refuse more).
- **Possible fixes**: compute the new `pendingConfIndex` in a local variable and store it only
  after `appendEntry` accepts the batch (and, with etcd-io/raft#44, only when the loop does
  not return early).
- **Found**: 2026-10-16, verifying etcd-io/raft#44 (`notes/pr-verify/raft-44.md`): the
  `MsgProp` spec's dropped case, which the PR's early return reaches with `pendingConfIndex`
  moved by the conf changes before the refused one.
