---
upstream: unchecked
checked: 2026-10-28
links: []
---

# raft: `doc.go` says `ApplyConfChange` must always be called; `Node`/`RawNode` say it must not be, for a rejected change

**Status**: documentation (contradictory). An application that follows one passage violates the other.

**Where** (etcd-io/raft v3.7.0 plus the fork's fixes, `c8217eb9`, `etc/goose.py`'s pin):

- `doc.go:93-99` (the usage steps, step 3): "If any committed Entry has Type EntryConfChange, call
  Node.ApplyConfChange() to apply it to the node. The configuration change may be cancelled at this
  point by setting the NodeId field to zero before calling ApplyConfChange (but ApplyConfChange must
  be called one way or the other, ...)".
- `node.go:179-183` (`Node.ApplyConfChange`): "This must be called whenever a config change is
  observed in Ready.CommittedEntries, except when the app decides to reject the configuration change
  (i.e. treats it as a noop instead), in which case it must not be called."
- `rawnode.go:108-110` (`RawNode.ApplyConfChange`): "The app must call this when it applies a
  configuration change, except when it decides to reject the configuration change, in which case no
  call must take place."

**What happens**: two ways of rejecting a committed change are documented, and each passage forbids
the other's. etcd follows `doc.go` (it zeroes `NodeID` and calls `ApplyConfChange`,
`EtcdServer.applyConfChange`); `examples/kvreconf` follows `node.go` (it does not call
`ApplyConfChange` for a change raft's `confchange` would refuse, `Replica.applyConf`). In the code
both are sound as long as every replica decides the same for the same committed entry: a `NodeID`
of zero makes `confchange` skip the change, and no call leaves the configuration as it is. The
`NodeID`-zero form does not work for a `ConfChangeV2` leaving a joint configuration (it has no
change to zero), nor for one whose changes `confchange` would refuse for another reason.

**Expected**: one statement of the rule: either form, decided from the replicated state alone.

**How the proof handles it**: the unified node API (in progress, `notes/STATUS.md`) admits both: the
cluster's rule (`ConfRule`) says per committed entry whether the application applies a change (which
may be etcd's zeroed one) or rejects it without a call.

**Possible fixes**: make `doc.go` step 3 say what `Node.ApplyConfChange` says, and that a change may
also be neutralized by zeroing `NodeID` (for a `ConfChange`/a `ConfChangeV2` with changes).

Related: `issues/upstream/raft-advance-before-applyconfchange/meta.md` (noted there, left alone by that
candidate).

**Found**: 2026-10-28, by the spec review of raft's node API for `examples/kvreconf`
(`notes/spec-first-study/raft-node-unified-review-1.md`).
