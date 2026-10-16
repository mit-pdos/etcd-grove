# etcd-io/raft#372: EnterJoint() may allow config changes without quorum overlap that could lead to data loss

<https://github.com/etcd-io/raft/issues/372>. Closed 2026-01-21, the same day it was filed, by the
reporter as invalid. No fix, PR or commit. No version given; the reporter quotes `doc.go:267-270` and
`confchange.go` as on `main`.

**The report.** `Changer.EnterJoint` (`confchange/confchange.go:51` at the raft pin `509271dac`) has
no check like `Simple`'s `symdiff(...) > 1`. So `{1,2,3}` can go in one step to the joint
configuration `⟨{3}, {1,2,3}⟩` and then to `{3}`. The quorum `{1,2}` of the old configuration does
not meet the quorum `{3}` of the new one, so entries committed by `{1,2}` might be missing on node 3.
The reporter's Go test (on a branch of a fork) gets the joint configuration and then calls the
unexported `raft.applyConfChange` with a LeaveJoint that was never committed. The reporter then
withdrew the report. To be committed, the LeaveJoint entry needs a joint quorum, so node 3 must take
part, and log replication gives it every earlier entry. The test had skipped that commit.

## Classification

**N** (not a bug: a misdiagnosis that the reporter withdrew). The decisive fact: quorums have to
overlap between *adjacent* configurations, and they do. The joint configuration's quorums contain a
majority of the old voters, and the final configuration's quorums meet the joint one's. Both facts
are proved, `enterJointM_overlap` and `leaveJointM_overlap` in
`Proof/go_etcd_io/raft/v3/Protocol/CfgOverlap.lean:173,196`. The reported data loss needs a
LeaveJoint applied before it is committed. The dynamic-mode spec of `RawNode.ApplyConfChange` rules
that out by a premise (`DynCCPre`). So the specs document the intended behavior exactly.

## The code path and its verification state

Source: the proof files directly, because `verified.txt` was not yet written. Each proof below is a
`theorem` with no `sorry`, linked in `Proof/go_etcd_io/raft/v3/Link.lean` (for example
`confchange.Changer.wp_EnterJoint`, Link.lean:655).

| Go function | State | Spec |
|---|---|---|
| `confchange.Changer.EnterJoint` | verified | `Spec/go_etcd_io/raft/v3/confchange/Changer__EnterJoint.lean` (result `enterJointM`) |
| `confchange.Changer.LeaveJoint` | verified | `Spec/go_etcd_io/raft/v3/confchange/Changer__LeaveJoint.lean` |
| `raft.applyConfChange` | verified | `Spec/go_etcd_io/raft/v3/raft__applyConfChange.lean` |
| `RawNode.ApplyConfChange` | verified (static and dynamic modes) | `Spec/go_etcd_io/raft/v3/RawNode__ApplyConfChange.lean` |

## The argument (step 4)

1. **Overlap between adjacent configurations.** `enterJointM_overlap` (`CfgOverlap.lean:173`): if
   `enterJointM al ccs s = some s'` and `CfgOk s`, then `QOverlap s.cfg s'.cfg`. Every joint quorum
   of `s'` is a majority of its outgoing voters, which are `s.cfg.incoming` (`applyM_outgoing`), so
   it meets every quorum of `s`. In the reporter's case, the joint configuration
   `⟨{3},{1,2,3}⟩` needs a majority of `{1,2,3}` *and* `{3}`, and that meets `{1,2}`.
   `leaveJointM_overlap` (`:196`): `{3}` overlaps the joint configuration, whose quorums all contain
   node 3. The old and final configurations, `{1,2,3}` and `{3}`, do not overlap, and nothing claims
   they do. `fold_adjacent` (`:424`) states overlap only for log prefixes whose conf counts differ by
   at most one. The far case is the ghost argument of `notes/reconfiguration-safety.md`: the
   LeaveJoint entry is committed under the joint configuration, and leader completeness plus log
   matching do the rest.
2. **The system result.** `raft_dyn_committed_agree` (`Protocol/ResultsDyn.lean:103`): the
   committed prefixes of any two nodes are prefixes of one another, for any sequence of conf
   changes (joint ones included). It is a protocol-model
   theorem. The dynamic mode of the `raft.Step` and `RawNode` specs (stage B7, `notes/STATUS.md`) keeps
   its ghost state, `ownRaftGhostR`, along the Go code. The file header's "not yet reached from Go"
   predates B7.
3. **What the reproduction violates.** `RawNode.ApplyConfChange.spec`, dynamic mode
   (`Spec/go_etcd_io/raft/v3/RawNode__ApplyConfChange.lean:101`), has the premise
   `DynCCPre dec rs o k e cs'` (`Proof/go_etcd_io/raft/v3/InvRawnode.lean:533-548`). The change
   must be the decoded change of the *next committed* conf entry `e` of the delivered log, in
   order and once (assumption A1). The test's LeaveJoint is not a committed entry, so the premise
   fails. The test also calls the unexported `raft.applyConfChange` directly, so it does not
   exercise any API. Under the premise, the observed state (node 3 the only voter without the
   committed entries) is excluded by (2).

Classifying it as A-pre would be wrong: no real caller applies a conf change that was never
committed, and the reporter agrees that "in production, this sequence cannot occur".

Side notes:

- The dynamic mode leaves out auto-leave joint configurations: `DynCCPreOp` requires
  `cs'.cfg.autoLeave = false`, because `appliedTo`'s auto-leave proposal is not in `raft.Step`'s
  scope. The reporter's scenario with `autoLeave = true` is therefore covered by
  `enterJointM_overlap` but not by the end-to-end result. This is a known scope limit
  (`notes/STATUS.md`, reconfiguration B7), not a gap this bug shows.
- `doc.go:270` says "the old and new configurations are guaranteed to overlap". That is true of
  adjacent configurations (each conf entry's before and after). It is not true of the two
  endpoints of a joint change. The wording is loose, which is what misled the reporter, but it is
  not wrong in a way that hides a bug. No `issues/` file.

## Proposal

None (class N). The behavior the reporter expected to be guarded is already stated and proved:
`enterJointM_overlap`, `leaveJointM_overlap` and `raft_dyn_committed_agree` under A1. A related
existing direction, not new: extend the dynamic mode to auto-leave (`autoLeave = true`) so that the
end-to-end result covers the reporter's scenario without manual `LeaveJoint`.

## Files

None in `issues/` or `notes/` besides this report.
