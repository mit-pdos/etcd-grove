/-
Port of `election_proof/spec_raft__appliedTo.v` (857d09190).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
-- (2026-10-29, stage U5) the automatic leave's proposal and step (`LeaveStep`)
public import Proof.go_etcd_io.raft.v3.AutoLeave

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3


section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.appliedTo(index, size)` (`raft.go:735`):

    oldApplied := r.raftLog.applied
    newApplied := max(index, oldApplied)
    r.raftLog.appliedTo(newApplied, size)
    if r.trk.Config.AutoLeave && newApplied >= r.pendingConfIndex && r.state == StateLeader {
        m, err := confChangeToMsg(nil)
        if err != nil { panic(err) }
        if err := r.Step(m); err != nil { r.logger.Debugf(...) } else { r.logger.Infof(...) }
    }

The log's `applied` moves to `max(index, applied)` (`logAppliedTo`, `InvReadylog.lean`); then
(2026-10-29, stage U5; until then the branch was dead, `c.autoLeave = true → s.role ≠ .leader` a
premise) a leader at a configuration it leaves automatically proposes the leave (`LeaveStep`):
`r.Step` of a local `MsgProp` of an empty `EntryConfChangeV2`, which `stepLeader` appends (its
conf-change loop decodes the empty data, `ccDecodeV2_nil`) or refuses. The recursion into `Step` is
one level deep -- `Step` of a `MsgProp` never reaches `appliedTo` -- so the proof takes `Step`'s
`MsgProp` branch (`wp_Step_MsgProp`, over the specs of the functions it calls), not `Step`'s spec.
The proposal is physical here: its ghost step is `raft.Step`'s, which steps the
`MsgStorageApplyResp` that called this. (Stated at `HasLC.hasLC`, as `raft.Step.spec`, whose branch
it takes.)

The premises are `raftLog.appliedTo`'s `Panicf` guard on the new `applied` (`applied <= committed`
already holds) and, at a leader, for the leave's proposal, `wp_Step_MsgProp`'s: the role agrees with
the step function, the term nonzero, the log's last index a word, and the time receipt of its last
index (`⧖ k0`), whose successor the post gives back for the appended entry. -/
abbrev raft.appliedTo.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (index size : w64) (k0 : Nat),
  uint.Z index ≤ uint.Z s.logst.committed →
  -- (D19i part 1) past `applying` only below `offsetInProgress` (`ownRaftLog`'s `FlOk`; D22
  -- S-d1b, 2026-10-21: with a snapshot pending too)
  (uint.Z s.logst.applying < uint.Z index → uint.Z index < uint.Z s.logst.inprogress) →
  -- (2026-10-29, stage U5; until then `c.autoLeave = true → s.role ≠ .leader`) at a leader, for
  -- the leave's proposal (`wp_Step_MsgProp`'s premises): the step function the role's, the term
  -- nonzero, the last index a word
  (s.role = .leader → NStateWf s) →
  (s.role = .leader → s.term ≠ W64 0) →
  (s.role = .leader → plogLastIndexZ (toPState s).base (toPState s).log < 2 ^ 64) →
  -- (D22 S-d2, 2026-10-21) on the raft struct in the acknowledgement's windows
  -- (`ownRaftPhysCVW`): `raft.appliedSnap` calls it in its own (`aps`: `stableSnapTo` dropped
  -- the snapshot, `applied` below the boundary), which ends here, at the boundary; never in the
  -- `sapp` window. The result is quiet.
  s.logst.sapp = false →
  (s.logst.aps = true → uint.Z s.logst.prev.index' ≤ uint.Z index) →
  -- (D22 S-d4 item 3) with a snapshot pending and the storage not lent, past `applying` only up to
  -- what the storage holds (`raftLog.appliedTo`'s premise; `appliedSnap` after a second restore)
  (s.logst.snap ≠ none → s.logst.lent = false → uint.Z s.logst.applying < uint.Z index →
    uint.Z index ≤ uint.Z s.logst.sxt) →
  -- (D22 S-r, 2026-10-21) and, with a pending snapshot not yet handed out, below its index
  -- (`raftLog.appliedTo`'s premise)
  (s.logst.snap ≠ none → s.logst.sip = false → uint.Z s.logst.applying < uint.Z index →
    uint.Z index < uint.Z s.logst.prev.index') →
  -- and in `appliedSnap`'s window, past the snapshot handed out (`SnpExt`)
  (s.logst.aps = true → ∀ k, s.gh.snp = some k → uint.Z k.sid.index' ≤ uint.Z index) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCVW c c.voters r id s ∗
      "#Hrc" ∷ ⧖ k0 }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"appliedTo")) (Val #index))
      (Val #size))
  {{ (s' : NState) (B : Int) (recv : List Msg), RET #();
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
      "%Hstep" ∷ ⌜LeaveStep c id { s with logst := logAppliedTo s.logst index size } s' B recv⌝ ∗
      "Hrcb" ∷ (⌜plogLastIndexZ (toPState s).base (toPState s).log < B⌝ -∗ ⧖ (k0 + 1)) }}

end spec

end EtcdGrove
end Perennial
