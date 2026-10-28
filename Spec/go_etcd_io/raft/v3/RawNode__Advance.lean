/-
Port of `election_proof/spec_RawNode__Advance.v` (857d09190), made client-facing on
2026-10-09.

Until 2026-10-09 the spec was stated on the node's states (`ownRawNode cfg rn id s rs`
at the `NState` `s`, `ownRaftGhost`, `NStateRel`, the `Step` it refines) and had two
protocol premises: `PstepCommitMono` (the protocol's commit index never moves back,
now the lemma `Step.commit_mono`, `Protocol/Facts.lean`) and `AdvanceOk s rs.steps` on
the queue at the current state (now `StepsOk`, part of `ownRawNode`, `InvRawnode.lean`).
Until 2026-10-10 it also required `rs.advanceable` (see the docstring) and kept the
term.

Lean notes: As for `raft.Step.spec`, the section fixes `hlc := HasLC.hasLC` and has
`[AllG GF]`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnodeReady

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `rn.Advance(rd)` (`rawnode.go:482`):

    if rn.asyncStorageWrites { Panicf(...) }
    for i, m := range rn.stepsOnAdvance {
        _ = rn.raft.Step(m)
        rn.stepsOnAdvance[i] = pb.Message{}
    }
    rn.stepsOnAdvance = rn.stepsOnAdvance[:0]

Steps the local messages the last `Ready` queued -- the node's own responses from
`msgsAfterAppend` (a candidate's vote for itself, a pre-candidate's pre-vote for itself,
a leader's acknowledgement of its own entries), the acknowledgement that the
application appended its entries (`MsgStorageAppendResp`, whose `stableTo` moves them
stable) and that it applied its committed entries (`MsgStorageApplyResp`,
`appliedTo`) -- through `Step`, and empties the queue. The `Ready` argument is unused.

Premises:
- the application appended the last `Ready`'s entries (`rs.unpersisted = []`, after
  `ownRawNode_appended`): the `MsgStorageAppendResp` then acknowledges persisted entries
  only (`StableOk`, `Step`'s premise; Rocq's `ready_stable_ok`) -- also after `MsgApp`s
  stepped since the `Ready` truncated the log below the acknowledged entry (2026-10-10:
  the storage agrees with the log up to it by Log Matching, `stableOk_of_stored`);
- no unstable entry is known to be still to hand out (`rs.unst = false`, 2026-10-10):
  `acceptReady` resets the flag and steps keep it; the acknowledgement's `stableTo` may
  hand out the rest (`NGhost`);
- (2026-10-10 to 2026-10-17) the term does not wrap if it is raised: stepping the node's own
  pre-vote response may win a pre-election, whose `campaign` increments the term
  (`Step`'s premise for a pre-candidate's `MsgPreVoteResp`). Since 2026-10-17 the term
  ceiling bounds it (`RNPv`: a pre-candidate's next term is within `rs.tc`).

The node after: the queue empty, and the term up by at most one -- by a won pre-vote;
once one is won the node is a candidate, which ignores the rest of the queue's
pre-vote responses, and the queue's other responses are its own of earlier terms
(`RespStep`, `Spec/raft__Step.lean`). The rest of the client-facing state is
unchanged.

Until 2026-10-10 the spec required `rs.advanceable`, which `Ready` returned and no
client could establish: the proof covered only a queue without the node's own
responses, for which `Step`'s spec asks facts nothing recorded (`Term ≠ 0`, no
entries, a non-rejecting `MsgAppResp`, a term bound). They are recorded now:
`ownRaftPhys` keeps them for `msgsAfterAppend` (`AAMsgOk`, `InvRaftPhys.lean`) and
`Ready` hands them to the queue (`pendingRel`, `StepsOk`, `InvRawnode.lean`).

(D22 S-d3a, 2026-10-21) After a `Ready` that handed out a snapshot (`RNState.slent`): the
application gives back the storage at the snapshot and its half of the snapshot (`loanRet`,
`snapReceipt`); the node absorbs the storage and steps the acknowledgement, which drops the
pending snapshot (`appliedSnap`: `stableSnapTo`, then `appliedTo` up to the snapshot's index), and
hands the committed log up to the snapshot over (`advRS`). Until then a premise `rs.psnap = false`. -/
abbrev RawNode.Advance.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (rd : Ready),
  -- (D22 S-d3a) the entries handed out appended, but after a snapshot `Ready`, whose receipt
  -- (`loanRet`, the storage at the snapshot holding them) comes back here
  (rs.slent = none → rs.unpersisted = []) →
  rs.unst = false →
  -- (2026-10-14, stage B7 part 2) **A1**, in the dynamic mode: every conf-change entry of the
  -- committed log handed out has been applied (`ApplyConfChange`) -- none past the
  -- configuration index (`issues/raft-advance-before-applyconfchange.md`)
  (rs.mode.isDyn = true → NoConfIn rs.delivered rs.capplied rs.delivered.length) →
  -- (2026-10-28, stage U3c) in the dynamic mode a snapshot's `ConfState` is no auto-leave joint one
  -- (`appliedTo`'s auto-leave proposal is out of `raft.Step`'s scope, as `ApplyConfChange`'s)
  (∀ l, rs.slent = some l → rs.mode.isDyn = true → l.snap.Metadata'.ConfState'.AutoLeave' = false) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      -- (D22 S-d3a, 2026-10-21) after a snapshot `Ready`, the application's receipt
      "Hret" ∷ loanRet rs }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Advance")) (Val #rd))
  {{ (t : w64) (ca : Nat), RET #();
      -- (D19i part 1) `applied` up to `applying`, at least the floor: no longer raised;
      -- (D22 S-d3a) after a snapshot `Ready` the loan returned, the committed log handed out up to
      -- the snapshot (`advRS`)
      ownRawNode γ rn id (advRS rs t ca) ∗
      ⌜uint.Z rs.term ≤ uint.Z t ∧ uint.Z t ≤ uint.Z rs.term + 1⌝ ∗
      -- (2026-10-17; 2026-10-10 to 2026-10-17, with pre-vote off: `t = rs.term`) within the
      -- term ceiling
      ⌜uint.Z t ≤ uint.Z rs.tc⌝ ∗
      -- (2026-10-14) the configuration index moves up, to at most the committed log handed
      -- out (`StepR.advance`); not at all in the static mode; (2026-10-28, stage U3c) after a
      -- snapshot `Ready`, dynamically, to the snapshot's index (`StepR.applySnap`)
      ⌜(rs.slent = none → rs.capplied ≤ ca ∧ ca ≤ max rs.capplied rs.delivered.length) ∧
        (∀ l, rs.slent = some l → rs.mode.isDyn = true → ca = l.dlv.length) ∧
        (rs.mode = .static → ca = rs.capplied)⌝ }}

end spec

end EtcdGrove
end Perennial
