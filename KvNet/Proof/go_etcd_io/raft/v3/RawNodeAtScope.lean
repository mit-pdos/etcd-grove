-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/RawNodeAtScope.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Lean-first (#33 S4, P-raft-3, `notes/antithesis-rawnode-design.md` §2.7). **The harness's scope at a
node's state, for the strengthened `RawNode` proofs**: the lifting lemmas' scope (`LiftScope`,
`InputEndLift.lean`) from `ownRawNodeAt`'s scope (`RnScope`) and the node's resources
(`liftScope_of`: the tally of a follower empty, `ownRaftGhost`'s; the progress map's halves, the
tracker's; the node one of the static configuration's voters, `CfgStatic`); the configuration of a
static node's end relations (`rnCfg`) by its voters (`TickEnd.of_voters`); and the scope's owned part
carried to the end state (`rnScopeAt_keepIf`).
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.RawNodeAbsSpecs
public import KvNet.Proof.go_etcd_io.raft.v3.RawNodeAtLemmas
public import KvNet.Proof.go_etcd_io.raft.v3.InputEndLift

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- `toPState`'s read-index requests are the node's (`rdNL` keeps them). -/
theorem toPState_rd_pend (s : NState) : (toPState s).rd.pend = s.rd.pend := by
  show (if s.role = .leader then s.rd else rdNL s.rd).pend = _
  split <;> rfl

/-- The harness's static configuration's voters (`rnCfg`). -/
theorem rnCfg_voters (γ : RaftNames) : (rnCfg γ).voters = γ.reCfg :=
  CfgM.voters_of_out rfl

/-- `TickEnd` reads the configuration's voters only. -/
theorem TickEnd.of_voters {c c' : CfgM} {id : w64} {s s' : PState} (hv : c.voters = c'.voters)
    (h : TickEnd c id s s') : TickEnd c' id s s' := by
  unfold TickEnd at h ⊢; rwa [← hv]

/-- **`LiftScope` from the pieces**: `RnScope`'s flags, no pre-candidate with pre-vote off, a
follower's tally empty, the progress map's halves, and the node in the configuration. -/
theorem liftScope_of {c : CfgM} {id : w64} {rs : RNState} {s : NState} (H : RnScope rs s)
    (Hpre : s.role = .preCandidate → s.prevote = true) (Hfv : FollowerVotesOk (toPState s))
    (Hd1 : domSet s.prvals = domSet s.progress) (Hd2 : domSet s.progress = c.ids)
    (Hid : id ∈ c.voters) : LiftScope id s := by
  obtain ⟨-, Hpv, Hcq, Hrd, -⟩ := H
  refine ⟨Hpv, Hcq, fun h => (by have := Hpre h; rw [Hpv] at this; cases this), Hfv, Hrd, Hd1, ?_⟩
  rw [Hd1, Hd2]
  exact GMap.elem_of_union_l c.learners Hid

/-- **The scope at the end state of an input** that keeps the log's state (`hl`), pre-vote and
check-quorum (`hpv`, `hcq`), the read-index requests (`hrd`), and queues no `MsgSnap` (`ho`). -/
theorem RnScope.keep {rs rs' : RNState} {s s' : NState} (H : RnScope rs s)
    (hm : rs'.mode = rs.mode) (hsl : rs'.slent = rs.slent)
    (hpv : s'.prevote = s.prevote) (hcq : s'.cq = s.cq) (hrd : s'.rd.pend = s.rd.pend)
    (hprev : s'.logst.prev = s.logst.prev) (hsn : s'.logst.snap = s.logst.snap)
    (ho : ∀ m ∈ s'.outbox, m ∈ s.outbox ∨ m.ty ≠ .snap) : RnScope rs' s' := by
  obtain ⟨H1, H2, H3, H4, H5, H6, H7, H8⟩ := H
  refine ⟨hm.trans H1, hpv.trans H2, hcq.trans H3, hrd.trans H4, hsl.trans H5, hprev.trans H6,
    hsn.trans H7, fun m hm' => ?_⟩
  rcases ho m hm' with h | h
  · exact H8 m h
  · exact h

/-- A tick's end relation keeps the read-index requests and queues no `MsgSnap`: a campaign's votes,
a leader's heartbeats. -/
theorem tickEnd_rd_out {c : CfgM} {id : w64} {s s' : NState}
    (hT : TickEnd c id (toPState s) (toPState s')) :
    s'.rd.pend = s.rd.pend ∧ ∀ m ∈ s'.outbox, m ∈ s.outbox ∨ m.ty ≠ .snap := by
  have ho : s'.outbox = (toPState s').outbox := rfl
  have ho0 : s.outbox = (toPState s).outbox := rfl
  rw [← toPState_rd_pend s', ← toPState_rd_pend s, ho, ho0]
  rcases hT with h | ⟨-, -, peers, cl, -, h⟩ | ⟨-, ms, hms, h⟩
  · rw [h]; exact ⟨rfl, fun m hm => .inl hm⟩
  · rw [h]
    refine ⟨rfl, fun m hm => ?_⟩
    rw [psendMsgs_outbox, List.mem_append] at hm
    rcases hm with hm | hm
    · exact .inl hm
    · right
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · rw [List.mem_singleton] at hm; subst hm; simp [Msg.plain]
      · obtain ⟨d, -, rfl⟩ := List.mem_map.1 hm; simp [pvoteReq]
  · rw [h]
    refine ⟨rfl, fun m hm => ?_⟩
    rw [psendMsgs_outbox, List.mem_append] at hm
    rcases hm with hm | hm
    · exact .inl hm
    · right; rw [(hms m hm).1.1]; decide

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A follower's tally is empty (`ownRaftGhost_follower_votes`, through `ownStepGhost`). -/
theorem ownStepGhost_followerVotes (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) :
    ownStepGhost (GF := GF) γ md c id s ⊢
      ⌜FollowerVotesOk (toPState s)⌝ ∗ ownStepGhost γ md c id s := by
  iintro H
  iunfold ownStepGhost at H
  icases H with ⟨Hg, Hr⟩
  ihave %Hfv := ownRaftGhost_follower_votes γ id (toPState s) $$ Hg
  isplitr
  · ipureintro; exact Hfv
  iunfold ownStepGhost
  iframe Hg Hr

/-- Statically, the configuration is the ghost state's (`ghostRestM`'s `CfgStatic`). -/
theorem ownStepGhost_cfgStatic (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) :
    ownStepGhost (GF := GF) γ md c id s ⊢
      ⌜md = .static → CfgStatic γ c⌝ ∗ ownStepGhost γ md c id s := by
  cases md with
  | static =>
    iintro H
    iunfold ownStepGhost at H
    icases H with ⟨Hg, Hr⟩
    iunfold ghostRest at Hr
    icases Hr with ⟨Hn, Hm, Hr⟩
    ihave %HC : ⌜CfgStatic γ c ∧ TrackedOk γ c id⌝ $$ [Hm]
    · simp only [ghostRestM]; iexact Hm
    isplitr
    · ipureintro; intro _; exact HC.1
    iunfold ownStepGhost
    iframe Hg
    iunfold ghostRest
    iframe Hn Hr
    simp only [ghostRestM]
    ipureintro; exact HC
  | dyn dec c0 h0 g =>
    iintro H
    iframe H
    ipureintro; intro h; cases h

/-- The progress map's halves agree, and track the configuration's ids. -/
theorem ownRaftPhysC_trkDoms (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysCV (GF := GF) c V r id s -∗
      ⌜domSet s.prvals = domSet s.progress ∧ domSet s.progress = c.ids⌝ ∗
      ownRaftPhysCV c V r id s := by
  iintro H
  icases ownRaftPhysC_tracker c r id s $$ H with ⟨%tv, Hf, Htrk, Hback⟩
  icases ownTrackerC_pure c tv _ $$ Htrk with ⟨%Hp, Htrk⟩
  icases ownTrackerC_prvals_dom c tv _ $$ Htrk with ⟨%Hd, Htrk⟩
  isplitr
  · ipureintro; exact ⟨Hd, Hp.2.1⟩
  iapply Hback $$ %tv %s.votes Hf Htrk

/-- **The scope's owned part at the end state**: the scope's facts carried (`H`), the storage the same. -/
theorem rnScopeAt_keepIf (sc : Bool) (rs rs' : RNState) (s s' : NState)
    (H : sc = true → RnScope rs s → RnScope rs' s') (hst : s'.logst.storage = s.logst.storage) :
    rnScopeAt (GF := GF) sc rs s ⊢ rnScopeAt sc rs' s' := by
  cases sc with
  | false => iintro -; iapply rnScopeAt_false
  | true =>
    unfold rnScopeAt; simp only [ite_true]
    iintro ⟨%Hs, #Hc⟩
    rw [hst]
    iframe Hc
    ipureintro; exact H rfl Hs

end ghost

end EtcdGrove
end Perennial
