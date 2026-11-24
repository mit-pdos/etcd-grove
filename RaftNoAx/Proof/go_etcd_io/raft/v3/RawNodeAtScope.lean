-- The copy for the part `RaftNoAx/` of `Proof/go_etcd_io/raft/v3/RawNodeAtScope.lean` (etc/copy-part.py; rerun it, do not edit).
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

public import RaftNoAx.Proof.go_etcd_io.raft.v3.RawNodeAbsSpecs
public import RaftNoAx.Proof.go_etcd_io.raft.v3.RawNodeAtLemmas
public import RaftNoAx.Proof.go_etcd_io.raft.v3.InputEndLift

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

/-- (#33 S4, msgShape) `RnScope`'s read-only conjunct at the protocol reading: a non-leader's
read-only object reads as the fresh one (`rdNL`). -/
theorem roEmpty_iff (s : NState) :
    (s.role = .leader → s.rd.ro.pending = []) ↔ (toPState s).rd.ro.pending = [] := by
  unfold toPState
  by_cases hr : s.role = .leader
  · simp only [hr, ite_true, true_implies]
  · simp only [hr, ite_false, false_implies, true_iff]; rfl

/-- **The scope at the end state of an input** that keeps the log's state (`hl`), pre-vote and
check-quorum (`hpv`, `hcq`), the read-index requests (`hrd`), an empty read-only queue (`hro`), and
queues no `MsgSnap` (`ho`). -/
theorem RnScope.keep {rs rs' : RNState} {s s' : NState} (H : RnScope rs s)
    (hm : rs'.mode = rs.mode) (hsl : rs'.slent = rs.slent)
    (hpv : s'.prevote = s.prevote) (hcq : s'.cq = s.cq) (hrd : s'.rd.pend = s.rd.pend)
    (hprev : s'.logst.prev = s.logst.prev) (hsn : s'.logst.snap = s.logst.snap)
    (ho : ∀ m ∈ s'.outbox, m ∈ s.outbox ∨ m.ty ≠ .snap)
    (hro : (toPState s).rd.ro.pending = [] → (toPState s').rd.ro.pending = [])
    (hcf : rs'.cfg = rs.cfg := by rfl) : RnScope rs' s' := by
  obtain ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9⟩ := H
  refine ⟨by rw [hm, hcf]; exact H1, hpv.trans H2, hcq.trans H3, hrd.trans H4, hsl.trans H5,
    hprev.trans H6, hsn.trans H7, fun m hm' => ?_, (roEmpty_iff s').2 (hro ((roEmpty_iff s).1 H9))⟩
  rcases ho m hm' with h | h
  · exact H8 m h
  · exact h

/-- (#33 S4, msgShape) A tick keeps the read-only queue empty: a campaign is no leader, a leader's
heartbeats touch no read state. -/
theorem tickEnd_ro {c : CfgM} {id : w64} {s s' : PState} (hT : TickEnd c id s s')
    (h : s.rd.ro.pending = []) : s'.rd.ro.pending = [] := by
  rcases hT with rfl | ⟨-, -, peers, cl, -, rfl⟩ | ⟨-, ms, -, rfl⟩
  · exact h
  · rfl
  · exact h

/-- (#33 S4, msgShape) A message of the harness's types keeps the read-only queue empty (no read
index; a new leader's `reset` installs a fresh one, `rdNL`). -/
theorem handleEnd_ro {c : CfgM} {id : w64} {s : PState} {m : Msg} {s' : PState}
    (hty : m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp)
    (h : HandleEnd c id s m s') (hp : s.rd.ro.pending = []) : s'.rd.ro.pending = [] := by
  unfold HandleEnd at h
  rcases hty with e | e | e | e | e | e <;> rw [e] at h <;> simp only at h
  · split at h
    · subst h; exact hp
    · unfold AppEnd at h
      rcases h with ⟨-, rfl⟩ | ⟨-, _, _, -, rfl⟩ | ⟨-, -, _, _, -, -, rfl⟩ <;> exact hp
  · split at h
    · unfold AppRespEnd SendsEnd at h
      rcases h with ⟨-, rfl⟩ | ⟨-, -, _, -, rfl⟩ | ⟨-, _, _, -, -, _, -, rfl⟩ <;> exact hp
    · subst h; exact hp
  · rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact hp
  · split at h
    · unfold WinEnd at h
      rcases h with ⟨-, rfl⟩ | ⟨-, _, _, -, -, rfl⟩ | ⟨-, rfl⟩
      · exact hp
      · rfl
      · rfl
    · subst h; exact hp
  · split at h <;> (subst h; first | exact hp | rfl)
  · split at h
    · unfold SendsEnd at h
      obtain ⟨_, -, rfl⟩ := h; exact hp
    · subst h; exact hp

theorem recvEnd_ro {c : CfgM} {id : w64} {s : PState} {m : Msg} {s' : PState}
    (hty : m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp)
    (h : RecvEnd c id s m s') (hp : s.rd.ro.pending = []) : s'.rd.ro.pending = [] := by
  rcases h with ⟨-, h⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, h⟩
  · exact handleEnd_ro hty h hp
  · exact hp
  · refine handleEnd_ro hty h ?_
    rcases hpre with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · rfl
    · exact hp

/-- (2026-11-24) **The harness's configuration at a node in the scope**: the incoming voters the
names', no outgoing half (`CfgStatic`'s first two conjuncts, in either mode). -/
def CfgScope (γ : RaftNames) (c : CfgM) : Prop :=
  c.incoming = γ.reCfg ∧ c.outgoing = ∅ ∧ True

theorem CfgScope.voters {γ : RaftNames} {c : CfgM} (HC : CfgScope γ c) : c.voters = γ.reCfg := by
  rw [CfgM.voters_of_out HC.2.1, HC.1]

/-- `CfgScope` from the mode's configuration facts (`ownStepGhost_cfgScope`) and the scope's. -/
theorem cfgScope_of {γ : RaftNames} {id : w64} {rs : RNState} {s : NState} {c : CfgM}
    (Hs : RnScope rs s) (Hc : RnCfgIn γ id rs)
    (Hm : (rs.mode.isDyn = false → CfgStatic γ c) ∧ (rs.mode.isDyn = true → rs.cfg.cfg = c)) :
    CfgScope γ c ∧ id ∈ γ.reCfg := by
  refine ⟨?_, Hc.1⟩
  cases hd : rs.mode.isDyn
  · have H := Hm.1 hd; exact ⟨H.1, H.2.1, trivial⟩
  · rw [← Hm.2 hd]; exact ⟨Hc.2.1 hd, Hs.1 hd, trivial⟩

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

/-- (2026-11-24) **The configuration, by mode**: statically `CfgStatic`; dynamically the ghost
state's (`ghostRestM`'s `g.cfg.cfg = c`, `g.cfg` the node's `rs.cfg`). -/
theorem ownStepGhost_cfgScope (γ : RaftNames) (rs : RNState) (fp : List EntryM) (ds : DecMap)
    (c : CfgM) (id : w64) (s : NState) :
    ownStepGhost (GF := GF) γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) c id s ⊢
      ⌜(rs.mode.isDyn = false → CfgStatic γ c) ∧ (rs.mode.isDyn = true → rs.cfg.cfg = c)⌝ ∗
      ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) c id s := by
  cases hm : rs.mode with
  | static =>
    iintro H
    icases ownStepGhost_cfgStatic γ _ c id s $$ H with ⟨%Hcfs, H⟩
    iframe H
    ipureintro
    exact ⟨fun _ => Hcfs rfl, fun h => by cases h⟩
  | dyn dec c0 h0 h1 =>
    iintro H
    iunfold ownStepGhost at H
    icases H with ⟨Hg, Hr⟩
    iunfold ghostRest at Hr
    icases Hr with ⟨Hn, Hm, Hr⟩
    simp only [RNMode.toG, ghostRestM]
    icases Hm with ⟨%HC, Hm⟩
    isplitr
    · ipureintro; exact ⟨fun h => (by cases h), fun _ => HC.2.1⟩
    iunfold ownStepGhost
    iframe Hg
    iunfold ghostRest
    iframe Hn Hr
    simp only [ghostRestM]
    iframe Hm
    ipureintro; exact HC

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
theorem rnScopeAt_keepIf {γ : RaftNames} {id : w64} (sc : Bool) (rs rs' : RNState) (s s' : NState)
    (H : sc = true → RnScope rs s → RnScope rs' s') (hst : s'.logst.storage = s.logst.storage)
    (hcf : rs'.mode = rs.mode ∧ rs'.cfg = rs.cfg := by exact ⟨rfl, rfl⟩) :
    rnScopeAt (GF := GF) γ id sc rs s ⊢ rnScopeAt γ id sc rs' s' := by
  cases sc with
  | false => iintro -; iapply rnScopeAt_false
  | true =>
    unfold rnScopeAt; simp only [ite_true]
    iintro ⟨%Hs, #Hc⟩
    rw [hst]
    iframe Hc
    ipureintro
    refine ⟨H rfl Hs.1, Hs.2.1, ?_, Hs.2.2.2⟩
    rw [hcf.1, hcf.2]; exact Hs.2.2.1

end ghost

end EtcdGrove
end Perennial
