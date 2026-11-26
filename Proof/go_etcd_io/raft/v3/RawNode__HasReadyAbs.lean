/-
#33 S4 (P-raft-3), `notes/antithesis-rawnode-design.md` §2.2, §2.6. **`RawNode.HasReady`, the
strengthened triple** (`RawNode.HasReady.absSpec`, `RawNodeAbsSpecs.lean`); the old spec is its
corollary (`RawNode.HasReady.spec_of_abs`, `RawNodeSpecOfAbs.lean`). The proof is `RawNode__HasReady.lean`'s (Rocq's
`proof_RawNode__HasReady.v`, 857d09190), over `ownRawNodeAt`: the paths returning `true` close the
node as it was; the one returning `false` reads, in the scope, the protocol-level idle facts
(`pidle_of_hasReady`): the empty queues (`outboxRel_empty`), the hard state `prevHardSt`'s or empty
(and then `prevHardSt`'s too, `PhsOk`), the soft state `prevSoftSt`'s (read by `roleProto`: a pre-candidate a follower), and nothing left to hand out (the in-progress boundary at
the log's end, the storage's view the whole log, `ownRaftPhysC_ipFacts`, which `durTie` makes the
recorded durable state, `durTie_scope`).

A sibling of the function's proof file (the layout: a proof file exposes only its `wp_proof`), which
`RawNode__HasReady.lean` applies.
-/
module

public import Proof.go_etcd_io.raft.v3.RawNodeAbsSpecs
public import Proof.go_etcd_io.raft.v3.RawNodeAtLemmas
public import Proof.go_etcd_io.raft.v3.RawNodeReadyAt
public import Spec.go_etcd_io.raft.v3.SoftState__equal
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.isHardStateEqual
public import Spec.go_etcd_io.raft.v3.raftLog__hasNextUnstableSnapshot
public import Spec.go_etcd_io.raft.v3.raftLog__hasNextUnstableEnts
public import Spec.go_etcd_io.raft.v3.raftLog__hasNextCommittedEnts
public import Spec.go_etcd_io.raft.v3.raft__softState
public import Spec.go_etcd_io.raft.v3.raft__hardState
public import Proof.go_etcd_io.raft.v3.LemmasRawnodeR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`HasReady`'s `false`, at the protocol level** (pure): the facts the false path has. -/
theorem pidle_of_hasReady (rs : RNState) (ps : PState) (ip : Nat) (s : NState) (sv : SoftState)
    (Hps : toPState s = ps) (Hip : uint.nat s.logst.inprogress = ip + 1) (Hprev : s.logst.prev = base0)
    (Hout : s.outbox = [])
    (Hhsi : hsOf s = hsZero ∨ hsOf s = rs.phs) (Hphs : PhsOk rs s)
    (Hsoft : stateW64 s.role = sv.RaftState') (Hrole : rs.role = sv.RaftState')
    (Hnu : nextUnstable s.logst = [])
    (Hb : uint.Z s.logst.prev.index' + (s.logst.sents.length : Int) + 1 ≤ uint.Z s.logst.inprogress ∧
        uint.Z s.logst.inprogress ≤ uint.Z s.logst.prev.index' + (s.logst.sents.length : Int)
          + (s.logst.uents.length : Int) + 1)
    (Hst : uint.Z s.logst.inprogress = uint.Z s.logst.prev.index'
          + (s.logst.sents.length : Int) + (s.logst.uents.length : Int) + 1 →
          s.logst.stored = s.logst.sents ++ s.logst.uents)
    (Hdur : DurFull rs.dur s.logst.stored ∧
      uint.Z rs.dur.base.index' ≤ uint.Z s.logst.prev.index') :
    PIdle rs ps ∧ ip = ps.log.length := by
  subst Hps
  have Hp0 : uint.Z s.logst.prev.index' = 0 := by rw [Hprev]; rfl
  -- the boundary at the log's end
  have Hend : uint.Z s.logst.inprogress = uint.Z s.logst.prev.index'
      + (s.logst.sents.length : Int) + (s.logst.uents.length : Int) + 1 := by
    unfold nextUnstable logOffset at Hnu
    have := List.drop_eq_nil_iff.1 Hnu
    omega
  refine ⟨⟨Hout, ?_, ?_, ?_⟩, ?_⟩
  · rcases Hhsi with h | h
    · have Hle := Hphs.1
      rw [h] at Hle
      obtain ⟨h1, h2, h3⟩ := Hle
      have ht : rs.phs.Term' = W64 0 := by word
      have hc : rs.phs.Commit' = W64 0 := by word
      have hv : rs.phs.Vote' = W64 0 := by
        rcases h3 (by rw [ht]) with h3 | h3 <;> simpa using h3
      have : rs.phs = hsZero := by
        cases hp : rs.phs; simp only [hp] at ht hc hv; simp [hsZero, ht, hc, hv]
      rw [this, ← h]; rfl
    · rw [← h]; rfl
  · rw [Hrole, ← Hsoft, roleProto_stateW64]; rfl
  · simp only [toPState]
    obtain ⟨Hd1, -⟩ := Hdur.1
    have Hb0 : uint.nat rs.dur.base.index' = 0 := by have := Hdur.2; word
    rw [Hd1, Hb0, List.drop_zero, Hst Hend]
  · simp only [toPState, List.length_append]
    word

set_option hygiene false in
/-- Close the raft struct unchanged (`Hphys`). -/
local macro "close_view" : tactic => `(tactic| (
  ihave Hphys := Hclose $$ %sl1 %sl2 %ms1 %ms2 %s.outbox %s.logst %s.gh %rss %s.rd Hf_Term Hf_Vote
    Hf_readStates HreadStates HreadStates_cap %(⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _) Hf_raftLog Hf_state Hf_lead Hf_msgs Hmsgs Hmsgs_cap Hf_msgsAA HmsgsAA
    HmsgsAA_cap Houtbox %HmsgsAA_ok %Hout_term %Hgh_out %(Hgh_unst.1) %(⟨rfl, Hgh_unst.2.1, fun _ h => h⟩) %(fun _ => Int.le_refl _) %Hxf Hscert %(rfl : s.gh.tr = s.gh.tr) %Hlq Hlog))

set_option hygiene false in
/-- Refold `ownRawNodeAt` unchanged, return `true` (the struct closed). -/
local macro "finish0" : tactic => `(tactic| (
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iapply ownRawNodeAt_intro γ rn id rs ps qs ip sc s cf fp rnv sv hprev steps Hwf Hin Hasync Hdlen
    Hunp Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan Hsdt Hrole Hphs Hps Hip
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hsloc Hhist
      Hledger Hdur Hrntr Hsc))

set_option hygiene false in
/-- Close the view, refold `ownRawNodeAt` unchanged, return `true`. -/
local macro "finish" : tactic => `(tactic| (
  close_view
  finish0))

set_option hygiene false in
/-- The one path that returns `false`: no queue is non-empty, no unstable entry is still to be handed
out and no `ReadState` is queued, so the node is idle (`ownRawNodeIdle`), and, in the scope, idle at
the protocol level (`PIdle`). -/
local macro "finish_false" : tactic => `(tactic| (
  ihave %Hl1 := ownSlice_len _ _ _ $$ Hmsgs
  ihave %Hl2 := ownSlice_len _ _ _ $$ HmsgsAA
  have Hnu : nextUnstable s.logst = [] := by
    by_cases h : nextUnstable s.logst = []
    · exact h
    · exact absurd (Hue.trans (decide_eq_true h)) (by decide)
  simp only [List.length_map] at Hl1 Hl2
  have Hout0 : s.gh.outlb = 0 := by word
  have Hm1 : ms1 = [] := List.eq_nil_of_length_eq_zero (by word)
  have Hm2 : ms2 = [] := List.eq_nil_of_length_eq_zero (by word)
  icases outboxRel_empty _ s.outbox ms1 ms2 Hm1 Hm2 $$ Houtbox with ⟨%Hob, Houtbox⟩
  have Hrd0 : s.rd.states = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [Hrs.1]
    have Hz : rss.len = W64 0 := by
      first
        | exact Hif
        | (apply Classical.byContradiction; intro h; exact Hif h)
    rw [Hz]; rfl
  have Hpi : ∀ md, sc = some md → PIdle rs ps.p ∧ ip = ps.p.log.length := fun md h =>
    pidle_of_hasReady rs ps.p ip s sv (by rw [← Hps]; rfl) Hip (Hpsn md h).1 Hob Hhsi Hphs Hsofteq Hrole
      Hnu Hipf.1 (Hipf.2 (Hpsn md h).2) (Hdurf md h)
  close_view
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact Hpi
  isplit
  · ihave Hpend := pendAt_lentPend γ id rs.bw rs.slent steps rs.steps qs $$ Hpend
    iapply ownRawNodeIdle_intro γ rn id rs s cf fp rnv sv hprev steps Hwf Hin Hasync Hdlen Hunp
      Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan Hsdt
      ⟨Hout0, Hnu, Hrd0, Hsn.2 rfl⟩
      Hrole Hphs Hhsi $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs
        Hloanc Hsloc Hhist Hledger Hdur Hrntr
  · iapply ownRawNodeAt_intro γ rn id rs ps qs ip sc s cf fp rnv sv hprev steps Hwf Hin Hasync Hdlen
      Hunp Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan Hsdt Hrole Hphs Hps Hip
      $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hsloc Hhist
        Hledger Hdur Hrntr Hsc))

set_option hygiene false in
/-- The rest of `HasReady` once the hard-state test fell through. -/
local macro "rest" : tactic => `(tactic| (
  icases ownRaftPhysC_view cf rnv.raft' id s $$ Hphys with
    ⟨%rss, %sl1, %sl2, %ms1, %ms2, Hv⟩
  iNamed Hv
  try wp_auto
  wp_apply wp_raftLog_hasNextUnstableSnapshot $$ [Hlog] as %bsn ⟨Hlog, %Hsn⟩
  · iframe Hlog
  cases bsn
  · wp_auto
    wp_if_destruct
    · finish
    wp_if_destruct
    · finish
    wp_apply wp_raftLog_hasNextUnstableEnts $$ [Hlog] as %bue ⟨Hlog, %Hue⟩
    · iframe Hlog
    cases bue
    · wp_auto
      wp_method_call
      wp_call
      wp_auto
      rw [Hasync]
      wp_apply wp_raftLog_hasNextCommittedEnts $$ [Hlog] as %bce ⟨Hlog, _⟩
      · iframe Hlog
      cases bce
      · wp_auto
        wp_if_destruct
        · finish_false
        · finish
      · wp_auto
        finish
    · wp_auto
      finish
  · wp_auto
    finish))

/-- **`RawNode.HasReady`, strengthened** (`RawNode.HasReady.absSpec`). -/
theorem RawNode.HasReady.wp_absProof
    (wp_SoftState_equal : SoftState.equal.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_isHardStateEqual : isHardStateEqual.spec (GF := GF) (hG := hG))
    (wp_raftLog_hasNextUnstableSnapshot :
      raftLog.hasNextUnstableSnapshot.spec (GF := GF) (hG := hG))
    (wp_raftLog_hasNextUnstableEnts : raftLog.hasNextUnstableEnts.spec (GF := GF) (hG := hG))
    (wp_raftLog_hasNextCommittedEnts :
      raftLog.hasNextCommittedEnts.spec (GF := GF) (hG := hG))
    (wp_raft_softState : raft.softState.spec (GF := GF) (hG := hG))
    (wp_raft_hardState : raft.hardState.spec (GF := GF) (hG := hG)) :
    RawNode.HasReady.absSpec (GF := GF) (hG := hG) := by
  intro sc hsc0 γ rn id rs ps qs ip
  wp_start as H
  iNamed H
  iNamed Hrn
  -- the scope's facts, and the struct's, for the `false` path
  icases rnScopeAt_pureOpt sc rs s $$ Hsc with ⟨%Hscope, Hsc⟩
  have Hpsn : ∀ md, sc = some md → s.logst.prev = base0 ∧ s.logst.snap = none := fun md h =>
    ⟨((Hscope md h).1.2.2.2.2.1 (hsc0 md h).1).2.1, ((Hscope md h).1.2.2.2.2.1 (hsc0 md h).1).2.2.1⟩
  ihave %Hdurf := durTie_scopeOpt γ sc rs s Hpsn $$ Hdur
  icases ownRaftPhysC_ipFacts cf rnv.raft' id s $$ Hphys with ⟨%Hipf, Hphys⟩
  wp_auto
  wp_apply wp_raft_softState cf rnv.raft' id s $$ Hphys as Hphys
  wp_apply wp_SoftState_equal $$ [$softSt $Hsoft] as ⟨softSt, _⟩
  wp_if_destruct
  rotate_left
  · finish0
  have Hsofteq : stateW64 s.role = sv.RaftState' := Hif.2
  -- `r.hardState()`: a fresh read-only hard state
  icases ownRaftPhysC_core cf rnv.raft' id s $$ Hphys with ⟨Hcore, Hpb⟩
  wp_apply wp_raft_hardState rnv.raft' id s $$ Hcore as %hp ⟨#Hhp, Hcore⟩
  ihave Hphys := Hpb $$ Hcore
  ihave #Hhp := hsROC_hsRO _ _ $$ Hhp
  ihave #Hhp' := hsRO_to_hsOpt _ _ $$ Hhp
  ihave #Hhard' := prevHS_hsRO γ _ _ _ $$ Hhard
  ihave #Hhard' := hsRO_to_hsOpt _ _ $$ Hhard'
  wp_apply wp_IsEmptyHardState hp _ $$ [$Hhp']
  ihave %Hpe := prevHS_eq γ _ _ _ $$ Hhard
  wp_if_destruct
  · have Hhsi : hsOf s = hsZero ∨ hsOf s = rs.phs := by
      left
      obtain ⟨h1, h2, h3⟩ := Hif
      simp only [hsOf, h1, h2, h3]
    rest
  · wp_apply wp_isHardStateEqual hp rnv.prevHardSt' _ _ $$ [$Hhp' $Hhard']
    wp_if_destruct
    · have Hhsi : hsOf s = hsZero ∨ hsOf s = rs.phs := by
        right
        obtain ⟨h1, h2, h3⟩ := Hif
        rw [← Hpe]
        cases hprev; simp only at h1 h2 h3; simp only [hsOf, h1, h2, h3]
      rest
    · finish0

end proof

end EtcdGrove
end Perennial
