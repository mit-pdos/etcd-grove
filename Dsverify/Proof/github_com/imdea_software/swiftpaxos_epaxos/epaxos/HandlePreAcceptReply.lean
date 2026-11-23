/-
`(*Replica).handlePreAcceptReply` against the model's `hPreAcceptReply`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HandleAcceptReply
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Attributes

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- `isInitialBallot(ballot, replica, instance)`. -/
theorem wp_isInitialBallot (b q n : w32) :
    {{ pkgInit_epaxos (GF := GF) }}
      (App (App (App (Val (@! epaxos.isInitialBallot)) (Val #b)) (Val #q)) (Val #n))
    {{ RET #(isInitialBallot b q); True }} := by
  wp_start
  wp_auto
  rw [show decide (b = q) = isInitialBallot b q from rfl]
  iapply HΦ
  itrivial


theorem parSlow_eq (lb : LbRec) (m : PreAcceptReply) (ok sent : w64)
    (hok : (parLb4 lb m).preAcceptOKs = ok) (hs : (parLb4 lb m).preAcceptsSent = sent) :
    parSlow lb m = Bool.and (decide (sint.Z (BitVec.sdiv (W64 ((5 : Nat) : Int)) (W64 2)) ≤ sint.Z ok))
      (Bool.or (!parPre lb m) (decide (sint.Z sent ≤ sint.Z ok))) := by
  unfold parSlow
  rw [hok, hs]
  have e : sint.Z (BitVec.sdiv (W64 ((5 : Nat) : Int)) (W64 2)) = sint.Z (W64 ((nR / 2 : Nat) : Int)) := rfl
  rw [e]
  simp only [BitVec.sle]
  rfl

theorem parFast_eq (lb : LbRec) (m : PreAcceptReply) (ok : w64)
    (hok : (parLb4 lb m).preAcceptOKs = ok) :
    parFast lb m = Bool.and (decide (sint.Z (W64 3) ≤ sint.Z ok)) (parPre lb m) := by
  unfold parFast
  rw [hok]
  simp only [BitVec.sle]
  rfl


theorem parLb4_same (lb : LbRec) (m : PreAcceptReply) :
    (parLb4 lb m).clientProposals = lb.clientProposals ∧ (parLb4 lb m).cmds = lb.cmds ∧
    (parLb4 lb m).prepareReplies = lb.prepareReplies := by
  unfold parLb4 parLb3 parLb2 parLb1
  split <;> (try split) <;> exact ⟨rfl, rfl, rfl⟩

theorem parLb4_deps (lb : LbRec) (m : PreAcceptReply) (mg : w32 × List w32 × Bool)
    (hmgv : parMg lb m = mg)
    (h : (parLb3 lb m).status.sle stPREACCEPTED_EQ = false → mg.2.1 = (parLb2 lb m).deps) :
    (parLb4 lb m).deps = mg.2.1 := by
  unfold parLb4
  split
  · simp [hmgv]
  · rename_i hc
    rw [h (by simpa using hc)]
    rfl

section heap2
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
theorem deps_if (d : GoSlice) (l : List w32) (b : Bool) :
    (d ↦* l : IProp GF) ⊢
      if b then iprop(d ↦* l) else iprop(∃ dq : DFrac, d ↦*{dq} l) := by
  cases b
  · iintro H; simp only [Bool.false_eq_true, ite_false]; iexists DFrac.own 1; iexact H
  · iintro H; simp only [ite_true]; iexact H
theorem par_cmdsRep_dup2 (sl : GoSlice) (o : Option (List WCmd)) :
    cmdsRep (GF := GF) sl o ⊢ cmdsRep sl o ∗ cmdsRep sl o := by
  rcases o with _ | cs
  · unfold cmdsRep
    iintro %Hnil
    isplitr
    · ipureintro; exact Hnil
    · ipureintro; exact Hnil
  · unfold cmdsRep
    iintro ⟨%Hnn, #Hc⟩
    isplitr
    · isplitr
      · ipureintro; exact Hnn
      · iexact Hc
    · isplitr
      · ipureintro; exact Hnn
      · iexact Hc

theorem pt_name_inst (l : Loc) (v : epaxos.Instance) :
    (l ↦ v : IProp GF) ⊢ ∃ v' : epaxos.Instance, l ↦ v' ∗ ⌜v' = v⌝ := by
  iintro H; iexists v; isplitl [H]
  · iexact H
  · ipureintro; rfl

theorem pt_name_lb (l : Loc) (v : epaxos.LeaderBookkeeping) :
    (l ↦ v : IProp GF) ⊢ ∃ v' : epaxos.LeaderBookkeeping, l ↦ v' ∗ ⌜v' = v⌝ := by
  iintro H; iexists v; isplitl [H]
  · iexact H
  · ipureintro; rfl
end heap2

/-- `b && c` with `c` loaded (Go's `&&`). -/
theorem wp_if_and_load (b c : Bool) (p : Loc) :
    {{ (p ↦ c : IProp GF) }}
      (If (Val #b) (App (Val (GoInstruction (GoLoad go.bool))) (Val #p)) (Val #false))
    {{ RET #(b && c); p ↦ c }} := by
  wp_start as Hp
  cases b <;> wp_auto <;> iapply HΦ <;> iframe

/-- What `handlePreAcceptReply` needs (from the invariant: the reply reaches a bookkeeping,
`Inv.replyTargets`; ids in range and deps followable, `Inv.msgWf`/`Inv.wf`; the first counted
reply has a higher vote ballot than `lb.ballot = -1` (the aliasing fact, State.lean "Aliasing");
no reply carries a ballot above `lastTriedBallot` (`Inv.lbInv`: the nack branch is dead); the
counter does not wrap). -/
structure PARWf (i : Nat) (σ : RState) (ord : List w32) (m : PreAcceptReply) (w : InstRec)
    (lb : LbRec) : Prop where
  hrep : RepWf i σ ord
  hq : 0 ≤ zz m.replica ∧ zz m.replica < nR
  hn : 0 ≤ zz m.inst ∧ toN m.inst + 1 < MAX_INSTANCE
  hw : σ.inst ⟨toN m.replica, toN m.inst⟩ = some w
  hlb : w.lb = some lb
  hord : ∀ o ∈ ord, 0 ≤ sint.Z o
  houts : OutsWf (hPreAcceptReply σ m).2
  hdl : (lb.status = stPREACCEPTED ∨ lb.status = stPREACCEPTED_EQ) → lb.deps.length = nR
  hml : m.deps.length = nR
  halias : lb.lastTriedBallot.slt m.ballot = false → m.ballot.slt lb.lastTriedBallot = false →
    (lb.status = stPREACCEPTED ∨ lb.status = stPREACCEPTED_EQ) →
    lb.preAcceptOKs = W64 0 → lb.ballot.slt m.vballot = true
  hnack : lb.lastTriedBallot.slt m.ballot = false
  hok : lb.preAcceptOKs + 1 ≠ W64 0


theorem parLb4_fields (yl1 : epaxos.LeaderBookkeeping) (lb : LbRec) (m : PreAcceptReply)
    (ae ae2 : Bool) (mg : w32 × List w32 × Bool) (hf1 : lbFields yl1 (parLb2 lb m))
    (hae : yl1.allEqual' = ae) (hmgv : parMg lb m = mg) (hae2 : mg.2.2 = ae2) :
    (sint.Z yl1.status' ≤ sint.Z (W8 2) →
      lbFields { yl1 with allEqual' := ae && ae2, seq' := mg.1 } (parLb4 lb m)) ∧
    (¬ sint.Z yl1.status' ≤ sint.Z (W8 2) →
      lbFields { yl1 with allEqual' := ae && ae2 } (parLb4 lb m)) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hf1
  have hst : (parLb3 lb m).status = yl1.status' := by simp [parLb3, a9]
  have hal : (parLb3 lb m).allEqual = (ae && ae2) := by
    simp only [parLb3, hmgv, hae2, ← a2, hae]
  constructor
  · intro h
    have hc : (parLb3 lb m).status.sle stPREACCEPTED_EQ = true := by
      rw [hst, sle_iff]; exact h
    unfold parLb4; rw [if_pos hc]
    exact ⟨a1, hal.symm, a3, a4, a5, a6, a7, a8, a9, by simp [hmgv], a11, a12⟩
  · intro h
    have hc : (parLb3 lb m).status.sle stPREACCEPTED_EQ = false := by
      rcases h' : (parLb3 lb m).status.sle stPREACCEPTED_EQ
      · rfl
      · exact absurd (by rw [hst, sle_iff] at h'; exact h') h
    unfold parLb4; rw [if_neg (by rw [hc]; decide)]
    exact ⟨a1, hal.symm, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩

set_option maxHeartbeats 8000000 in
/-- **`handlePreAcceptReply(pareply)`**. -/
theorem wp_handlePreAcceptReply (hS : replica.Replica.SendMsg.spec (GF := GF))
    (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (ord : List w32) (σ : RState) (l : Loc) (m : PreAcceptReply) (w : InstRec) (lb : LbRec)
    (hw : PARWf i σ ord m w lb) :
    {{ hdCtx (GF := GF) γ i r rr L p Rext ord ∗ ownRep γ i r σ ∗ ownPreAcceptReply l m (DFrac.own 1) ∗
        repFrag γ i (hPreAcceptReply σ m).1 ∗ outsOk γ i (hPreAcceptReply σ m).2 }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"handlePreAcceptReply"))
        (Val #l))
    {{ RET #(); repDone γ i r }} := by
  wp_start as ⟨#Hctx, Hrep, Hm, Hf, Houts⟩
  ihave #Hctx0 := Hctx
  unfold hdCtx
  icases Hctx with ⟨#Hpe, #Hpr, #Hrr, #Hfw, #Hro, #Hinv, #Hpo⟩
  icases ownRep_open γ i r σ $$ Hrep with ⟨%Hib, %Hcb, Hinsts, Hrest⟩
  icases ownRepRest_bump i r σ m.ballot $$ Hrest with ⟨Hmrb, Hrest⟩
  unfold ownPreAcceptReply ownDeps
  icases Hm with ⟨%ds, %cds, Hm, Hds, Hcds⟩
  have hq' : toN m.replica < nR := by
    have := hw.hq.1; have := hw.hq.2; simp only [toN, zz] at *; omega
  have hn' : toN m.inst < MAX_INSTANCE := by have := hw.hn.2; omega
  icases (repInsts_P γ i r σ.inst).1 $$ Hinsts with Hinsts
  icases repInstsP_acc r _ ⟨toN m.replica, toN m.inst⟩ hq' hn' $$ Hinsts with
    ⟨%iss, %rows, %row, %ptrs, %ptr, #Hiss, #Hrows, %Hrow, Hptrs, %Hptr, Hx, Hclose⟩
  ihave Hx := (instAt_some γ i _ ptr w hw.hw).1 $$ Hx
  unfold ownInst
  icases Hx with ⟨%y, Hy, %Hyf, #Hyid, Hycmds, Hydeps, Hylb⟩
  rw [hw.hlb]
  icases Hylb with ⟨%Hlbnn, Hlb⟩
  unfold ownLb
  icases Hlb with ⟨%yl, %gs, %prs, Hyl, %Hylf, Hcp, Hlcmds, Hldeps, Hlprs, %Hlprsl, Hlpr⟩
  ihave %Hrlen := ownSlice_len _ _ _ $$ Hrows
  ihave %Hplen := ownSlice_len _ _ _ $$ Hptrs
  have e1 : sint.Z (W64 (sint.Z m.replica)) = sint.Z m.replica := by word
  have e2 : sint.Z (W64 (sint.Z m.inst)) = sint.Z m.inst := by word
  have hqe : (sint.Z m.replica).toNat = toN m.replica := rfl
  have hne : (sint.Z m.inst).toNat = toN m.inst := rfl
  have h1 : 0 ≤ sint.Z (W64 (sint.Z m.replica)) ∧
      sint.Z (W64 (sint.Z m.replica)) < sint.Z iss.len := by
    have := hw.hq.1; have hl := (List.getElem?_eq_some_iff.mp Hrow).1
    unfold toN zz at *; constructor <;> word
  have h2 : 0 ≤ sint.Z (W64 (sint.Z m.inst)) ∧ sint.Z (W64 (sint.Z m.inst)) < sint.Z row.len := by
    have := hw.hn.1; have := hw.hn.2; have := Hptr.2
    unfold toN zz at *; constructor <;> word
  wp_auto
  simp only [h1, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
  · ipureintro; rw [e1, hqe]; exact Hrow
  simp only [h2, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index row _ ptrs _ ptr h2.1 $$ [$Hptrs] as Hptrs
  · ipureintro; rw [e2, hne]; exact Hptr.1
  ipersist r
  ipersist pareply
  wp_join iprop(efld r go!"maxRecvBallot" ↦ (bumpRecvBallot σ m.ballot).maxRecvBallot ∗
      l ↦ epaxos.PreAcceptReply.mk m.replica m.inst m.ballot m.vballot m.seq ds cds m.status)
    with [Hmrb Hm] as ⟨Hmrb, Hm⟩
  · rw [bumpRecvBallot_true _ _ (by simpa using Hif)]; iframe Hm; iexact Hmrb
  · rw [bumpRecvBallot_false _ _ (by simpa using Hif)]; iframe Hm; iexact Hmrb
  ihave Hrest := Hrest $$ Hmrb
  have hset : ptrs.set (toN m.inst) ptr = ptrs := by
    have := List.getElem?_eq_some_iff.mp Hptr.1
    rw [← this.2]; exact List.set_getElem_self this.1
  wp_if_destruct
  · have hc : stGe w.status stCOMMITTED = true :=
      (stGe_iff _ _).mpr (by rw [← Hyf.2.2.1]; exact Hif)
    rw [hPAR_ret1 σ m w lb hw.hw hw.hlb hc]
    iapply HΦ
    iapply repDone_of γ i r _ [] (by intro o ho; simp at ho)
    iframe Hf Houts
    iapply ownRep_of
    iframe Hrest
    isplitr
    · ipureintro; simpa using Hib
    isplitr
    · ipureintro; simpa using Hcb
    ihave Hx := slot_close_gen (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr y w lb yl gs prs Hyf hw.hlb Hylf
      $$ [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hldeps Hlprs Hlpr]
    · iframe
      isplitl []
      · iexact Hyid
      ipureintro; exact ⟨Hlbnn, Hlprsl⟩
    ihave Hins := Hclose $$ %ptr %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some w))
      [Hptrs] Hx
    · rw [hset]; iexact Hptrs
    rw [show updP (instAtP γ i σ.inst) ⟨toN m.replica, toN m.inst⟩
      (fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some w)) = instAtP γ i σ.inst by
        rw [← hw.hw]; exact updP_self _ _]
    simp only [bumpRecvBallot_inst]
    iapply (repInsts_P γ i r σ.inst).2
    iexact Hins
  have hc : stGe w.status stCOMMITTED = false := by
    rcases h : stGe w.status stCOMMITTED
    · rfl
    · exact absurd ((stGe_iff _ _).mp h) (by rw [← Hyf.2.2.1]; exact Hif)
  rw [Hylf.2.2.2.2.2.2.2.1]
  wp_if_destruct
  · have hb : lb.lastTriedBallot.slt w.bal = true := by rw [slt_iff, ← Hyf.1]; exact Hif
    rw [hPAR_ret2 σ m w lb hw.hw hw.hlb hc hb]
    iapply HΦ
    iapply repDone_of γ i r _ [] (by intro o ho; simp at ho)
    iframe Hf Houts
    iapply ownRep_of
    iframe Hrest
    isplitr
    · ipureintro; simpa using Hib
    isplitr
    · ipureintro; simpa using Hcb
    ihave Hx := slot_close_gen (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr y w lb yl gs prs Hyf hw.hlb Hylf
      $$ [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hldeps Hlprs Hlpr]
    · iframe
      isplitl []
      · iexact Hyid
      ipureintro; exact ⟨Hlbnn, Hlprsl⟩
    ihave Hins := Hclose $$ %ptr %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some w))
      [Hptrs] Hx
    · rw [hset]; iexact Hptrs
    rw [show updP (instAtP γ i σ.inst) ⟨toN m.replica, toN m.inst⟩
      (fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some w)) = instAtP γ i σ.inst by
        rw [← hw.hw]; exact updP_self _ _]
    simp only [bumpRecvBallot_inst]
    iapply (repInsts_P γ i r σ.inst).2
    iexact Hins
  have hb : lb.lastTriedBallot.slt w.bal = false := by
    rcases h : lb.lastTriedBallot.slt w.bal
    · rfl
    · exact absurd ((slt_iff _ _).mp h) (by rw [← Hyf.1]; exact Hif)
  rw [Hylf.2.2.2.2.2.2.2.1]
  wp_if_destruct
  · have hl : m.ballot.slt lb.lastTriedBallot = true := by rw [slt_iff]; exact Hif
    rw [hPAR_ret3 σ m w lb hw.hw hw.hlb hc hb hl]
    iapply HΦ
    iapply repDone_of γ i r _ [] (by intro o ho; simp at ho)
    iframe Hf Houts
    iapply ownRep_of
    iframe Hrest
    isplitr
    · ipureintro; simpa using Hib
    isplitr
    · ipureintro; simpa using Hcb
    ihave Hx := slot_close_gen (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr y w lb yl gs prs Hyf hw.hlb Hylf
      $$ [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hldeps Hlprs Hlpr]
    · iframe
      isplitl []
      · iexact Hyid
      ipureintro; exact ⟨Hlbnn, Hlprsl⟩
    ihave Hins := Hclose $$ %ptr %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some w))
      [Hptrs] Hx
    · rw [hset]; iexact Hptrs
    rw [show updP (instAtP γ i σ.inst) ⟨toN m.replica, toN m.inst⟩
      (fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some w)) = instAtP γ i σ.inst by
        rw [← hw.hw]; exact updP_self _ _]
    simp only [bumpRecvBallot_inst]
    iapply (repInsts_P γ i r σ.inst).2
    iexact Hins
  have hl : m.ballot.slt lb.lastTriedBallot = false := by
    rcases h : m.ballot.slt lb.lastTriedBallot
    · rfl
    · exact absurd ((slt_iff _ _).mp h) Hif
  rw [Hylf.2.2.2.2.2.2.2.1, show decide (sint.Z lb.lastTriedBallot < sint.Z m.ballot) = false from
    decide_eq_false (fun h => by rw [← slt_iff] at h; rw [hw.hnack] at h; cases h)]
  wp_auto
  rw [Hylf.2.2.2.2.2.2.2.2.1]
  unfold epaxos.PREACCEPTED_EQ
  by_cases hs : lb.status = stPREACCEPTED ∨ lb.status = stPREACCEPTED_EQ
  case neg =>
    have hs1 : lb.status ≠ W8 1 := fun h => hs (Or.inl h)
    have hs2 : lb.status ≠ W8 2 := fun h => hs (Or.inr h)
    rw [show decide (lb.status = W8 1) = false from decide_eq_false hs1]
    wp_auto
    rw [Hylf.2.2.2.2.2.2.2.2.1, show decide (lb.status = W8 2) = false from decide_eq_false hs2]
    wp_auto
    rw [hPAR_ret4 σ m w lb hw.hw hw.hlb hc hb hl hw.hnack hs]
    iapply HΦ
    iapply repDone_of γ i r _ [] (by intro o ho; simp at ho)
    iframe Hf Houts
    iapply ownRep_of
    iframe Hrest
    isplitr
    · ipureintro; simpa using Hib
    isplitr
    · ipureintro; simpa using Hcb
    ihave Hx := slot_close_gen (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr y w lb yl gs prs Hyf hw.hlb Hylf
      $$ [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hldeps Hlprs Hlpr]
    · iframe
      isplitl []
      · iexact Hyid
      ipureintro; exact ⟨Hlbnn, Hlprsl⟩
    ihave Hins := Hclose $$ %ptr %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some w))
      [Hptrs] Hx
    · rw [hset]; iexact Hptrs
    rw [show updP (instAtP γ i σ.inst) ⟨toN m.replica, toN m.inst⟩
      (fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some w)) = instAtP γ i σ.inst by
        rw [← hw.hw]; exact updP_self _ _]
    simp only [bumpRecvBallot_inst]
    iapply (repInsts_P γ i r σ.inst).2
    iexact Hins
  have hs0 := hs
  rcases hs with hs1 | hs2
  rw [show decide (lb.status = W8 1) = true from decide_eq_true hs1]
  wp_auto
  rotate_left
  rw [show decide (lb.status = W8 1) = false from decide_eq_false (by rw [hs2]; decide)]
  wp_auto
  rw [Hylf.2.2.2.2.2.2.2.2.1, show decide (lb.status = W8 2) = true from decide_eq_true hs2]
  wp_auto
  rotate_left
  all_goals
    rw [Hylf.1]
    have hdo1 : lb.ballot.slt m.vballot = false → lbDepsOwned lb = true := by
      intro hf
      have hok0 : lb.preAcceptOKs ≠ W64 0 := fun h0 => by rw [hw.halias hw.hnack hl hs0 h0] at hf; cases hf
      simp only [lbDepsOwned, decide_eq_true_eq]
      exact ⟨hs0, hok0⟩
    ipersist lb
    wp_join iprop(∃ (yl1 : epaxos.LeaderBookkeeping), y.lb' ↦ yl1 ∗
        ⌜lbFields yl1 (parLb2 lb m) ∧ yl1.clientProposals' = yl.clientProposals' ∧
          yl1.cmds' = yl.cmds' ∧ yl1.prepareReplies' = yl.prepareReplies'⌝ ∗
        ((⌜yl1.deps' = ds ∧ lb.ballot.slt m.vballot = true⌝ ∗ ds ↦* m.deps) ∨
         (⌜yl1.deps' = yl.deps' ∧ lb.ballot.slt m.vballot = false⌝ ∗ yl.deps' ↦* lb.deps ∗
          ds ↦* m.deps)) ∗
        l ↦ epaxos.PreAcceptReply.mk m.replica m.inst m.ballot m.vballot m.seq ds cds m.status)
      with [Hyl Hldeps Hds Hm] as ⟨%yl1, Hyl, %Hyl1, Hdeps, Hm⟩
    · have hfire : lb.ballot.slt m.vballot = true := by rw [slt_iff]; exact Hif
      iexists _
      iframe Hyl Hm
      isplitr
      · ipureintro
        obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := Hylf
        unfold parLb2 parLb1; rw [if_pos hfire]
        exact ⟨⟨rfl, a2, by simp [a3], a4, a5, a6, a7, a8, rfl, rfl, a11, a12⟩, rfl, rfl, rfl⟩
      ileft
      iframe Hds
      ipureintro; exact ⟨rfl, hfire⟩
    · have hfire : lb.ballot.slt m.vballot = false := by
        rcases h : lb.ballot.slt m.vballot
        · rfl
        · exact absurd ((slt_iff _ _).mp h) Hif
      rw [hdo1 hfire]
      iexists _
      iframe Hyl Hm
      isplitr
      · ipureintro
        obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := Hylf
        unfold parLb2 parLb1; rw [if_neg (by rw [hfire]; decide)]
        exact ⟨⟨rfl, a2, by simp [a3], a4, a5, a6, a7, a8, a9, a10, a11, a12⟩, rfl, rfl, rfl⟩
      iright
      simp only [Bool.true_eq_false, if_true, ↓reduceIte]
      iframe Hldeps Hds
      ipureintro; simp [hfire]
    obtain ⟨hf1, hcp1, hcm1, hpr1⟩ := Hyl1
    ihave #Hfro := isReplicaFw_ro _ _ _ _ _ _ $$ Hfw
    ihave ⟨#HN, #HF, #HId, #HSt, #HRPC, #HPC, #HThr, #HEx, #HDr, #HSh, #HStats, #HStm, #HAl, %HLn⟩ :=
      fwRO_fields _ _ _ _ _ $$ Hfro
    wp_apply wp_isInitialBallot
    have hseq1 : yl1.seq' = (parLb2 lb m).seq := hf1.2.2.2.2.2.2.2.2.2.1
    icases Hdeps with (⟨%Hd, Hds⟩ | ⟨%Hd, Hld, Hds⟩)
    have hp2 : (parLb2 lb m).deps = m.deps := by
      unfold parLb2; rw [if_pos (by simpa [parLb1] using Hd.2)]
    have hpm : parMg lb m = mergeAttributes yl1.seq' m.deps m.seq m.deps := by
      unfold parMg; rw [hp2, hseq1]
    rw [Hd.1]
    wp_apply +noauto (wp_mergeAttributes_self γ i r rr L p yl1.seq' m.seq ds m.deps (DFrac.own 1)
      hw.hml) $$ [$Hrr $Hfro $Hds]
    iintro ⟨Hd0, %Hmg⟩
    rw [← hpm] at Hmg ⊢
    rw [← Hd.1]
    ihave Hd0 : yl1.deps' ↦* (parMg lb m).2.1 $$ [Hd0]
    · rw [Hmg, Hd.1]; iexact Hd0
    have hdeps4 : (parLb3 lb m).status.sle stPREACCEPTED_EQ = false →
        (parMg lb m).2.1 = (parLb2 lb m).deps := fun _ => by rw [Hmg, hp2]
    rotate_left
    have hp2 : (parLb2 lb m).deps = lb.deps := by
      unfold parLb2; rw [if_neg (by simp [parLb1, Hd.2])]; rfl
    have hpm : parMg lb m = mergeAttributes yl1.seq' lb.deps m.seq m.deps := by
      unfold parMg; rw [hp2, hseq1]
    rw [Hd.1]
    wp_apply +noauto (wp_mergeAttributes γ i r rr L p yl1.seq' m.seq yl.deps' ds lb.deps m.deps
      (DFrac.own 1) (hw.hdl hs0) hw.hml) $$ [$Hrr $Hfro $Hld $Hds]
    iintro ⟨Hd0, Hds⟩
    rw [← hpm]
    rw [← Hd.1]
    iclear Hds
    have hdeps4 : (parLb3 lb m).status.sle stPREACCEPTED_EQ = false →
        (parMg lb m).2.1 = (parLb2 lb m).deps := by
      intro h
      exfalso
      have hst : (parLb3 lb m).status = lb.status := by
        simp [parLb3, parLb2, parLb1, Hd.2]
      rw [hst] at h
      rcases hs0 with h' | h' <;> rw [h'] at h <;> revert h <;> decide
    rotate_left
    all_goals
      generalize hmgv : parMg lb m = mg at hdeps4 ⊢
      wp_auto
      rw [show L.length = 5 from HLn.1,
        show decide (sint.Z (W64 ((5 : Nat) : Int)) ≤ sint.Z (W64 3)) = false by decide]
      wp_auto
      generalize hae : yl1.allEqual' = ae
      wp_join (Q := fun v => iprop(⌜v = #(ae && mg.2.2)⌝ ∗ allEqual_ptr ↦ mg.2.2)) with [allEqual]
      all_goals first | (iframe allEqual; done) | (iframe allEqual; ipureintro; first | rfl | trivial) | skip
      iintro ⟨%Hv, allEqual⟩
      subst Hv
      wp_auto
      generalize hae2 : mg.2.2 = ae2
      generalize hnb : (!ae2) = nb
      wp_join iprop(True) with [] as %_
      all_goals try itrivial
      · -- `r.Stats.M["conflicted"]++` under `r.M`
        ihave #Hlock := isReplicaFw_lock _ _ _ _ _ _ $$ Hfw
        wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HR⟩
        unfold fwLockInv
        icases HR with ⟨Hcore, Hext⟩
        icases fwCore_stats _ _ _ _ $$ Hcore with ⟨%sm, Hsm, Hcl⟩
        ihave #HStm2 := HStm
        iStructNamed HStm2
        wp_auto
        wp_apply wp_map_lookup1 $$ [$Hsm] as Hsm
        try wp_auto
        wp_apply wp_mapInsert $$ [$Hsm] as Hsm
        ihave Hcore := Hcl $$ Hsm
        wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hcore Hext]
        · iframe Hcore Hext
        wp_join_done
        try itrivial
      have hp4 := parLb4_fields yl1 lb m ae ae2 mg hf1 hae hmgv hae2
      ipersist deps
      ipersist seq
      wp_join iprop(∃ yl4 : epaxos.LeaderBookkeeping, y.lb' ↦ yl4 ∗
          ⌜lbFields yl4 (parLb4 lb m) ∧ yl4.deps' = yl1.deps' ∧
            yl4.clientProposals' = yl.clientProposals' ∧ yl4.cmds' = yl.cmds' ∧
            yl4.prepareReplies' = yl.prepareReplies'⌝) with [Hyl] as ⟨%yl4, Hyl, %Hyl4⟩
      all_goals first
        | (iexists _; iframe Hyl; ipureintro; exact ⟨hp4.1 Hif, rfl, hcp1, hcm1, hpr1⟩)
        | (iexists _; iframe Hyl; ipureintro; exact ⟨hp4.2 Hif, rfl, hcp1, hcm1, hpr1⟩)
        | skip
      try wp_auto
      wp_apply wp_if_and_load $$ [$allCommitted] as allCommitted
      wp_apply wp_if_and_load $$ [$isInitialBallot] as isInitialBallot
      have hpreq : (yl4.allEqual' && true && isInitialBallot yl1.lastTriedBallot' m.replica) =
          parPre lb m := by
        simp only [Bool.and_true, parPre, Hyl4.1.2.1, hf1.2.2.2.2.2.2.2.1]
      rw [hpreq]
      have hok4 : (parLb4 lb m).preAcceptOKs = yl4.preAcceptOKs' := Hyl4.1.2.2.1.symm
      have hsent4 : (parLb4 lb m).preAcceptsSent = yl4.preAcceptsSent' :=
        Hyl4.1.2.2.2.2.2.2.2.2.2.2.2.symm
      have hsq := parSlow_eq lb m _ _ hok4 hsent4
      ipersist inst
      wp_join (Q := fun v => iprop(⌜v = #(parSlow lb m)⌝ ∗ y.lb' ↦ yl4 ∗ ptr ↦ y ∗
          precondition_ptr ↦ parPre lb m)) with [Hyl Hy precondition]
      · cases hp : parPre lb m <;> wp_auto
        · iframe; ipureintro; rw [hsq, hp, decide_eq_true Hif]; rfl
        · iframe; ipureintro; rw [hsq, hp, decide_eq_true Hif]; rfl
      · iframe; ipureintro; rw [hsq, decide_eq_false Hif]
      iintro ⟨%Hv, Hyl, Hy, precondition⟩
      subst Hv
      wp_auto
      wp_apply wp_fastQuorumReplies $$ [$Hrr $HF]
      wp_apply wp_if_and_load $$ [$precondition] as precondition
      rw [← parFast_eq lb m _ hok4]
      have hm4 := hPAR_main σ m w lb hw.hw hw.hlb hc hb hl hw.hnack hs0
      cases hfst : parFast lb m
      · cases hsl : parSlow lb m
        · -- neither path: the bookkeeping updated, return
          wp_auto
          rw [hm4, hfst, hsl]
          simp only [Bool.false_eq_true, ↓reduceIte]
          iapply HΦ
          iapply repDone_of γ i r _ [] (by intro o ho; simp at ho)
          iframe Hf Houts
          iapply ownRep_of
          rw [ownRepRest_setInst]
          iframe Hrest
          isplitr
          · ipureintro; simpa [RState.setInst] using instBounds_upd _ _ _ Hib hq' hw.hn.2
          isplitr
          · ipureintro; simpa [RState.setInst] using Hcb
          obtain ⟨hs1, hs2, hs3⟩ := parLb4_same lb m
          have hd4 := parLb4_deps lb m mg hmgv hdeps4
          ihave Hd0 := deps_if _ _ (lbDepsOwned (parLb4 lb m)) $$ Hd0
          ihave Hx := slot_close_gen (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr y
            { w with lb := some (parLb4 lb m) } (parLb4 lb m) yl4 gs prs Hyf rfl Hyl4.1
            $$ [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hd0 Hlprs Hlpr]
          · rw [hs1, hs2, hs3, hd4, Hyl4.2.1, Hyl4.2.2.1, Hyl4.2.2.2.1, Hyl4.2.2.2.2]
            iframe
            isplitl []
            · iexact Hyid
            ipureintro; exact ⟨Hlbnn, Hlprsl⟩
          ihave Hins := Hclose $$ %ptr %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt
            (some { w with lb := some (parLb4 lb m) })) [Hptrs] Hx
          · rw [hset]; iexact Hptrs
          rw [updP_instAtP]
          simp only [RState.setInst, bumpRecvBallot_inst]
          iapply (repInsts_P γ i r _).2
          iexact Hins
        · -- the slow path: `lb.status = ACCEPTED`, the instance takes its attributes
          have hnex : w.status ≠ stEXECUTED := by
            intro hex; rw [hex] at hc; revert hc; decide
          obtain ⟨hs1, hs2, hs3⟩ := parLb4_same lb m
          have hd4 := parLb4_deps lb m mg hmgv hdeps4
          imod ownSlice_persist $$ Hd0 with #Hd0
          iclear Hycmds Hydeps
          ihave ⟨Hlcmds, Hlcmds2⟩ := par_cmdsRep_dup2 _ _ $$ Hlcmds
          unfold epaxos.ACCEPTED
          wp_auto
          icases pt_name_lb _ _ $$ Hyl with ⟨%yl5, Hyl, %Hyl5⟩
          icases pt_name_inst _ _ $$ Hy with ⟨%y5, Hy, %Hy5⟩
          have hyf5 : instFields y5 (parInstS w lb m) := by
            subst Hy5
            obtain ⟨a1, a2, a3, a4, a5⟩ := Hyf
            obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := Hyl4.1
            exact ⟨b1, a2, rfl, b10, fun _ => a5 hnex⟩
          have hlf5 : lbFields yl5 (parLbS lb m) := by
            subst Hyl5
            obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := Hyl4.1
            exact ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl, b10, b11, b12⟩
          have hy5 : y5.id' = y.id' ∧ y5.Cmds' = yl.cmds' ∧ y5.Deps' = yl1.deps' ∧ y5.lb' = y.lb' := by
            subst Hy5; exact ⟨rfl, Hyl4.2.2.2.1, Hyl4.2.1, rfl⟩
          have hyl5 : yl5.cmds' = yl.cmds' ∧ yl5.deps' = yl1.deps' ∧
              yl5.clientProposals' = yl.clientProposals' ∧ yl5.prepareReplies' = yl.prepareReplies' := by
            subst Hyl5; exact ⟨Hyl4.2.2.2.1, Hyl4.2.1, Hyl4.2.2.1, Hyl4.2.2.2.2⟩
          have hF : (parInstS w lb m).cmds = lb.cmds ∧ (parInstS w lb m).deps = mg.2.1 ∧
              (parLbS lb m).cmds = lb.cmds ∧ (parLbS lb m).deps = mg.2.1 ∧
              (parLbS lb m).clientProposals = lb.clientProposals ∧
              (parLbS lb m).prepareReplies = lb.prepareReplies ∧
              lbDepsOwned (parLbS lb m) = false ∧
              decide ((parInstS w lb m).status = stEXECUTED) = false := by
            refine ⟨hs2, hd4, hs2, hd4, hs1, hs3, ?_, ?_⟩ <;>
              simp [lbDepsOwned, parLbS, parInstS, stCOMMITTED, stACCEPTED, stPREACCEPTED,
                stPREACCEPTED_EQ, stEXECUTED]
          have hdoK := hF.2.2.2.2.2.2.1
          ihave Hx := slot_close_gen (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr y5 (parInstS w lb m)
              (parLbS lb m) yl5 gs prs hyf5 rfl hlf5
            $$ [Hy Hlcmds Hlcmds2 Hyl Hcp Hlprs Hlpr]
          · obtain ⟨e1, e2, e3, e4⟩ := hy5
            obtain ⟨f1, f2, f3, f4⟩ := hyl5
            obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hF
            simp only [e1, e2, e3, e4, f1, f2, f3, f4, g1, g2, g3, g4, g5, g6, g7, g8,
              show decide (w.status = stEXECUTED) = false from decide_eq_false hnex,
              Bool.false_eq_true, ↓reduceIte]
            iframe Hy Hyid Hlcmds Hlcmds2 Hyl Hcp Hlprs Hlpr
            isplitr
            · iexists _; iexact Hd0
            isplitr
            · ipureintro; exact Hlbnn
            isplitr
            · iexists _; iexact Hd0
            ipureintro; exact Hlprsl
          ihave Hins := Hclose $$ %ptr %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt
            (some (parInstS w lb m))) [Hptrs] Hx
          · rw [hset]; iexact Hptrs
          rw [updP_instAtP]
          ihave Hrep : ownRep γ i r ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩ (parInstS w lb m))
            $$ [Hins Hrest]
          · iapply ownRep_of
            rw [ownRepRest_setInst]
            iframe Hrest
            isplitr
            · ipureintro; simpa [RState.setInst] using instBounds_upd _ _ _ Hib hq' hw.hn.2
            isplitr
            · ipureintro; simpa [RState.setInst] using Hcb
            simp only [RState.setInst, bumpRecvBallot_inst]
            iapply (repInsts_P γ i r _).2
            iexact Hins
          ihave #Hdur := isReplicaFw_durable _ _ _ _ _ _ $$ Hfw
          wp_apply wp_recordInstanceMetadata $$ [$Hrr $Hdur]
          wp_apply wp_sync_e $$ [$Hrr $Hdur]
          have hm4S := hm4
          rw [hfst, hsl, if_neg Bool.false_ne_true, if_pos (rfl : true = true)] at hm4S
          have houts := hw.houts
          rw [hm4S] at houts
          have hmA := houts _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
          rw [hm4S]
          ihave ⟨Hob, Hpd, Hcur⟩ := outsOk_bcast2 γ i _ _ _ (noSends_ev [_, _]) $$ Houts
          have hwfS : RepWf i ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩ (parInstS w lb m)) ord :=
            ⟨by simpa [RState.setInst] using hw.hrep.id, hw.hrep.hi,
              by simpa [RState.setInst] using hw.hrep.po⟩
          wp_apply (wp_bcastAccept hS γ i r rr L p Rext ord _ m.replica m.inst (parInstS w lb m)
            (parLbS lb m) hwfS hw.hq hw.hn (by simp [RState.setInst, upd]) rfl hdoK hmA hw.hord)
            $$ [Hrep Hf Hpd Hob]
          · iframe Hrep Hf Hpd Hob
            unfold hdCtx; iexact Hctx0
          iintro ⟨Hrep, Hf, Hpd, Hob⟩
          -- `r.Stats.M["slow"]++` under `r.M` (`allCommitted` is `true`: no `weird`)
          ihave #Hlock := isReplicaFw_lock _ _ _ _ _ _ $$ Hfw
          try wp_auto
          wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HR⟩
          unfold fwLockInv
          icases HR with ⟨Hcore, Hext⟩
          icases fwCore_stats _ _ _ _ $$ Hcore with ⟨%sm, Hsm, Hcl⟩
          ihave #HStm2 := HStm
          iStructNamed HStm2
          wp_auto
          wp_apply wp_map_lookup1 $$ [$Hsm] as Hsm
          try wp_auto
          wp_apply wp_mapInsert $$ [$Hsm] as Hsm
          try wp_auto
          ihave Hcore := Hcl $$ Hsm
          wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hcore Hext]
          · iframe Hcore Hext
          try wp_auto
          iapply HΦ
          unfold repDone
          iexists _
          iframe Hf Hrep
          unfold repIdle outboxesNil; iframe Hob Hpd Hcur
      · -- the fast path: `lb.status = COMMITTED`
        have hnex : w.status ≠ stEXECUTED := by
          intro hex; rw [hex] at hc; revert hc; decide
        obtain ⟨hs1, hs2, hs3⟩ := parLb4_same lb m
        have hd4 := parLb4_deps lb m mg hmgv hdeps4
        imod ownSlice_persist $$ Hd0 with #Hd0
        iclear Hycmds Hydeps
        ihave ⟨Hlcmds, Hlcmds2⟩ := par_cmdsRep_dup2 _ _ $$ Hlcmds
        unfold epaxos.COMMITTED
        wp_auto
        icases pt_name_lb _ _ $$ Hyl with ⟨%yl5, Hyl, %Hyl5⟩
        icases pt_name_inst _ _ $$ Hy with ⟨%y5, Hy, %Hy5⟩
        have hyf5 : instFields y5 (parInstF w lb m) := by
          subst Hy5
          obtain ⟨a1, a2, a3, a4, a5⟩ := Hyf
          obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := Hyl4.1
          exact ⟨b1, a2, rfl, b10, fun _ => a5 hnex⟩
        have hlf5 : lbFields yl5 (parLbF lb m) := by
          subst Hyl5
          obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := Hyl4.1
          exact ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl, b10, b11, b12⟩
        have hy5 : y5.id' = y.id' ∧ y5.Cmds' = yl.cmds' ∧ y5.Deps' = yl1.deps' ∧ y5.lb' = y.lb' := by
          subst Hy5; exact ⟨rfl, Hyl4.2.2.2.1, Hyl4.2.1, rfl⟩
        have hyl5 : yl5.cmds' = yl.cmds' ∧ yl5.deps' = yl1.deps' ∧
            yl5.clientProposals' = yl.clientProposals' ∧ yl5.prepareReplies' = yl.prepareReplies' := by
          subst Hyl5; exact ⟨Hyl4.2.2.2.1, Hyl4.2.1, Hyl4.2.2.1, Hyl4.2.2.2.2⟩
        have hF : (parInstF w lb m).cmds = lb.cmds ∧ (parInstF w lb m).deps = mg.2.1 ∧
            (parLbF lb m).cmds = lb.cmds ∧ (parLbF lb m).deps = mg.2.1 ∧
            (parLbF lb m).clientProposals = lb.clientProposals ∧
            (parLbF lb m).prepareReplies = lb.prepareReplies ∧
            lbDepsOwned (parLbF lb m) = false ∧
            decide ((parInstF w lb m).status = stEXECUTED) = false := by
          refine ⟨hs2, hd4, hs2, hd4, hs1, hs3, ?_, ?_⟩ <;>
            simp [lbDepsOwned, parLbF, parInstF, stCOMMITTED, stACCEPTED, stPREACCEPTED,
              stPREACCEPTED_EQ, stEXECUTED]
        have hdoK := hF.2.2.2.2.2.2.1
        ihave Hx := slot_close_gen (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr y5 (parInstF w lb m)
            (parLbF lb m) yl5 gs prs hyf5 rfl hlf5
          $$ [Hy Hlcmds Hlcmds2 Hyl Hcp Hlprs Hlpr]
        · obtain ⟨e1, e2, e3, e4⟩ := hy5
          obtain ⟨f1, f2, f3, f4⟩ := hyl5
          obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hF
          simp only [e1, e2, e3, e4, f1, f2, f3, f4, g1, g2, g3, g4, g5, g6, g7, g8,
            show decide (w.status = stEXECUTED) = false from decide_eq_false hnex,
            Bool.false_eq_true, ↓reduceIte]
          iframe Hy Hyid Hlcmds Hlcmds2 Hyl Hcp Hlprs Hlpr
          isplitr
          · iexists _; iexact Hd0
          isplitr
          · ipureintro; exact Hlbnn
          isplitr
          · iexists _; iexact Hd0
          ipureintro; exact Hlprsl
        ihave Hins := Hclose $$ %ptr %(fun pt => iprop(⌜pt = ptr⌝ ∗
            instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some (parInstF w lb m)))) [Hptrs] [Hx]
        · rw [hset]; iexact Hptrs
        · isplitr
          · ipureintro; rfl
          iexact Hx
        rw [updP_instAtP_irrel γ i σ.inst ⟨toN m.replica, toN m.inst⟩ (some (parInstF w lb m))]
        unfold ownRepRest
        icases Hrest with ⟨Hcrt, Hcut, Heut, Hconf, Hmsk, HmaxSeq, Hlead, Hmrb, Hstore, Hpeer⟩
        have hxc : ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩ (parInstF w lb m)).inst
            ⟨toN m.replica, toN m.inst⟩ = some (parInstF w lb m) := by simp [RState.setInst, upd]
        have hibc : instBounds ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩
            (parInstF w lb m)).inst := by
          simpa [RState.setInst] using instBounds_upd _ _ _ Hib hq' hw.hn.2
        have hcbc : cutBounds ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩
            (parInstF w lb m)).committedUpTo := by simpa [RState.setInst] using Hcb
        ihave #Hdur := isReplicaFw_durable _ _ _ _ _ _ $$ Hfw
        wp_apply wp_recordInstanceMetadata $$ [$Hrr $Hdur]
        wp_apply wp_sync_e $$ [$Hrr $Hdur]
        wp_apply (wp_updateCommittedP γ i r rr L p Rext
          ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩ (parInstF w lb m)) m.replica
          hw.hq hibc hcbc _ (ptrSlot_status γ i _ ⟨toN m.replica, toN m.inst⟩ ptr (parInstF w lb m) hxc))
          $$ [$Hrr $Hfw Hins Hcut] as ⟨Hins, Hcut⟩
        · simp only [RState.setInst, bumpRecvBallot_inst, bumpRecvBallot_cut]
          iframe Hins Hcut
        -- `inst.lb.clientProposals != nil && !r.Dreply`: the slot read again
        icases repInstsP_acc r _ ⟨toN m.replica, toN m.inst⟩ hq' hn' $$ Hins with
          ⟨%iss2, %rows2, %row2, %ptrs2, %ptr2, #Hiss2, #Hrows2, %Hrow2, Hptrs2, %Hptr2, Hx2, Hclose2⟩
        ihave Hx2 := updP_apply_self _ _ _ _ $$ Hx2
        icases Hx2 with ⟨%He2, Hx2⟩
        subst He2
        ihave Hx2 := (instAt_some γ i _ ptr2 _ rfl).1 $$ Hx2
        unfold ownInst
        icases Hx2 with ⟨%y2, Hy2, %Hyf2, #Hyid2, Hycmds2, Hydeps2, Hylb2⟩
        simp only [show (parInstF w lb m).lb = some (parLbF lb m) from rfl]
        icases Hylb2 with ⟨%Hlbnn2, Hlb2⟩
        unfold ownLb
        icases Hlb2 with ⟨%yl2, %gs2, %prs2, Hyl2, %Hylf2, Hcp2, Hlcmds2, Hldeps2, Hlprs2, %Hlprsl2, Hlpr2⟩
        wp_auto
        generalize decide (yl2.clientProposals' = slice.nil) = bnil
        cases bnil <;> wp_auto
        all_goals
          ihave Hx2 := slot_close_gen (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr2 y2 (parInstF w lb m) (parLbF lb m) yl2
            gs2 prs2 Hyf2 rfl Hylf2 $$ [Hy2 Hycmds2 Hydeps2 Hyl2 Hcp2 Hlcmds2 Hldeps2 Hlprs2 Hlpr2]
          · iframe
            isplitl []
            · iexact Hyid2
            ipureintro; exact ⟨Hlbnn2, Hlprsl2⟩
          ihave Hins := Hclose2 $$ %ptr2 %(ptrQ γ i ⟨toN m.replica, toN m.inst⟩ ptr2 (parInstF w lb m))
            [Hptrs2] [Hx2]
          · have hset2 : ptrs2.set (toN m.inst) ptr2 = ptrs2 := by
              have := List.getElem?_eq_some_iff.mp Hptr2.1
              rw [← this.2]; exact List.set_getElem_self this.1
            rw [hset2]; iexact Hptrs2
          · unfold ptrQ; isplitr
            · ipureintro; rfl
            iexact Hx2
          rw [updP_updP]
          have hm4F := hm4
          rw [hfst, if_pos (rfl : true = true)] at hm4F
          have houts := hw.houts
          rw [hm4F] at houts
          have hm := houts _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
          rw [hm4F]
          ihave ⟨Hob, Hpd, Hcur⟩ := outsOk_bcast2 γ i _ _ _ (noSends_ev [_, _]) $$ Houts
          have hwf' : RepWf i (updateCommitted ((bumpRecvBallot σ m.ballot).setInst
              ⟨toN m.replica, toN m.inst⟩ (parInstF w lb m)) (toN m.replica)) ord :=
            ⟨by simp [updateCommitted, RState.setInst, hw.hrep.id], hw.hrep.hi,
              by simp [updateCommitted, RState.setInst, hw.hrep.po]⟩
          wp_apply (wp_bcastCommitKeep hS γ i r rr L p Rext ord _ m.replica m.inst (parInstF w lb m)
            (parLbF lb m) ptr2 hwf' hw.hq hw.hn (by simpa [updateCommitted] using hxc) rfl hdoK hm
            hw.hord)
            $$ [Hins Hcrt Heut Hconf Hmsk HmaxSeq Hlead Hmrb Hstore Hpeer Hcut Hf Hpd Hob]
          · isplitl []
            · unfold hdCtx; iexact Hctx0
            isplitr
            · ipureintro; simpa [updateCommitted, RState.setInst] using instBounds_upd _ _ _ Hib hq' hw.hn.2
            isplitr
            · ipureintro; exact cutBounds_updateCommitted _ _ hibc hcbc
            rw [show (updateCommitted ((bumpRecvBallot σ m.ballot).setInst
                ⟨toN m.replica, toN m.inst⟩ (parInstF w lb m)) (toN m.replica)).inst =
                upd σ.inst ⟨toN m.replica, toN m.inst⟩ (some (parInstF w lb m)) by
              simp [updateCommitted, RState.setInst]]
            rw [ownRepRest_updC]
            simp only [RState.setInst, bumpRecvBallot_inst]
            iframe
          iintro ⟨Hins, Hrest, Hf, Hpd, Hob⟩
          ihave #Hlock := isReplicaFw_lock _ _ _ _ _ _ $$ Hfw
          try wp_auto
          wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HR⟩
          unfold fwLockInv
          icases HR with ⟨Hcore, Hext⟩
          icases fwCore_stats _ _ _ _ $$ Hcore with ⟨%sm, Hsm, Hcl⟩
          ihave #HStm2 := HStm
          iStructNamed HStm2
          wp_auto
          wp_apply wp_map_lookup1 $$ [$Hsm] as Hsm
          try wp_auto
          wp_apply wp_mapInsert $$ [$Hsm] as Hsm
          icases repInstsP_acc r _ ⟨toN m.replica, toN m.inst⟩ hq' hn' $$ Hins with
            ⟨%iss3, %rows3, %row3, %ptrs3, %ptr3, #Hiss3, #Hrows3, %Hrow3, Hptrs3, %Hptr3, Hx3, Hclose3⟩
          ihave Hx3 := updP_apply_self _ _ _ _ $$ Hx3
          unfold ptrQ
          icases Hx3 with ⟨%He3, Hx3⟩
          subst He3
          ihave Hx3 := (instAt_some γ i _ ptr3 _ rfl).1 $$ Hx3
          unfold ownInst
          icases Hx3 with ⟨%y3, Hy3, %Hyf3, Hrest3⟩
          wp_auto
          generalize decide (y3.proposeTime' = W64 0) = bz
          cases bz
          · try wp_auto
            wp_apply wp_map_lookup1 $$ [$Hsm] as Hsm
            wp_apply time.wp_Now as %tnow -
            wp_apply time.Time.wp_UnixNano' as %ns -
            wp_apply wp_mapInsert $$ [$Hsm] as Hsm
            try wp_auto
            ihave Hcore := Hcl $$ Hsm
            wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hcore Hext]
            · iframe Hcore Hext
            ihave Hx3 : instAt γ i ⟨toN m.replica, toN m.inst⟩ ptr3 (some (parInstF w lb m)) $$ [Hy3 Hrest3]
            · iapply (instAt_some γ i _ ptr3 _ rfl).2
              unfold ownInst
              iexists y3
              iframe Hy3 Hrest3
              ipureintro; exact Hyf3
            have hset3 : ptrs3.set (toN m.inst) ptr3 = ptrs3 := by
              have := List.getElem?_eq_some_iff.mp Hptr3.1
              rw [← this.2]; exact List.set_getElem_self this.1
            ihave Hins := Hclose3 $$ %ptr3 %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some (parInstF w lb m)))
              [Hptrs3] Hx3
            · rw [hset3]; iexact Hptrs3
            rw [updP_updP, updP_instAtP, upd_self _ _ _ (by simpa [updateCommitted] using hxc)]
            try wp_auto
            iapply HΦ
            unfold repDone
            iexists _
            iframe Hf
            isplitl [Hins Hrest]
            · iapply ownRep_of
              iframe Hrest
              isplitr
              · ipureintro; simpa [updateCommitted] using hibc
              isplitr
              · ipureintro; exact cutBounds_updateCommitted _ _ hibc hcbc
              iapply (repInsts_P γ i r _).2
              iexact Hins
            unfold repIdle outboxesNil; iframe Hob Hpd Hcur
          · try wp_auto
            ihave Hcore := Hcl $$ Hsm
            wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hcore Hext]
            · iframe Hcore Hext
            ihave Hx3 : instAt γ i ⟨toN m.replica, toN m.inst⟩ ptr3 (some (parInstF w lb m)) $$ [Hy3 Hrest3]
            · iapply (instAt_some γ i _ ptr3 _ rfl).2
              unfold ownInst
              iexists y3
              iframe Hy3 Hrest3
              ipureintro; exact Hyf3
            have hset3 : ptrs3.set (toN m.inst) ptr3 = ptrs3 := by
              have := List.getElem?_eq_some_iff.mp Hptr3.1
              rw [← this.2]; exact List.set_getElem_self this.1
            ihave Hins := Hclose3 $$ %ptr3 %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some (parInstF w lb m)))
              [Hptrs3] Hx3
            · rw [hset3]; iexact Hptrs3
            rw [updP_updP, updP_instAtP, upd_self _ _ _ (by simpa [updateCommitted] using hxc)]
            try wp_auto
            iapply HΦ
            unfold repDone
            iexists _
            iframe Hf
            isplitl [Hins Hrest]
            · iapply ownRep_of
              iframe Hrest
              isplitr
              · ipureintro; simpa [updateCommitted] using hibc
              isplitr
              · ipureintro; exact cutBounds_updateCommitted _ _ hibc hcbc
              iapply (repInsts_P γ i r _).2
              iexact Hins
            unfold repIdle outboxesNil; iframe Hob Hpd Hcur

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
