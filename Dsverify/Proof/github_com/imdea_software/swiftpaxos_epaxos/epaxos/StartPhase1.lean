/-
`startPhase1` against the model's `startPhase1`: the new instance and bookkeeping (slot `x`
overwritten: the caller hands it over as `ownRepHole`), `updateAttributes`, `updateConflicts`,
`maxSeq`, `bcastPreAccept`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.BcastOthers
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Attributes
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.UpdateConflicts
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.NewInstance
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Record

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

theorem nilDeps_set {α : Type} (a b : α) (k : Nat) (hk : k < 5) :
    (List.replicate k a ++ List.replicate (5 - k) b).set k a =
      List.replicate (k + 1) a ++ List.replicate (5 - (k + 1)) b := by
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem depsOk_nil : depsOk (List.replicate nR (W32 (-1))) := by
  refine ⟨by simp, ?_⟩
  intro d hd
  left
  rw [List.eq_of_mem_replicate hd]
  rfl

/-! ## The model's `startPhase1`, named -/

/-- `updateAttributes` from seq 0 and deps all `-1`. -/
def spAttrs (σ : RState) (cmds : List WCmd) : w32 × List w32 × Bool :=
  updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))

/-- The new bookkeeping. -/
def spLb (σ : RState) (cmds : List WCmd) (ballot : w32) (props : Option (List Proposal)) :
    LbRec :=
  { clientProposals := props, ballot := W32 (-1), allEqual := true,
    preAcceptOKs := W64 0, acceptOKs := W64 0, nacks := W64 0, prepareReplies := [],
    preparing := false, tryingToPreAccept := false, lastTriedBallot := ballot,
    cmds := some cmds, status := stPREACCEPTED, seq := W32 (-1), deps := (spAttrs σ cmds).2.1,
    leaderResponded := false, preAcceptsSent := W64 0 }

/-- The new instance. -/
def spInst (σ : RState) (cmds : List WCmd) (x : InstId) (ballot : w32)
    (props : Option (List Proposal)) : InstRec :=
  { cmds := some cmds, bal := ballot, vbal := ballot, status := stPREACCEPTED,
    seq := (spAttrs σ cmds).1, deps := (spAttrs σ cmds).2.1, lb := some (spLb σ cmds ballot props),
    id := x }

/-- `startPhase1`'s state before `maxSeq`. -/
def spSt1 (σ : RState) (cmds : List WCmd) (x : InstId) (n ballot : w32)
    (props : Option (List Proposal)) : RState :=
  updateConflicts (σ.setInst x (spInst σ cmds x ballot props)) cmds x.q n (spAttrs σ cmds).1

/-- `startPhase1`'s final state. -/
def spSt (σ : RState) (cmds : List WCmd) (x : InstId) (n ballot : w32)
    (props : Option (List Proposal)) : RState :=
  if (spSt1 σ cmds x n ballot props).maxSeq.sle (spAttrs σ cmds).1 then
    { spSt1 σ cmds x n ballot props with maxSeq := (spAttrs σ cmds).1 }
  else spSt1 σ cmds x n ballot props

theorem startPhase1_fst (σ : RState) (cmds : List WCmd) (x : InstId) (replica n ballot : w32)
    (props : Option (List Proposal)) :
    (startPhase1 σ cmds x replica n ballot props).1 = spSt σ cmds x n ballot props := rfl

theorem startPhase1_snd (σ : RState) (cmds : List WCmd) (x : InstId) (replica n ballot : w32)
    (props : Option (List Proposal)) :
    (startPhase1 σ cmds x replica n ballot props).2 =
      [Out.ev (.phase1 x ballot (lbVal (spLb σ cmds ballot props))),
       Out.ev (.vote x ballot stPREACCEPTED ⟨cmds, (spAttrs σ cmds).1, (spAttrs σ cmds).2.1⟩),
       Out.ev (.attrsRec x cmds (spAttrs σ cmds).2.1)] ++
      [Out.bcast (bcastPreAcceptOf (spSt σ cmds x n ballot props) x
        (preAcceptOf (spSt σ cmds x n ballot props) replica n (spLb σ cmds ballot props)))] := rfl

/-- `updateConflicts` changes only the conflicts, `lastScan`/`lastPut` and `maxSeqPerKey`. -/
theorem uc_shape (σ : RState) (cmds : List WCmd) (q : Nat) (n seq : w32) :
    updateConflicts σ cmds q n seq =
      { σ with conflicts := (updateConflicts σ cmds q n seq).conflicts,
               lastScan := (updateConflicts σ cmds q n seq).lastScan,
               lastPut := (updateConflicts σ cmds q n seq).lastPut,
               maxSeqPerKey := (updateConflicts σ cmds q n seq).maxSeqPerKey } :=
  updateConflicts_eq σ cmds q n seq

theorem uc_congr (σ σ' : RState) (cmds : List WCmd) (q : Nat) (n seq : w32)
    (h1 : σ.conflicts = σ'.conflicts) (h2 : σ.maxSeqPerKey = σ'.maxSeqPerKey) :
    (updateConflicts σ cmds q n seq).conflicts = (updateConflicts σ' cmds q n seq).conflicts ∧
    (updateConflicts σ cmds q n seq).maxSeqPerKey =
      (updateConflicts σ' cmds q n seq).maxSeqPerKey := by
  unfold updateConflicts
  induction cmds generalizing σ σ' with
  | nil => exact ⟨h1, h2⟩
  | cons c cs ih =>
    simp only [List.foldl_cons]
    apply ih
    · simp only [h1, h2]
    · simp only [h1, h2]

theorem spSt1_eq (σ : RState) (cmds : List WCmd) (x : InstId) (n ballot : w32)
    (props : Option (List Proposal)) :
    spSt1 σ cmds x n ballot props =
      { σ with inst := upd σ.inst x (some (spInst σ cmds x ballot props)),
               conflicts := (updateConflicts σ cmds x.q n (spAttrs σ cmds).1).conflicts,
               lastScan := (updateConflicts σ cmds x.q n (spAttrs σ cmds).1).lastScan,
               lastPut := (updateConflicts σ cmds x.q n (spAttrs σ cmds).1).lastPut,
               maxSeqPerKey := (updateConflicts σ cmds x.q n (spAttrs σ cmds).1).maxSeqPerKey } := by
  have hc := uc_congr (σ.setInst x (spInst σ cmds x ballot props)) σ cmds x.q n
    (spAttrs σ cmds).1 rfl rfl
  have hl := updateConflicts_cls (σ.setInst x (spInst σ cmds x ballot props)) σ cmds x.q n
    (spAttrs σ cmds).1 rfl rfl
  unfold spSt1
  rw [uc_shape, hc.1, hc.2, hl.1, hl.2]
  rfl

theorem spSt_eq (σ : RState) (cmds : List WCmd) (x : InstId) (n ballot : w32)
    (props : Option (List Proposal)) :
    spSt σ cmds x n ballot props =
      { σ with inst := upd σ.inst x (some (spInst σ cmds x ballot props)),
               conflicts := (updateConflicts σ cmds x.q n (spAttrs σ cmds).1).conflicts,
               lastScan := (updateConflicts σ cmds x.q n (spAttrs σ cmds).1).lastScan,
               lastPut := (updateConflicts σ cmds x.q n (spAttrs σ cmds).1).lastPut,
               maxSeqPerKey := (updateConflicts σ cmds x.q n (spAttrs σ cmds).1).maxSeqPerKey,
               maxSeq := if σ.maxSeq.sle (spAttrs σ cmds).1 then (spAttrs σ cmds).1
                 else σ.maxSeq } := by
  unfold spSt
  rw [spSt1_eq]
  split <;> simp_all

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- `sync()`: nothing without a durable log (`Durable` is false). -/
theorem wp_sync (r rr : Loc) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ fld rr go!"Durable" ↦□ false }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"sync")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hrr, #Hd⟩
  wp_auto
  wp_end

/-- `newLeaderBookkeeping(p, originalDeps, committedDeps, deps, lastTriedBallot, cmds, status,
seq)`: a fresh bookkeeping (`possibleQuorum` a fresh slice, not tracked). -/
theorem wp_newLeaderBookkeeping (r rr : Loc) (N : w64) (hN : 0 ≤ sint.Z N) (ps od cd d : GoSlice)
    (ltb : w32) (cmds : GoSlice) (st : w8) (seq : w32) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ fld rr go!"N" ↦□ N }}
      (App (App (App (App (App (App (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty
        @!! go!"newLeaderBookkeeping")) (Val #ps)) (Val #od)) (Val #cd)) (Val #d)) (Val #ltb))
        (Val #cmds)) (Val #st)) (Val #seq))
    {{ (l : Loc), RET #l; ⌜l ≠ null⌝ ∗ ∃ pq : GoSlice,
        l ↦ epaxos.LeaderBookkeeping.mk ps (W32 (-1)) true (W64 0) (W64 0) (W64 0) od cd
          slice.nil true false pq (W64 0) false ltb cmds st seq d false (W64 0) }} := by
  wp_start as ⟨#Hrr, #HN⟩
  wp_auto
  wp_apply (wp_slice_make2 (V := Bool) N) as %pq ⟨-, -⟩
  · ipureintro; exact hN
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$r0»
  iapply HΦ
  isplitr
  · ipureintro; exact Hnn
  iexists pq
  iexact «$r0»

/-- The heap image of `startPhase1`'s new instance (`deps` one read-only array shared by the
instance and its bookkeeping). -/
theorem ownInst_sp (γ : EpNames) (i : Nat) (x : InstId) (σ : RState) (cmds : List WCmd)
    (ballot : w32) (props : Option (List Proposal)) (replica n : w32)
    (hxq : W32 (x.q : Int) = replica) (hxi : W32 (x.i : Int) = n) (ip idp lbp : Loc)
    (cs dsl csl pq prs : GoSlice) (t : w64) (hcs : cs ≠ slice.nil) (hlbp : lbp ≠ null) :
    ip ↦ epaxos.Instance.mk cs ballot ballot (W8 1) (spAttrs σ cmds).1 dsl lbp (W64 0) (W64 0)
        GoInterface.nil t idp ∗
      idp ↦□ epaxos.instanceId.mk replica n ∗
      lbp ↦ epaxos.LeaderBookkeeping.mk prs (W32 (-1)) true (W64 0) (W64 0) (W64 0) dsl csl
        slice.nil false false pq (W64 0) false ballot cs (W8 1) (W32 (-1)) dsl false (W64 0) ∗
      propsOwn (GF := GF) γ i prs props ∗ ownCmds cs cmds DFrac.discard ∗ dsl ↦*□ (spAttrs σ cmds).2.1 ⊢
    ownInst γ i x ip (spInst σ cmds x ballot props) := by
  iintro ⟨Hip, #Hid, Hlbp, Hprops, #Hcs, #Hd⟩
  unfold ownInst
  iexists epaxos.Instance.mk cs ballot ballot (W8 1) (spAttrs σ cmds).1 dsl lbp (W64 0) (W64 0)
    GoInterface.nil t idp
  simp only [spInst]
  iframe Hip
  isplitr
  · ipureintro; and_intros <;> first | rfl | trivial | (intro; rfl)
  isplitr
  · simp only [hxq, hxi]; iexact Hid
  isplitr
  · simp only [cmdsRep]
    iframe Hcs
    ipureintro; exact hcs
  isplitr
  · iexists DFrac.discard; iexact Hd
  isplitr
  · ipureintro; exact hlbp
  have hdo : lbDepsOwned (spLb σ cmds ballot props) = false := by
    simp [lbDepsOwned, spLb]
  unfold ownLb
  rw [hdo]
  have hne : decide (stPREACCEPTED = stEXECUTED) = false := by decide
  try simp only [hne]
  rcases props with _ | ps
  · unfold propsOwn
    icases Hprops with %Hprs
    iexists epaxos.LeaderBookkeeping.mk prs (W32 (-1)) true (W64 0) (W64 0) (W64 0) dsl csl
      slice.nil false false pq (W64 0) false ballot cs (W8 1) (W32 (-1)) dsl false (W64 0), [], []
    simp only [spLb]
    iframe Hlbp
    isplitr
    · ipureintro; and_intros <;> first | rfl | trivial
    isplitr
    · ipureintro; exact Hprs
    isplitr
    · simp only [cmdsRep]
      iframe Hcs
      ipureintro; exact hcs
    isplitr
    · simp only [Bool.false_eq_true, ite_false]; iexists DFrac.discard; iexact Hd
    isplitl []
    · isplitl []
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
    isplitr
    · ipureintro; rfl
    iempintro
  · unfold propsOwn
    icases Hprops with ⟨%gs, %Hgs, #Hgs, Hheld⟩
    iexists epaxos.LeaderBookkeeping.mk prs (W32 (-1)) true (W64 0) (W64 0) (W64 0) dsl csl
      slice.nil false false pq (W64 0) false ballot cs (W8 1) (W32 (-1)) dsl false (W64 0), gs, []
    simp only [spLb]
    iframe Hlbp Hgs
    isplitr
    · ipureintro; and_intros <;> first | rfl | trivial
    isplitl [Hheld]
    · isplitr
      · ipureintro; exact Hgs
      have hne' : ¬ (stPREACCEPTED = stEXECUTED) := by decide
      simp only [hne', decide_false]
      iexact Hheld
    isplitr
    · simp only [cmdsRep]
      iframe Hcs
      ipureintro; exact hcs
    isplitr
    · simp only [Bool.false_eq_true, ite_false]; iexists DFrac.discard; iexact Hd
    isplitl []
    · isplitl []
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
    isplitr
    · ipureintro; rfl
    iempintro

set_option maxHeartbeats 4000000 in
/-- `startPhase1(cmds, replica, instance, ballot, proposals)` for `x = replica.instance`: from
the state with slot `x` about to be overwritten, the proposals' ownership (`propsOwn`), and the
ghost step's outputs (the replica's fragment already at the model's result, the pending
`bcastPreAccept`), the handler ends in the lock's invariant shape. -/
theorem wp_startPhase1 (hS : replica.Replica.SendMsg.spec (GF := GF)) (γ : EpNames) (i : Nat) (r rr : Loc)
    (L : List GoString) (p : FwPtrs) (Rext : IProp GF) (ord : List w32) (σ : RState)
    (cs : GoSlice) (cmds : List WCmd) (replica n ballot : w32) (prs : GoSlice)
    (props : Option (List Proposal)) (hwf : RepWf i σ ord)
    (hq : 0 ≤ zz replica ∧ zz replica < nR) (hn : 0 ≤ zz n ∧ toN n + 1 < MAX_INSTANCE)
    (hcs : cs ≠ slice.nil) (hconf : ConfWf σ) (hord : ∀ o ∈ ord, 0 ≤ sint.Z o)
    (hout : OutsWf (startPhase1 σ cmds ⟨toN replica, toN n⟩ replica n ballot props).2) :
    {{ hdCtx γ i r rr L p Rext ord ∗ ownRepHole γ i r σ ⟨toN replica, toN n⟩ ∗
        ownCmds cs cmds DFrac.discard ∗ propsOwn γ i prs props ∗
        repFrag γ i (startPhase1 σ cmds ⟨toN replica, toN n⟩ replica n ballot props).1 ∗
        outsOk γ i (startPhase1 σ cmds ⟨toN replica, toN n⟩ replica n ballot props).2 }}
      (App (App (App (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty
        @!! go!"startPhase1")) (Val #cs)) (Val #replica)) (Val #n)) (Val #ballot)) (Val #prs))
    {{ RET #(); repDone γ i r }} := by
  wp_start as ⟨#Hctx, Hhole, Hcs, Hprops, Hf, Houts⟩
  ihave #Hctx0 := Hctx
  unfold hdCtx
  icases Hctx with ⟨#Hpe, #Hpr, #Hrr, #Hfw, #Hro, #Hinv, #Hpo⟩
  ihave #Hfro := isReplicaFw_ro _ _ _ _ _ _ $$ Hfw
  ihave ⟨#HN, #HF, #HId, #HSt, #HRPC, #HPC, #HThr, #HEx, #HDr, #HSh, #HStats, #HStm, #HAl, %HLn⟩ :=
    fwRO_fields _ _ _ _ _ $$ Hfro
  ihave #HDur := isReplicaFw_durable _ _ _ _ _ _ $$ Hfw
  have hL5 : L.length = nR := HLn.1
  unfold ownRepHole
  icases Hhole with ⟨%Hib, %Hcb, Hinsts, Hrest⟩
  unfold ownRepRest
  icases Hrest with ⟨Hcrt, Hcut, Heut, Hconf, Hmsk, HmaxSeq, Hlead, Hmrb, Hstore, Hpeer, HlS, HlP⟩
  have hL : ((L.length : Nat) : Int) = 5 := by rw [hL5]; rfl
  rw [hL]
  wp_auto
  wp_apply (wp_slice_make2 (V := w32) (W64 5)) as %dsl ⟨Hdsl, -⟩
  · ipureintro; decide
  irename : (instance_ptr ↦ n : IProp GF) => Hinstance
  -- `deps[q] = -1` for every `q`
  ihave %Hdl := ownSlice_len _ _ _ $$ Hdsl
  have hdl : sint.Z dsl.len = 5 := by
    have h1 := Hdl.1; have := Hdl.2; simp only [List.length_replicate] at h1; word
  ihave HI : (∃ k : Nat, "Hq" ∷ q_ptr ↦ W64 (k : Int) ∗
      "Hd" ∷ dsl ↦* (List.replicate k (W32 (-1)) ++ List.replicate (5 - k) (W32 0)) ∗
      "%Hk" ∷ ⌜k ≤ 5⌝ : IProp GF) $$ [q Hdsl]
  · iexists 0
    iframe
    ipureintro; omega
  wp_for HI
  wp_if_destruct
  · have hk5 : k < 5 := by
      have := Hif; have : sint.Z (W64 (k : Int)) = (k : Int) := by word
      word
    have hkk : sint.Z (W64 (k : Int)) = (k : Int) := by word
    rw [if_pos (by rw [hkk, hdl]; omega), hkk]
    wp_apply wp_store_slice_index $$ [Hd] as Hd
    · iframe; ipureintro; simp; omega
    wp_for_post
    iframe
    iexists k + 1
    simp only [Int.toNat_natCast]
    rw [nilDeps_set _ _ k hk5, show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
    iframe
    ipureintro; omega
  · have hk : k = 5 := by
      have := Hif; have : sint.Z (W64 (k : Int)) = (k : Int) := by word
      word
    subst hk
    ihave Hd : dsl ↦* List.replicate nR (W32 (-1)) $$ [Hd]
    · rw [show List.replicate 5 (W32 (-1)) ++ List.replicate (5 - 5) (W32 0) =
        List.replicate nR (W32 (-1)) from rfl]
      iexact Hd
    -- `updateAttributes`
    wp_apply (wp_updateAttributes γ i r rr L p σ _ (updP_seq γ i σ.inst ⟨toN replica, toN n⟩)
      hconf Hib cs cmds DFrac.discard (W32 0) dsl _ depsOk_nil replica n)
      $$ [$Hpe $Hrr $Hfro $Hinsts $Hconf $Hmsk $HlS $HlP $Hcs $Hd]
      as ⟨Hinsts, Hconf, Hmsk, HlS, HlP, Hcs, Hd⟩
    ipersist Hd
    ihave #Hcs := Hcs
    rw [show updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1))) = spAttrs σ cmds
      from rfl]
    -- `comDeps` (not tracked)
    wp_apply (wp_slice_make2 (V := w32) (W64 5)) as %csl ⟨Hcsl, -⟩
    · ipureintro; decide
    ihave %Hcl := ownSlice_len _ _ _ $$ Hcsl
    have hcl : sint.Z csl.len = 5 := by
      have h1 := Hcl.1; have := Hcl.2; simp only [List.length_replicate] at h1; word
    ihave HI : (∃ k : Nat, "Hq" ∷ i_ptr ↦ W64 (k : Int) ∗
        "Hd" ∷ csl ↦* (List.replicate k (W32 (-1)) ++ List.replicate (5 - k) (W32 0)) ∗
        "%Hk" ∷ ⌜k ≤ 5⌝ : IProp GF) $$ [«i» Hcsl]
    · iexists 0
      iframe
      ipureintro; omega
    wp_for HI
    wp_if_destruct
    · have hk5 : k < 5 := by
        have := Hif; have : sint.Z (W64 (k : Int)) = (k : Int) := by word
        word
      have hkk : sint.Z (W64 (k : Int)) = (k : Int) := by word
      rw [if_pos (by rw [hkk, hcl]; omega), hkk]
      wp_apply wp_store_slice_index $$ [Hd] as Hd
      · iframe; ipureintro; simp; omega
      wp_for_post
      iframe
      iexists k + 1
      simp only [Int.toNat_natCast]
      rw [nilDeps_set _ _ k hk5, show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
      iframe
      ipureintro; omega
    iclear Hd
    -- the new instance and bookkeeping
    unfold epaxos.PREACCEPTED
    wp_apply (wp_newInstance r replica n cs ballot ballot (W8 1) _ dsl)
      as %ip ⟨%Hipnn, %t, %idp, Hip, Hid⟩
    wp_apply (wp_newLeaderBookkeeping r rr (W64 5) (by decide) prs dsl csl dsl ballot cs (W8 1)
      (W32 (-1))) $$ [$Hpe $Hrr $HN] as %lbp ⟨%Hlbnn, %pq, Hlbp⟩
    -- `InstanceSpace[replica][instance] = inst`
    have hq' : toN replica < nR := by
      have := hq.1; have := hq.2; simp only [toN, zz] at *; omega
    have hn' : toN n < MAX_INSTANCE := by have := hn.2; omega
    icases repInstsP_acc r _ ⟨toN replica, toN n⟩ hq' hn' $$ Hinsts with
      ⟨%iss, %rows, %row, %ptrs, %ptr, #Hiss, #Hrows, %Hrow, Hptrs, %Hptr, -, Hclose⟩
    ihave %Hrlen := ownSlice_len _ _ _ $$ Hrows
    ihave %Hplen := ownSlice_len _ _ _ $$ Hptrs
    have e1 : sint.Z (W64 (sint.Z replica)) = sint.Z replica := by word
    have e2 : sint.Z (W64 (sint.Z n)) = sint.Z n := by word
    have hqe : (sint.Z replica).toNat = toN replica := rfl
    have hne : (sint.Z n).toNat = toN n := rfl
    have h1 : 0 ≤ sint.Z (W64 (sint.Z replica)) ∧ sint.Z (W64 (sint.Z replica)) < sint.Z iss.len := by
      have := hq.1; have hl := (List.getElem?_eq_some_iff.mp Hrow).1
      unfold toN zz at *; constructor <;> word
    have h2 : 0 ≤ sint.Z (W64 (sint.Z n)) ∧ sint.Z (W64 (sint.Z n)) < sint.Z row.len := by
      have := hn.1; have := hn.2; have := Hptr.2
      unfold toN zz at *; constructor <;> word
    wp_auto
    simp only [h1, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
    · ipureintro; rw [e1, hqe]; exact Hrow
    simp only [h2, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [$Hptrs] as Hptrs
    · ipureintro; have := Hplen.1; have := h2.2; constructor <;> word
    ipersist Hid
    have hxq : W32 ((toN replica : Nat) : Int) = replica := W32_toN replica hq.1
    have hxi : W32 ((toN n : Nat) : Int) = n := W32_toN n hn.1
    ihave Hins := Hclose $$ %ip
      %(fun pt => instAt γ i ⟨toN replica, toN n⟩ pt
        (some (spInst σ cmds ⟨toN replica, toN n⟩ ballot props))) [Hptrs]
      [Hip Hid Hlbp Hprops]
    · rw [show (sint.Z (W64 (sint.Z n))).toNat = toN n by rw [e2]; rfl]; iexact Hptrs
    · simp only [instAt]
      iapply ownInst_sp γ i ⟨toN replica, toN n⟩ σ cmds ballot props replica n hxq hxi ip idp lbp
        cs dsl csl pq prs t hcs Hlbnn
      iframe Hip Hlbp Hprops
      isplitl []
      · iexact Hid
      isplitl []
      · iexact Hcs
      iexact Hd
    have hP : updP (updP (instAtP (GF := GF) γ i σ.inst) ⟨toN replica, toN n⟩
        (slotSeq (σ.inst ⟨toN replica, toN n⟩))) ⟨toN replica, toN n⟩
        (fun pt => instAt γ i ⟨toN replica, toN n⟩ pt
          (some (spInst σ cmds ⟨toN replica, toN n⟩ ballot props))) =
        instAtP γ i (upd σ.inst ⟨toN replica, toN n⟩
          (some (spInst σ cmds ⟨toN replica, toN n⟩ ballot props))) := by
      funext y pt
      simp only [updP, instAtP, upd]
      split <;> simp_all
    ihave Hins := repInstsP_congr _ _ _ hP $$ Hins
    ihave Hins := (repInsts_P γ i r _).2 $$ Hins
    -- `updateConflicts`
    wp_apply (wp_updateConflicts r σ cs cmds DFrac.discard replica n (spAttrs σ cmds).1 hq)
      $$ [$Hpe $Hcs $Hconf $Hmsk $HlS $HlP] as ⟨-, Hconf, Hmsk, HlS, HlP⟩
    -- `maxSeq`
    have hms : (spSt σ cmds ⟨toN replica, toN n⟩ n ballot props).maxSeq =
        if σ.maxSeq.sle (spAttrs σ cmds).1 then (spAttrs σ cmds).1 else σ.maxSeq := by
      rw [spSt_eq]
    wp_join iprop(efld r go!"maxSeq" ↦ (spSt σ cmds ⟨toN replica, toN n⟩ n ballot props).maxSeq ∗
        seq_ptr ↦ (spAttrs σ cmds).1 ∗ r_ptr ↦ r)
      with [HmaxSeq seq r] as ⟨HmaxSeq, seq, r⟩
    · rw [hms, if_pos ((sle_iff _ _).mpr Hif)]
      iframe
    · rw [hms, if_neg (fun h => Hif ((sle_iff _ _).mp h))]
      iframe
    -- `recordInstanceMetadata(r.InstanceSpace[r.Id][instance])`: slot `r.Id.instance` read
    have hi : i < nR := hwf.hi
    icases repInsts_acc γ i r _ ⟨i, toN n⟩ hi hn' $$ Hins with
      ⟨%iss', %rows', %row', %ptrs', %ptr', #Hiss', #Hrows', %Hrow', Hptrs', %Hptr', Hx', Hclose'⟩
    icombine Hiss Hiss' gives %Heqi
    subst Heqi
    ihave %Heqr := ownSlice_agree _ _ _ _ _ $$ Hrows Hrows'
    subst Heqr
    ihave %Hplen2 := ownSlice_len _ _ _ $$ Hptrs'
    have ei : sint.Z (W64 (sint.Z (W32 (i : Int)))) = (i : Int) := by
      have : i < 5 := hi; word
    have h1' : 0 ≤ sint.Z (W64 (sint.Z (W32 (i : Int)))) ∧
        sint.Z (W64 (sint.Z (W32 (i : Int)))) < sint.Z iss.len := by
      have hl : i < rows.length := (List.getElem?_eq_some_iff.mp Hrow').1
      have := Hrlen.1; have := Hrlen.2
      rw [ei]; constructor <;> word
    have h2' : 0 ≤ sint.Z (W64 (sint.Z n)) ∧ sint.Z (W64 (sint.Z n)) < sint.Z row'.len := by
      have := hn.1; have := hn.2; have := Hptr'.2; have := Hplen2.1
      unfold toN zz at *; constructor <;> word
    simp only [h1', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index iss _ rows _ row' h1'.1 $$ [$Hrows] as -
    · ipureintro; rw [ei]; exact Hrow'
    simp only [h2', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index row' _ ptrs' _ ptr' h2'.1 $$ [$Hptrs'] as Hptrs'
    · ipureintro; rw [e2, hne]; exact Hptr'.1
    have hset' : ptrs'.set (toN n) ptr' = ptrs' := by
      have := List.getElem?_eq_some_iff.mp Hptr'.1
      rw [← this.2]; exact List.set_getElem_self this.1
    ihave Hins := Hclose' $$ %ptr' %_ [Hptrs'] Hx'
    · rw [hset']; iexact Hptrs'
    rw [upd_self _ _ _ rfl]
    wp_apply wp_recordInstanceMetadata $$ [$Hrr $HDur]
    wp_apply wp_recordCommands $$ [$Hrr $HDur]
    wp_apply wp_sync $$ [$Hrr $HDur]
    -- the state, closed, and `bcastPreAccept`
    have hib2 : instBounds (upd σ.inst ⟨toN replica, toN n⟩ (some (spInst σ cmds ⟨toN replica, toN n⟩ ballot props))) :=
      instBounds_upd _ _ _ Hib hq' hn.2
    have hc := uc_congr (σ.setInst ⟨toN replica, toN n⟩ (spInst σ cmds ⟨toN replica, toN n⟩ ballot props)) σ cmds (toN replica) n
      (spAttrs σ cmds).1 rfl rfl
    ihave Hrep : ownRep γ i r (spSt σ cmds ⟨toN replica, toN n⟩ n ballot props) $$
        [Hins Hcrt Hcut Heut Hconf Hmsk HmaxSeq Hlead Hmrb Hstore Hpeer HlS HlP]
    · iapply ownRep_of
      rw [hms]
      rw [spSt_eq]
      unfold ownRepRest
      iframe
      ipureintro; exact ⟨hib2, Hcb⟩
    have hwf' : RepWf i (spSt σ cmds ⟨toN replica, toN n⟩ n ballot props) ord :=
      ⟨by rw [spSt_eq]; exact hwf.id, hwf.hi, by rw [spSt_eq]; exact hwf.po⟩
    have hw' : (spSt σ cmds ⟨toN replica, toN n⟩ n ballot props).inst ⟨toN replica, toN n⟩ = some (spInst σ cmds ⟨toN replica, toN n⟩ ballot props) := by
      rw [spSt_eq]; simp [upd]
    have hdo : lbDepsOwned (spLb σ cmds ballot props) = false := by simp [lbDepsOwned, spLb]
    rw [startPhase1_snd] at hout
    have hm : (Msg.preAccept (preAcceptOf (spSt σ cmds ⟨toN replica, toN n⟩ n ballot props) replica n
        (spLb σ cmds ballot props))).wf :=
      hout _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hns : NoSends [Out.ev (.phase1 ⟨toN replica, toN n⟩ ballot (lbVal (spLb σ cmds ballot props))),
        Out.ev (.vote ⟨toN replica, toN n⟩ ballot stPREACCEPTED ⟨cmds, (spAttrs σ cmds).1, (spAttrs σ cmds).2.1⟩),
        Out.ev (.attrsRec ⟨toN replica, toN n⟩ cmds (spAttrs σ cmds).2.1)] := by
      intro o ho
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ho
      rcases ho with rfl | rfl | rfl <;>
        exact ⟨fun _ _ h => Out.noConfusion h, fun _ h => Out.noConfusion h⟩
    rw [startPhase1_snd, startPhase1_fst]
    icases outsOk_bcast γ i _ _ hns $$ Houts with ⟨Hob, Hp, Hcur⟩
    wp_apply (wp_bcastPreAccept hS γ i r rr L p Rext ord (spSt σ cmds ⟨toN replica, toN n⟩ n ballot props) replica n
      (spInst σ cmds ⟨toN replica, toN n⟩ ballot props) (spLb σ cmds ballot props) hwf' hq hn hw' rfl hdo hm hord)
      $$ [Hrep Hf Hp Hob] as ⟨%σ', Hrep, Hf, Hp, Hob⟩
    · iframe Hrep Hf Hp Hob
      unfold hdCtx; iexact Hctx0
    iapply HΦ
    unfold repDone repIdle
    iexists σ'
    unfold outboxesNil
    iframe
    done

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
