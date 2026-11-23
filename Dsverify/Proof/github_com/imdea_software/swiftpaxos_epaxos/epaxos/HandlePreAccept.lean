/-
`(*Replica).handlePreAccept` against the model's `hPreAccept`, and
`startRecoveryForInstance` against `hRecover` (statements; proofs in progress).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.StartPhase1
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Ballot
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Log
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.RecHelpers
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.RecModel
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.RecInst
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.PAProof

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

/-- What `handlePreAccept` needs (from the invariant: `Inv.msgWf` for the ids, deps and
non-empty commands; `Inv.ballotOwner` for `LeaderId` = the sender ≠ `i`; `Inv.wf` for
`ConfWf`). -/
structure PAWf (i : Nat) (σ : RState) (ord : List w32) (m : PreAccept) : Prop where
  hrep : RepWf i σ ord
  hq : 0 ≤ zz m.replica ∧ zz m.replica < nR
  hn : 0 ≤ zz m.inst ∧ toN m.inst + 1 < MAX_INSTANCE
  hlead : toN m.leaderId < nR ∧ toN m.leaderId ≠ i ∧ 0 ≤ zz m.leaderId
  hdeps : depsOk m.deps
  hcmd : m.command ≠ []
  hconf : ConfWf σ
  hord : ∀ o ∈ ord, 0 ≤ sint.Z o
  houts : OutsWf (hPreAccept σ m).2

/-- **`handlePreAccept(preAccept)`**. -/
theorem wp_handlePreAccept (hS : replica.Replica.SendMsg.spec (GF := GF)) (hP : dlog.Logger.Printf.spec (GF := GF))
    (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (ord : List w32) (σ : RState) (l : Loc) (m : PreAccept) (hw : PAWf i σ ord m) :
    {{ hdCtx (GF := GF) γ i r rr L p Rext ord ∗ ownRep γ i r σ ∗ ownPreAccept l m (DFrac.own 1) ∗
        repFrag γ i (hPreAccept σ m).1 ∗ outsOk γ i (hPreAccept σ m).2 }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"handlePreAccept"))
        (Val #l))
    {{ RET #(); repDone γ i r }} := by
  exact wp_handlePreAccept_core hS γ i r rr L p Rext ord σ l m hw.hrep hw.hq hw.hn hw.hlead
    hw.hdeps hw.hcmd hw.hconf hw.houts

theorem toN_W32 (k : Nat) (h : k < MAX_INSTANCE) : toN (W32 (k : Int)) = k := by
  unfold toN
  unfold MAX_INSTANCE at h
  have : sint.Z (W32 (k : Int)) = (k : Int) := by word
  rw [this]; simp

/-- What `startRecoveryForInstance` needs (`Step.recover`: the ids in range; `Inv.wf`). -/
structure RecWf (i : Nat) (σ : RState) (ord : List w32) (x : InstId) : Prop where
  hrep : RepWf i σ ord
  hq : x.q < nR
  hn : x.i + 1 < MAX_INSTANCE
  hord : ∀ o ∈ ord, 0 ≤ sint.Z o
  houts : OutsWf (hRecover σ x).2

set_option maxHeartbeats 8000000 in
/-- **`startRecoveryForInstance(q, k)`** (fixes R-BAL, R-VBAL, B10's guard R-OVF). -/
theorem wp_startRecoveryForInstance
    (hS : replica.Replica.SendMsg.spec (GF := GF))
    (hP : dlog.Logger.Printf.spec (GF := GF)) (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString)
    (p : FwPtrs) (Rext : IProp GF) (ord : List w32) (σ : RState) (x : InstId)
    (hw : RecWf i σ ord x) :
    {{ hdCtx (GF := GF) γ i r rr L p Rext ord ∗ ownRep γ i r σ ∗
        repFrag γ i (hRecover σ x).1 ∗ outsOk γ i (hRecover σ x).2 }}
      (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty
        @!! go!"startRecoveryForInstance")) (Val #(W32 x.q))) (Val #(W32 x.i)))
    {{ RET #(); repDone γ i r }} := by
  wp_start as ⟨#Hctx, Hrep, Hf, Houts⟩
  ihave #Hctx0 := Hctx
  unfold hdCtx
  icases Hctx with ⟨#Hpe, #Hpr, #Hrr, #Hfw, #Hro, #Hinv, #Hpo⟩
  ihave #Hfro := isReplicaFw_ro _ _ _ _ _ _ $$ Hfw
  ihave ⟨#HN, #HF, #HId, #HSt, #HRPC, #HPC, #HThr, #HEx, #HDr, #HSh, #HStats, #HStm, #HAl, %HLn⟩ :=
    fwRO_fields _ _ _ _ _ $$ Hfro
  ihave #HDur := isReplicaFw_durable _ _ _ _ _ _ $$ Hfw
  have hL5 : L.length = nR := HLn.1
  ihave #HN5 : fld rr go!"N" ↦□ W64 5 $$ []
  · rw [show (W64 5 : w64) = W64 ((L.length : Nat) : Int) by rw [hL5]; rfl]; iexact HN
  have hi : i < nR := hw.hrep.hi
  have hq5 : x.q < 5 := hw.hq
  have hn' : x.i < MAX_INSTANCE := by have := hw.hn; omega
  rw [ownRep_unseal]; unfold ownRepDef
  icases Hrep with ⟨%Hib, %Hcb, Hinsts, Hcrt, Hcut, Heut, Hconf, Hmsk, HlS, HlP, HmaxSeq, Hlead, Hmrb,
    Hstore, Hpeer⟩
  icases repInsts_acc γ i r σ.inst x hw.hq hn' $$ Hinsts with
    ⟨%iss, %rows, %row, %ptrs, %ptr, #Hiss, #Hrows, %Hrow, Hptrs, %Hptr, Hx, Hclose⟩
  ihave %Hrlen := ownSlice_len _ _ _ $$ Hrows
  ihave %Hplen := ownSlice_len _ _ _ $$ Hptrs
  have e1 : sint.Z (W64 (sint.Z (W32 (x.q : Int)))) = (x.q : Int) := by
    have : x.q < 5 := hq5; word
  have e2 : sint.Z (W64 (sint.Z (W32 (x.i : Int)))) = (x.i : Int) := by
    have : x.i < MAX_INSTANCE := hn'; unfold MAX_INSTANCE at this; word
  have h1 : 0 ≤ sint.Z (W64 (sint.Z (W32 (x.q : Int)))) ∧
      sint.Z (W64 (sint.Z (W32 (x.q : Int)))) < sint.Z iss.len := by
    have hl := (List.getElem?_eq_some_iff.mp Hrow).1
    have := Hrlen.1; have := Hrlen.2
    rw [e1]; constructor <;> word
  have h2 : 0 ≤ sint.Z (W64 (sint.Z (W32 (x.i : Int)))) ∧
      sint.Z (W64 (sint.Z (W32 (x.i : Int)))) < sint.Z row.len := by
    have := Hptr.2; have := Hplen.1; have := Hplen.2
    rw [e2]; unfold MAX_INSTANCE at *; constructor <;> word
  wp_auto
  simp only [h1, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
  · ipureintro; rw [e1]; exact Hrow
  simp only [h2, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index row _ ptrs _ ptr h2.1 $$ [$Hptrs] as Hptrs
  · ipureintro; rw [e2]; exact Hptr.1
  irename : (instance_ptr ↦ W32 (x.i : Int) : IProp GF) => Hinstance
  ipersist r
  ipersist replica
  ipersist Hinstance
  by_cases hdone : stGe (recW0 σ x).status stCOMMITTED = true ∧ (recW0 σ x).cmds ≠ none
  · -- committed with commands: nothing to recover
    rcases hx : σ.inst x with _ | w
    · exfalso
      simp only [recW0, getOrDefault, hx, newInstanceDefault] at hdone
      revert hdone; decide
    have hw0 : recW0 σ x = w := by simp [recW0, getOrDefault, hx]
    have hres : hRecover σ x = (σ, []) := by
      rw [hRec_done σ x hdone]; simp [getOrDefault, hx]
    rw [hw0] at hdone
    unfold instAt ownInst
    icases Hx with ⟨%y, Hy, %Hyf, #Hyid, Hycmds, Hydeps, Hylb⟩
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hy
    rw [show decide (ptr = null) = false from decide_eq_false Hnn]
    obtain ⟨cs0, hcs0⟩ : ∃ cs0, w.cmds = some cs0 := Option.ne_none_iff_exists'.mp hdone.2
    rw [hcs0]
    unfold cmdsRep
    icases Hycmds with ⟨%Hcnn, #Hycmds⟩
    wp_auto
    have hst : sint.Z (W8 4) ≤ sint.Z y.Status' := by
      rw [Hyf.2.2.1]; exact (stGe_iff _ _).mp hdone.1
    rw [show decide (sint.Z (W8 4) ≤ sint.Z y.Status') = true from decide_eq_true hst]
    wp_auto
    rw [show decide (y.Cmds' = slice.nil) = false from decide_eq_false Hcnn]
    simp only [Bool.not_false]
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %_ ⟨-, -⟩
    wp_auto
    wp_apply (wp_ep_Printf hP γ r rr i L p) $$ [$Hrr $Hfro]
    rw [hres]
    ihave Hidle := outsOk_idle (GF := GF) γ i [] (fun o ho => by simp at ho) $$ Houts
    ihave Hins := Hclose $$ %ptr %(some w) [Hptrs] [Hy Hydeps Hylb]
    · rw [show ptrs.set x.i ptr = ptrs by
        have := List.getElem?_eq_some_iff.mp Hptr.1
        rw [← this.2]; exact List.set_getElem_self this.1]
      iexact Hptrs
    · dsimp only
      iexists y; iframe Hy Hydeps Hylb
      isplitr
      · ipureintro; exact Hyf
      iframe Hyid
      rw [hcs0]
      isplitl []
      · ipureintro; exact Hcnn
      · iexact Hycmds
    rw [upd_self _ _ _ hx]
    iapply HΦ
    unfold repDone
    iexists σ
    iframe Hf Hidle
    rw [ownRep_unseal]; unfold ownRepDef
    iframe
    ipureintro; exact ⟨Hib, Hcb⟩
  -- the instance, created if nil
  have hxq : W32 ((x.q : Nat) : Int) = W32 (x.q : Int) := rfl
  have hplen' : (sint.Z row.len) = ((ptrs.length : Nat) : Int) := by
    have := Hplen.1; have := Hplen.2; word
  wp_join iprop(∃ p', inst_ptr ↦ p' ∗ row ↦* ptrs.set x.i p' ∗ ownInst γ i x p' (recW0 σ x))
    with [inst Hptrs Hx]
  · -- nil: `newInstanceDefault`
    rcases hx : σ.inst x with _ | w0
    case some =>
      unfold instAt ownInst
      icases Hx with ⟨%y, Hy, -⟩
      ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hy
      exact (Hnn rfl).elim
    wp_apply wp_newInstanceDefault as %p' ⟨%Hp'nn, %t, %idp, Hp', Hid⟩
    ipersist Hid
    simp only [h1, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
    · ipureintro; rw [e1]; exact Hrow
    simp only [h2, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [$Hptrs] as Hptrs
    · ipureintro; rw [← hplen']; exact h2
    rw [e2]
    wp_join_done
    iexists p'
    simp only [Int.toNat_natCast]
    iframe inst Hptrs
    have hd : recW0 σ x = newInstanceDefault x := by simp [recW0, getOrDefault, hx]
    rw [hd]
    iapply ownInst_default
    iframe Hp'
    iexact Hid
  · -- not nil: not committed with commands
    rcases hx : σ.inst x with _ | w0
    · unfold instAt; icases Hx with %Hnull
      exact (Hif Hnull).elim
    have hw0 : recW0 σ x = w0 := by simp [recW0, getOrDefault, hx]
    rw [hw0] at hdone
    unfold instAt ownInst
    icases Hx with ⟨%y, Hy, %Hyf, #Hyid, Hycmds, Hydeps, Hylb⟩
    have hw0' : recW0 σ x = w0 := hw0
    wp_auto
    by_cases hst : sint.Z (W8 4) ≤ sint.Z y.Status'
    · rw [show decide (sint.Z (W8 4) ≤ sint.Z y.Status') = true from decide_eq_true hst]
      have hnc : w0.cmds = none := by
        cases hc : w0.cmds with
        | none => rfl
        | some c =>
          exact (hdone ⟨(stGe_iff _ _).mpr (by rw [← Hyf.2.2.1]; exact hst),
            by rw [hc]; simp⟩).elim
      rw [hnc]
      unfold cmdsRep
      icases Hycmds with %Hcn
      wp_auto
      rw [show decide (y.Cmds' = slice.nil) = true from decide_eq_true Hcn]
      simp only [Bool.not_true]
      wp_auto
      wp_join_done
      iexists ptr
      rw [show ptrs.set x.i ptr = ptrs by
        have := List.getElem?_eq_some_iff.mp Hptr.1
        rw [← this.2]; exact List.set_getElem_self this.1]
      iframe inst Hptrs
      rw [hw0']
      iexists y; iframe Hy Hydeps Hylb
      isplitr
      · ipureintro; exact Hyf
      iframe Hyid
      rw [hnc]; ipureintro; exact Hcn
    · rw [show decide (sint.Z (W8 4) ≤ sint.Z y.Status') = false from decide_eq_false hst]
      wp_auto
      wp_join_done
      iexists ptr
      rw [show ptrs.set x.i ptr = ptrs by
        have := List.getElem?_eq_some_iff.mp Hptr.1
        rw [← this.2]; exact List.set_getElem_self this.1]
      iframe inst Hptrs
      rw [hw0']
      iexists y; iframe Hy Hycmds Hydeps Hylb
      isplitr
      · ipureintro; exact Hyf
      iexact Hyid
  iintro ⟨%p', inst, Hptrs, Hx⟩
  unfold ownInst
  icases Hx with ⟨%y, Hy, %Hyf, #Hyid, Hycmds, Hydeps, Hylb⟩
  have hib' : instBounds (upd σ.inst x (some (recW0 σ x))) :=
    instBounds_upd _ _ _ Hib hw.hq hw.hn
  wp_auto
  -- the nextBallot guard
  wp_apply (wp_nextBallot γ i r rr L p σ hw.hrep.id p' y (DFrac.own 1) (W32 0))
    $$ [$Hrr $Hfro $Hy $Hlead $Hmrb] as ⟨Hy, Hlead, Hmrb⟩
  rcases hnb : nextBallot σ y.bal' (W32 0) with _ | b
  · -- no ballot left
    simp only [Option.isSome_none, Option.getD_none]
    wp_auto
    have ho : (2 ^ 31 - 1 : Int) < makeBallotZ (getOrDefault σ x).1 (getOrDefault σ x).2.bal
        (W32 0) := by
      rw [makeBallotZ_god]
      unfold nextBallot at hnb
      rw [Hyf.1] at hnb
      split at hnb
      · assumption
      · cases hnb
    rw [hRec_ovf σ x hdone ho, getOrDefault_fst]
    ihave Hidle := outsOk_idle (GF := GF) γ i [] (fun o ho => by simp at ho) $$ Houts
    ihave Hins := Hclose $$ %p' %(some (recW0 σ x)) [Hptrs] [Hy Hycmds Hydeps Hylb]
    · iexact Hptrs
    · unfold instAt ownInst
      iexists y; iframe Hy Hycmds Hydeps Hylb
      isplitr
      · ipureintro; exact Hyf
      iexact Hyid
    iapply HΦ
    unfold repDone
    iexists { σ with inst := upd σ.inst x (some (getOrDefault σ x).2) }
    iframe Hf Hidle
    rw [ownRep_unseal]; unfold ownRepDef
    iframe
    ipureintro; exact ⟨hib', Hcb⟩
  have hb : b = recN σ x := by
    unfold nextBallot at hnb
    rw [Hyf.1] at hnb
    split at hnb
    · cases hnb
    · exact (Option.some.inj hnb).symm
  have hnovf : ¬ (2 ^ 31 - 1 : Int) < makeBallotZ σ (recW0 σ x).bal (W32 0) := by
    unfold nextBallot at hnb
    rw [Hyf.1] at hnb
    split at hnb
    · cases hnb
    · assumption
  subst hb
  simp only [Option.isSome_some, Bool.not_true, Option.getD_some]
  wp_auto
  -- the proposals carried over
  wp_join iprop(∃ pv, proposals_ptr ↦ pv ∗ recCp γ i σ x pv ∗ p' ↦ y ∗ inst_ptr ↦ p')
    with [proposals Hylb Hy inst] as ⟨%pv, proposals, Hcp, Hy, inst⟩
  · -- `inst.lb == nil`
    rcases hlb : (recW0 σ x).lb with _ | lb0
    · iexists slice.nil
      iframe proposals Hy inst
      unfold recCp
      rw [hlb]
      simp only [Option.bind_none]
      ipureintro; trivial
    · icases Hylb with ⟨%Hlbnn, -⟩
      exact (Hlbnn Hif).elim
  · -- `inst.lb != nil`
    rcases hlb : (recW0 σ x).lb with _ | lb0
    · icases Hylb with %Hnull
      exact (Hif Hnull).elim
    icases Hylb with ⟨%Hlbnn, Hlb⟩
    unfold ownLb
    icases Hlb with ⟨%yl, %gs, %prs, Hyl, %Hylf, Hcp, -⟩
    wp_auto
    wp_join_done
    iexists yl.clientProposals'
    iframe proposals Hy inst
    unfold recCp
    rw [hlb]
    simp only [Option.bind_some]
    rcases hcpp : lb0.clientProposals with _ | ps
    · iexact Hcp
    · icases Hcp with ⟨%H1, #H2, H3⟩
      iexists gs
      iframe H3
      isplitr
      · ipureintro; exact H1
      iexact H2
  -- the new bookkeeping
  wp_apply (wp_newLeaderBookkeepingDefault r rr) $$ [$Hpe $Hrr $HN5] as
    %lbp ⟨%Hlbpnn, %od, %cd, %d0, %pq, Hlbp⟩
  -- `makeBallot`
  have htq : toN (W32 (x.q : Int)) = x.q := toN_W32 _ (by unfold MAX_INSTANCE; omega)
  have hti : toN (W32 (x.i : Int)) = x.i := toN_W32 _ hn'
  have hpt : (ptrs.set x.i p')[toN (W32 (x.i : Int))]? = some p' := by
    rw [hti]; simp [show x.i < ptrs.length by have := Hptr.2; omega]
  have hb1 : sint.Z (W32 (x.q : Int)) < sint.Z iss.len := by
    have := h1.2; rwa [show sint.Z (W64 (sint.Z (W32 (x.q : Int)))) = sint.Z (W32 (x.q : Int))
      by word] at this
  have hb2 : sint.Z (W32 (x.i : Int)) < sint.Z row.len := by
    have := h2.2; rwa [show sint.Z (W64 (sint.Z (W32 (x.i : Int)))) = sint.Z (W32 (x.i : Int))
      by word] at this
  have hq0 : 0 ≤ sint.Z (W32 (x.q : Int)) := by
    have := h1.1; rwa [show sint.Z (W64 (sint.Z (W32 (x.q : Int)))) = sint.Z (W32 (x.q : Int))
      by word] at this
  have hn0 : 0 ≤ sint.Z (W32 (x.i : Int)) := by
    have := h2.1; rwa [show sint.Z (W64 (sint.Z (W32 (x.i : Int)))) = sint.Z (W32 (x.i : Int))
      by word] at this
  wp_apply (wp_makeBallot_slot γ i r rr L p σ hw.hrep.id (W32 (x.q : Int)) (W32 (x.i : Int)) iss
    rows row (ptrs.set x.i p') p' hq0 hn0 (by rw [htq]; exact Hrow) hpt hb1 hb2 _ _)
    $$ [$Hpe $Hrr $Hfro $Hiss $Hrows $Hptrs $Hy $Hlbp $Hlead $Hmrb]
    as ⟨Hptrs, Hy, Hlbp, Hlead, Hmrb⟩
  simp only [hnb, Option.getD_some]
  ihave Hy : p' ↦ epaxos.Instance.mk y.Cmds' (recN σ x) y.vbal' y.Status' y.Seq' y.Deps' lbp
      y.Index' y.Lowlink' y.bfilter' y.proposeTime' y.id' $$ [Hy]
  · iexact Hy
  ihave Hlbp : lbp ↦ epaxos.LeaderBookkeeping.mk pv y.vbal' true (W64 0) (W64 0) (W64 0) od cd
      slice.nil true false pq (W64 0) false (recN σ x) y.Cmds' y.Status' y.Seq' y.Deps' false
      (W64 0) $$ [Hlbp]
  · iexact Hlbp
  -- `lb.prepareReplies = append(lb.prepareReplies, preply)`
  wp_apply wp_slice_literal (V := Loc) [«$r0_ptr»]
  isplitr
  · ipureintro; rfl
  iintro %sl2p Hsl2
  icases Hsl2 with ⟨Hsl2, -⟩
  ihave Hnil := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
  ihave Hcap := ownSliceCap_nil (V := Loc) (GF := GF)
  wp_apply (wp_slice_append (V := Loc) slice.nil [] _ [«$r0_ptr»] (DFrac.own 1))
    $$ [$Hnil $Hcap $Hsl2] as %prsl ⟨Hprsl, Hprcap, -⟩
  simp only [List.nil_append]
  icases Hydeps with ⟨%dq, Hydeps⟩
  imod ownSlice_persist $$ Hydeps with #Hydeps
  icases cmdsRep_dup2 _ _ $$ Hycmds with ⟨Hycmds, Hycmds2⟩
  icases cmdsRep_dup2 _ _ $$ Hycmds2 with ⟨Hycmds2, Hycmds3⟩
  ipersist «$r0»
  have hlr : decide (W32 (i : Int) = W32 (x.q : Int)) = decide (σ.id = x.q) := by
    rw [hw.hrep.id]
    apply decide_eq_decide.mpr
    constructor
    · intro h
      have := congrArg toN h
      rwa [toN_W32 _ (by unfold MAX_INSTANCE nR at *; omega), htq] at this
    · intro h; rw [h]
  ihave Hlbp : lbp ↦ epaxos.LeaderBookkeeping.mk pv y.vbal' true (W64 0) (W64 0) (W64 0) od cd
      prsl true false pq (W64 0) false (recN σ x) y.Cmds' y.Status' y.Seq' y.Deps'
      (decide (W32 (i : Int) = W32 (x.q : Int))) (W64 0) $$ [Hlbp]
  · iexact Hlbp
  ihave Hx := ownInst_rec (GF := GF) γ i σ x hw.hrep.id p' lbp «$r0_ptr» y pv od cd prsl pq _ hlr Hlbpnn Hyf
    $$ [Hy Hycmds Hycmds2 Hycmds3 Hlbp Hprsl Hprcap Hcp]
  · iframe Hy Hycmds Hycmds2 Hycmds3 Hlbp Hprsl Hprcap Hcp
    isplitl []
    · iexact Hyid
    isplitl []
    · iexact Hydeps
    iexact «$r0»
  ihave Hins := Hclose $$ %p' %(some (recInst σ x)) Hptrs [Hx]
  · dsimp only [instAt]; iexact Hx
  -- the state, and `bcastPrepare`
  rw [hRec_main σ x hdone hnovf]
  have hns : NoSends [Out.ev (.makeBallot x (recN σ x)), Out.ev (.selfReply (recReply σ x))] := by
    intro o ho
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ho
    rcases ho with rfl | rfl <;>
      exact ⟨fun _ _ h => Out.noConfusion h, fun _ h => Out.noConfusion h⟩
  icases outsOk_bcast γ i _ _ hns $$ Houts with ⟨Hob, Hp, Hcur⟩
  have hX : (⟨toN (W32 (x.q : Int)), toN (W32 (x.i : Int))⟩ : InstId) = x := by rw [htq, hti]
  have hwf' : RepWf i (recSt σ x) ord := ⟨hw.hrep.id, hi, hw.hrep.po⟩
  have hw' : (recSt σ x).inst ⟨toN (W32 (x.q : Int)), toN (W32 (x.i : Int))⟩ =
      some (recInst σ x) := by
    rw [hX]; simp [recSt, RState.setInst, upd]
  have hqz : 0 ≤ zz (W32 (x.q : Int)) ∧ zz (W32 (x.q : Int)) < nR := by
    unfold zz nR at *; constructor <;> word
  have hnz : 0 ≤ zz (W32 (x.i : Int)) ∧ toN (W32 (x.i : Int)) + 1 < MAX_INSTANCE := by
    rw [hti]; refine ⟨?_, hw.hn⟩
    unfold zz; have := hn'; unfold MAX_INSTANCE at this; word
  have spec := wp_bcastPrepare hS γ i r rr L p Rext ord (recSt σ x) (W32 (x.q : Int))
    (W32 (x.i : Int)) (recInst σ x) (recLb σ x) hwf' hqz hnz hw' rfl
  rw [hX, show (recLb σ x).lastTriedBallot = recN σ x from rfl] at spec
  ihave Hrep : ownRep γ i r (recSt σ x) $$ [Hins Hcrt Hcut Heut Hconf Hmsk HlS HlP HmaxSeq Hlead Hmrb
      Hstore Hpeer]
  · rw [ownRep_unseal]; unfold ownRepDef
    simp only [recSt, RState.setInst]
    iframe
    ipureintro; exact ⟨instBounds_upd _ _ _ Hib hw.hq hw.hn, Hcb⟩
  wp_apply spec $$ [Hrep Hf Hp Hob] as ⟨Hrep, Hf, Hp, Hob⟩
  · iframe
    unfold hdCtx; iexact Hctx0
  iapply HΦ
  unfold repDone repIdle
  iexists recSt σ x
  unfold outboxesNil
  iframe
  done

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
