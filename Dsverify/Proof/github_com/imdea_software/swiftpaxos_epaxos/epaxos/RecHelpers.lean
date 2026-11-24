/-
Callee specs for `startRecoveryForInstance`: `newNilDeps`, `newLeaderBookkeepingDefault`, and
`makeBallot` on an opened slot (its instance and bookkeeping held, the rest of the state not
needed).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.StartPhase1
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Ballot

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
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : StateTreemap GF]

/-- `newNilDeps()`: a fresh slice (its contents not tracked). -/
theorem wp_newNilDeps (r rr : Loc) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ fld rr go!"N" ↦□ W64 5 }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"newNilDeps")) (Val #()))
    {{ (s : GoSlice), RET #s; True }} := by
  wp_start as ⟨#Hrr, #HN⟩
  wp_auto
  wp_apply (wp_slice_make2 (V := w32) (W64 5)) as %dsl ⟨Hdsl, -⟩
  · ipureintro; decide
  ihave %Hdl := ownSlice_len _ _ _ $$ Hdsl
  have hdl : sint.Z dsl.len = 5 := by
    have h1 := Hdl.1; have := Hdl.2; simp only [List.length_replicate] at h1; word
  ihave HI : (∃ (k : Nat) (vs : List w32), "Hq" ∷ i_ptr ↦ W64 (k : Int) ∗
      "Hd" ∷ dsl ↦* vs ∗ "%Hk" ∷ ⌜k ≤ 5 ∧ vs.length = 5⌝ : IProp GF) $$ [«i» Hdsl]
  · iexists 0, _
    iframe
    ipureintro; simp
  wp_for HI
  wp_if_destruct
  · have hk5 : k < 5 := by
      have := Hif; have : sint.Z (W64 (k : Int)) = (k : Int) := by word
      have := Hk.1; word
    have hkk : sint.Z (W64 (k : Int)) = (k : Int) := by word
    rw [if_pos (by rw [hkk, hdl]; omega), hkk]
    wp_apply wp_store_slice_index $$ [Hd] as Hd
    · iframe; ipureintro; simp; omega
    wp_for_post
    iframe
    iexists k + 1, _
    rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
    iframe
    ipureintro; simp; omega
  iapply HΦ
  iempintro

/-- `newLeaderBookkeepingDefault()`: `newLeaderBookkeeping(nil, newNilDeps(), newNilDeps(),
newNilDeps(), 0, nil, NONE, -1)`. -/
theorem wp_newLeaderBookkeepingDefault (r rr : Loc) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ fld rr go!"N" ↦□ W64 5 }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty
        @!! go!"newLeaderBookkeepingDefault")) (Val #()))
    {{ (l : Loc), RET #l; ⌜l ≠ null⌝ ∗ ∃ od cd d pq : GoSlice,
        l ↦ epaxos.LeaderBookkeeping.mk slice.nil (W32 (-1)) true (W64 0) (W64 0) (W64 0) od cd
          slice.nil true false pq (W64 0) false (W32 0) slice.nil (W8 0) (W32 (-1)) d false
          (W64 0) }} := by
  wp_start as ⟨#Hrr, #HN⟩
  wp_auto
  wp_apply (wp_newNilDeps r rr) $$ [$Hpkg $Hrr $HN] as %d1 -
  wp_apply (wp_newNilDeps r rr) $$ [$Hpkg $Hrr $HN] as %d2 -
  wp_apply (wp_newNilDeps r rr) $$ [$Hpkg $Hrr $HN] as %d3 -
  unfold epaxos.NONE
  wp_apply (wp_newLeaderBookkeeping r rr (W64 5) (by decide) slice.nil d1 d2 d3 (W32 0) slice.nil
    (W8 0) (W32 (-1))) $$ [$Hpkg $Hrr $HN] as %l ⟨%Hlnn, %pq, Hl⟩
  iapply HΦ
  isplitr
  · ipureintro; exact Hlnn
  iexists d1, d2, d3, pq
  iexact Hl

/-- `makeBallot(replica, instance)` on an opened slot: `lb.lastTriedBallot = nextBallot(inst,
lb.lastTriedBallot)` when it fits. -/
theorem wp_makeBallot_slot (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs)
    (σ : RState) (hid : σ.id = i) (replica n : w32) (iss : GoSlice) (rows : List GoSlice)
    (row : GoSlice) (ptrs : List Loc) (pt : Loc)
    (hq : 0 ≤ sint.Z replica) (hn : 0 ≤ sint.Z n)
    (hrow : rows[toN replica]? = some row) (hpt : ptrs[toN n]? = some pt)
    (hb1 : sint.Z replica < sint.Z iss.len) (hb2 : sint.Z n < sint.Z row.len)
    (y : epaxos.Instance) (yl : epaxos.LeaderBookkeeping) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ fwRO γ rr i L p ∗
        efld r go!"InstanceSpace" ↦□ iss ∗ iss ↦*□ rows ∗ row ↦* ptrs ∗ pt ↦ y ∗ y.lb' ↦ yl ∗
        efld r go!"IsLeader" ↦ σ.isLeader ∗ efld r go!"maxRecvBallot" ↦ σ.maxRecvBallot }}
      (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"makeBallot"))
        (Val #replica)) (Val #n))
    {{ RET #(); row ↦* ptrs ∗ pt ↦ y ∗
        y.lb' ↦ { yl with lastTriedBallot' :=
          (nextBallot σ y.bal' yl.lastTriedBallot').getD yl.lastTriedBallot' } ∗
        efld r go!"IsLeader" ↦ σ.isLeader ∗ efld r go!"maxRecvBallot" ↦ σ.maxRecvBallot }} := by
  wp_start as ⟨#Hrr, #Hro, #Hiss, #Hrows, Hptrs, Hy, Hyl, Hlead, Hmrb⟩
  wp_auto
  have e1 : sint.Z (W64 (sint.Z replica)) = sint.Z replica := by word
  have e2 : sint.Z (W64 (sint.Z n)) = sint.Z n := by word
  have h1 : 0 ≤ sint.Z (W64 (sint.Z replica)) ∧ sint.Z (W64 (sint.Z replica)) < sint.Z iss.len := by
    rw [e1]; exact ⟨hq, hb1⟩
  simp only [h1, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
  · ipureintro; rw [e1]; exact hrow
  have h2 : 0 ≤ sint.Z (W64 (sint.Z n)) ∧ sint.Z (W64 (sint.Z n)) < sint.Z row.len := by
    rw [e2]; exact ⟨hn, hb2⟩
  simp only [h2, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index row _ ptrs _ pt h2.1 $$ [$Hptrs] as Hptrs
  · ipureintro; rw [e2]; exact hpt
  wp_apply (wp_nextBallot γ i r rr L p σ hid pt y (DFrac.own 1) yl.lastTriedBallot')
    $$ [$Hrr $Hro $Hy $Hlead $Hmrb] as ⟨Hy, Hlead, Hmrb⟩
  rcases h : nextBallot σ y.bal' yl.lastTriedBallot' with _ | b
  · simp only [Option.isSome_none, Option.getD_none]
    wp_auto
    iapply HΦ
    iframe
  · simp only [Option.isSome_some, Option.getD_some]
    wp_auto
    iapply HΦ
    iframe

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
