/- Port of election_proof/proof_unstable__truncateAndAppend.v.

Lean notes: Rocq's `wp_slice_append_persistent` is Perennial's
`wp_slice_append_persistent` (`Golang/Theory/Slice.lean`).
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.unstable__truncateAndAppend
public import RaftWitness.Spec.go_etcd_io.raft.v3.unstable__slice
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex

@[expose] public section

noncomputable section

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

private theorem ite_true_of {P : Prop} [Decidable P] {α : Sort _} (h : P) (a b : α) :
    (if P then a else b) = a := by simp [h]

private theorem ite_false_of {P : Prop} [Decidable P] {α : Sort _} (h : ¬P) (a b : α) :
    (if P then a else b) = b := by simp [h]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The three arms of the `switch`, in order; see the spec. The `Infof` of arms 2 and 3
is `Logger.wp_logf` on `u.logger`, read through `u ↦ uv`. Arm 3's `keep` is capped
(`u.slice` returns `entries[a:b:b]`), so its `ownSliceCap` is free (`ownSliceCap_empty`)
and the `append` reallocates; arm 3's `min` needs the `go.min` unfolding. raft v3.7: the
slices are of entry pointers (`entsPts`), `fromIndex` is `ents[0].GetIndex()` on the loaded
pointer's `entRO`, and each new suffix's `entRO`s are the old ones' and the batch's (`entsBig_app`). -/
theorem unstable.truncateAndAppend.wp_proof
    (wp_unstable_slice : unstable.slice.spec (GF := GF) (hG := hG))
    (wp_Entry_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG)) :
    unstable.truncateAndAppend.spec (GF := GF) (hG := hG) := by
  intro u us ents e0 es dq Hfirst Hle Hnw
  wp_start as H
  iNamed H
  open_unstable
  ihave #Hulgv : isLoggerVal uv.logger' $$ [Hlogger]
  · iexact Hlogger
  iunfold isLoggerVal at Hulgv
  icases Hulgv with ⟨%ulg, %Hulg, #Hlg⟩
  wp_auto
  ihave %Hlen := entsPts_len $$ Hes
  ihave %Hulen := entsPts_len $$ Hents
  iunfold entsPts at Hes
  icases Hes with ⟨%lsb, Hesl, #Hbb⟩
  icases Hents with #Hents
  ihave Hents' := Hents
  iunfold entsRO at Hents'
  iunfold entsPts at Hents'
  icases Hents' with ⟨%lsu, #Hlsu, #Hbu⟩
  obtain ⟨Hlen1, Hlen2⟩ := Hlen
  obtain ⟨Hulen1, Hulen2⟩ := Hulen
  have Hlenz : (ents.length : Int) = sint.Z es.len := by rw [Hlen1]; word
  have Hulenz : (us.ents.length : Int) = sint.Z uv.entries'.len := by rw [Hulen1]; word
  -- `ents[0].GetIndex()`: the pointer loaded from the slice is a log entry
  have Hne : 0 < ents.length := (List.getElem?_eq_some_iff.1 Hfirst).1
  simp only [show (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z es.len) = True from
    eq_true ⟨by word, by word⟩, ↓reduceIte]
  icases entsBig_lookup lsb ents 0 e0 Hfirst $$ Hbb with ⟨%l0, %Hl0, #Hl0⟩
  wp_apply wp_load_slice_index es (sint.Z (W64 0)) lsb dq l0 (by word) $$ [Hesl] as Hesl
  · iframe Hesl; ipureintro; simpa using Hl0
  wp_apply wp_Entry_GetIndex.1 l0 DFrac.discard e0 $$ [$Hl0] as -
  by_cases Hcont : uint.Z e0.Index' = uint.Z us.offset + (us.ents.length : Int)
  · -- arm 1: the batch continues the suffix
    have Hguard : e0.Index' = us.offset + uv.entries'.len := by word
    have Had : ¬(uint.Z e0.Index' ≤ uint.Z us.offset ∧
        uint.Z e0.Index' ≠ uint.Z us.offset + (us.ents.length : Int)) := fun H => H.2 Hcont
    simp only [Had, ↓reduceIte, decide_eq_true Hguard]
    wp_auto
    wp_apply wp_slice_append_persistent (V := Loc) uv.entries' lsu es lsb dq
      $$ [$Hlsu $Hents_cap $Hesl] as %sl ⟨#Hsl, Hents_cap, Hesl⟩
    iapply HΦ
    rw [List.take_of_length_le (by omega)]
    isplitl [Hu Hents_cap]
    · iapply ownUnstable_intro $$ Hu Hents_cap
      · iunfold entsRO; iunfold entsPts
        iexists lsu ++ lsb
        iframe Hsl
        iapply entsBig_app $$ [Hbu Hbb]
        iframe Hbu Hbb
      · iexact Hsnap
      · iexact Hpksn
      · iexact Hlogger
      ipureintro
      constructor
      · unfold w64Min; rw [ite_eq_right (by omega)]
      · simp only [truncOffsetInProgress, ite_eq_left Hcont]
    iunfold entsPts; iexists lsb; iframe Hesl Hbb
  have Hguard : ¬e0.Index' = us.offset + uv.entries'.len := fun Heq => Hcont (by
    rw [Heq]; word)
  simp only [decide_eq_false Hguard]
  wp_auto
  by_cases Hrep : uint.Z e0.Index' ≤ uint.Z us.offset
  · -- arm 2: replace the suffix, adopting the caller's slice
    have Had : uint.Z e0.Index' ≤ uint.Z us.offset ∧
        uint.Z e0.Index' ≠ uint.Z us.offset + (us.ents.length : Int) := ⟨Hrep, Hcont⟩
    rw [ite_true_of Had, ite_true_of Had, decide_eq_true Hrep]
    icases Hadopt with ⟨%Hdq, Hcap⟩
    subst Hdq
    icases Hesl with #Hesl
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl_ptr ⟨-, -⟩
    wp_auto
    rw [Hulg]
    wp_auto
    wp_apply Logger.wp_logf ulg _ _ _ (by simp [logMethods]) $$ Hlg
    rw [← Hulg]
    iapply HΦ
    rw [show (uint.Z e0.Index' - uint.Z us.offset).toNat = 0 by omega, List.take_zero,
      List.nil_append]
    isplitl
    · iapply ownUnstable_intro $$ Hu Hcap
      · iunfold entsRO; iunfold entsPts; iexists lsb; iframe Hesl Hbb
      · iexact Hsnap
      · iexact Hpksn
      · iexact Hlogger
      ipureintro
      constructor
      · unfold w64Min
        split
        · rfl
        · apply BitVec.eq_of_toNat_eq; word
      · simp only [truncOffsetInProgress, ite_eq_right Hcont, ite_eq_left Hrep]
    itrivial
  -- arm 3: keep the suffix below `fromIndex`, then append
  have Had : ¬(uint.Z e0.Index' ≤ uint.Z us.offset ∧
      uint.Z e0.Index' ≠ uint.Z us.offset + (us.ents.length : Int)) := fun H => Hrep H.1
  rw [ite_false_of Had, ite_false_of Had, decide_eq_false Hrep]
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl_ptr ⟨-, -⟩
  wp_auto
  rw [Hulg]
  wp_auto
  wp_apply Logger.wp_logf ulg _ _ _ (by simp [logMethods]) $$ Hlg
  rw [← Hulg]
  have Hus : uint.Z us.offset ≤ uint.Z us.offset ∧ uint.Z us.offset < uint.Z e0.Index' ∧
      uint.Z e0.Index' ≤ uint.Z us.offset + (us.ents.length : Int) := ⟨Int.le_refl _, by omega, Hle⟩
  wp_apply wp_unstable_slice u us _ _ Hus Hnw
      $$ [Hu Hents Hents_cap] as %s0 %es0 ⟨Hun, #Hs0e, %Hlen0, %Hin0, %Hcap0, %Hes0⟩
  · close_unstable
  open_unstable_again
  rw [Int.sub_self, Int.toNat_zero, subslice, List.drop_zero] at Hes0
  subst Hes0
  ihave Hs0' := Hs0e
  iunfold entsRO at Hs0'
  iunfold entsPts at Hs0'
  icases Hs0' with ⟨%ls0, #Hs0, #Hb0⟩
  ihave %Hs0len := ownSlice_len $$ Hs0
  ihave Hs0cap := ownSliceCap_empty (V := Loc) s0 Hcap0.symm Hs0len.2
  wp_apply wp_slice_append_persistent (V := Loc) _ _ _ _ _
    $$ [$Hesl $Hs0 $Hs0cap] as %sl ⟨#Hsl, Hsl_cap, Hesl⟩
  -- `min(u.offsetInProgress, fromIndex)`
  wp_func_call
  wp_call
  wp_if_destruct <;>
  · iapply HΦ
    isplitl [Hu Hsl_cap]
    · iapply ownUnstable_intro $$ Hu Hsl_cap
      · iunfold entsRO; iunfold entsPts
        iexists ls0 ++ lsb
        iframe Hsl
        iapply entsBig_app $$ [Hb0 Hbb]
        iframe Hb0 Hbb
      · iexact Hsnap
      · iexact Hpksn
      · iexact Hlogger
      ipureintro
      constructor
      · unfold w64Min; rw [ite_eq_right (by omega)]
      · simp only [truncOffsetInProgress, ite_eq_right Hcont, ite_eq_right Hrep, w64Min]
        split <;> first | rfl | (apply BitVec.eq_of_toNat_eq; word) | omega
    iunfold entsPts; iexists lsb; iframe Hesl Hbb
  done

end proof

end EtcdGrove
end Perennial
