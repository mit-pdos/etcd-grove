/- Port of election_proof/proof_unstable__truncateAndAppend.v.

Lean notes: Rocq's `wp_slice_append_persistent` is Perennial's
`wp_slice_append_persistent` (`Golang/Theory/Slice.lean`).
-/
import EtcdGrove.Raft.ElectionProof.Spec.unstable__truncateAndAppend
import EtcdGrove.Raft.ElectionProof.Spec.unstable__slice

noncomputable section

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

private theorem ite_true_of {P : Prop} [Decidable P] {α : Sort _} (h : P) (a b : α) :
    (if P then a else b) = a := by simp [h]

private theorem ite_false_of {P : Prop} [Decidable P] {α : Sort _} (h : ¬P) (a b : α) :
    (if P then a else b) = b := by simp [h]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The three arms of the `switch`, in order; see the spec. The `Infof` of arms 2 and 3
is `Logger.wp_logf` on `u.logger`, read through `u ↦ uv`. Arm 3's `keep` is capped
(`u.slice` returns `entries[a:b:b]`), so its `ownSliceCap` is free (`ownSliceCap_empty`)
and the `append` reallocates; arm 3's `min` needs the `go.min` unfolding. -/
theorem unstable.truncateAndAppend.wp_proof
    (wp_unstable_slice : unstable.slice.spec (GF := GF) (hG := hG)) :
    unstable.truncateAndAppend.spec (GF := GF) (hG := hG) := by
  intro u uv uents ents e0 es dq ulg Hfirst Hle Hnw Hulg
  wp_start as H
  iNamed H
  unfold ownUnstable
  iNamed Hun
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hes
  ihave %Hulen := ownSlice_len $$ Hents
  obtain ⟨Hlen1, Hlen2⟩ := Hlen
  obtain ⟨Hulen1, Hulen2⟩ := Hulen
  have Hlenz : (ents.length : Int) = sint.Z es.len := by rw [Hlen1]; word
  have Hulenz : (uents.length : Int) = sint.Z uv.entries'.len := by rw [Hulen1]; word
  -- `ents[0].Index`: hand the element out of the slice for the field load
  have Hne : 0 < ents.length := (List.getElem?_eq_some_iff.1 Hfirst).1
  simp only [show (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z es.len) = True from
    eq_true ⟨by word, by word⟩, ↓reduceIte]
  icases ownSlice_elem_acc (sint.Z (W64 0)) e0 _ _ _ (by word) (by simpa using Hfirst) $$ Hes
    with ⟨He0, Hesback⟩
  -- (a field load through a fractional struct points-to is not found by `wp_auto`: take
  -- the field out by hand)
  icases (AccessStrict.access_strict
      (A := (sliceIndexRef raftpb.Entry (sint.Z (W64 0)) es).[raftpb.Entry, go!"Index"] ↦{dq}
        e0.Index')
      (A' := (sliceIndexRef raftpb.Entry (sint.Z (W64 0)) es).[raftpb.Entry, go!"Index"] ↦{dq}
        e0.Index')
      (P := sliceIndexRef raftpb.Entry (sint.Z (W64 0)) es ↦{dq} e0)) $$ He0 with ⟨He0, Hclose⟩
  wp_auto
  ihave He0 := Hclose $$ He0
  ihave Hes := Hesback $$ He0
  rw [list_insert_id (by simpa using Hfirst)]
  by_cases Hcont : uint.Z e0.Index' = uint.Z uv.offset' + (uents.length : Int)
  · -- arm 1: the batch continues the suffix
    have Hguard : e0.Index' = uv.offset' + uv.entries'.len := by word
    have Had : ¬(uint.Z e0.Index' ≤ uint.Z uv.offset' ∧
        uint.Z e0.Index' ≠ uint.Z uv.offset' + (uents.length : Int)) := fun H => H.2 Hcont
    simp only [Had, ↓reduceIte, decide_eq_true Hguard]
    wp_auto
    wp_apply wp_slice_append_persistent (V := raftpb.Entry) _ _ _ _ _
      $$ [$Hents $Hents_cap $Hes] as %sl ⟨Hents, Hents_cap, Hes⟩
    iapply HΦ
    rw [List.take_of_length_le (by omega)]
    iframe
    ipureintro
    exact ⟨by dsimp only; omega, rfl, rfl, by simp only [truncOffsetInProgress, if_pos Hcont]⟩
  have Hguard : ¬e0.Index' = uv.offset' + uv.entries'.len := fun Heq => Hcont (by
    rw [Heq]; word)
  simp only [decide_eq_false Hguard]
  wp_auto
  by_cases Hrep : uint.Z e0.Index' ≤ uint.Z uv.offset'
  · -- arm 2: replace the suffix, adopting the caller's slice
    have Had : uint.Z e0.Index' ≤ uint.Z uv.offset' ∧
        uint.Z e0.Index' ≠ uint.Z uv.offset' + (uents.length : Int) := ⟨Hrep, Hcont⟩
    rw [ite_true_of Had, ite_true_of Had, decide_eq_true Hrep]
    icases Hadopt with ⟨%Hdq, Hcap⟩
    subst Hdq
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl_ptr ⟨-, -⟩
    wp_auto
    rw [Hulg]
    wp_auto
    wp_apply Logger.wp_logf ulg _ _ _ (by simp [logMethods]) $$ Hlg
    iapply HΦ
    rw [show (uint.Z e0.Index' - uint.Z uv.offset').toNat = 0 by omega, List.take_zero,
      List.nil_append]
    iframe
    ipureintro
    refine ⟨⟨?_, rfl, Hulg, ?_⟩, trivial⟩
    · dsimp only
      omega
    · simp only [truncOffsetInProgress, if_neg Hcont, if_pos Hrep]
  -- arm 3: keep the suffix below `fromIndex`, then append
  have Had : ¬(uint.Z e0.Index' ≤ uint.Z uv.offset' ∧
      uint.Z e0.Index' ≠ uint.Z uv.offset' + (uents.length : Int)) := fun H => Hrep H.1
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
  have Hus : uint.Z uv.offset' ≤ uint.Z uv.offset' ∧ uint.Z uv.offset' < uint.Z e0.Index' ∧
      uint.Z e0.Index' ≤ uint.Z uv.offset' + (uents.length : Int) := ⟨Int.le_refl _, by omega, Hle⟩
  wp_apply wp_unstable_slice _ _ _ _ _ Hus Hnw $$ [Hu Hents Hents_cap]
    as %s0 %es0 ⟨Hun, #Hs0, %Hlen0, %Hin0, %Hcap0, %Hes0⟩
  · unfold ownUnstable; simp only [named]; iframe
  iNamed Hun
  rw [Int.sub_self, Int.toNat_zero, subslice, List.drop_zero] at Hes0
  subst Hes0
  ihave %Hs0len := ownSlice_len $$ Hs0
  ihave Hs0cap := ownSliceCap_empty (V := raftpb.Entry) s0 Hcap0.symm Hs0len.2
  wp_apply wp_slice_append_persistent (V := raftpb.Entry) _ _ _ _ _
    $$ [$Hes $Hs0 $Hs0cap] as %sl ⟨Hsl, Hsl_cap, Hes⟩
  -- `min(u.offsetInProgress, fromIndex)`
  wp_func_call
  wp_call
  wp_if_destruct <;>
  · iapply HΦ
    iframe
    ipureintro
    refine ⟨?_, rfl, Hulg, ?_⟩
    · dsimp only
      omega
    · simp only [truncOffsetInProgress, if_neg Hcont, if_neg Hrep, w64Min]
      split <;> first | rfl | (apply BitVec.eq_of_toNat_eq; word) | omega
  done

end proof

end EtcdGrove
end Perennial
