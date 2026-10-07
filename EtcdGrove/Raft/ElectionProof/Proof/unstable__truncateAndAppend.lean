/- Port of election_proof/proof_unstable__truncateAndAppend.v.

Lean notes: Rocq's `wp_slice_append_persistent` (`new/golang/theory/slice.v`) has no
Lean counterpart in Perennial's `Golang/Theory/Slice.lean`; it is proved here as a
private lemma (a copy of the one in `Proof/readOnly__addRequest.lean`, which a proof
file cannot import).
-/
import EtcdGrove.Raft.ElectionProof.Spec.unstable__truncateAndAppend
import EtcdGrove.Raft.ElectionProof.Spec.unstable__slice

noncomputable section

namespace Perennial

section append
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode BigSepL
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {s : Stuckness} {E : CoPset}
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

/-- Go's `append` onto a destination held read-only (Rocq `wp_slice_append_persistent`):
the result is read-only too, with the capacity owned. -/
private theorem wp_slice_append_persistent {st t : go.GoType} [st ↓u go.SliceType t]
    [IntoValTyped (GF := GF) V t]
    (sl : GoSlice) (vs : List V) (sl2 : GoSlice) (vs' : List V) (dq : DFrac) :
    {{ (sl ↦*□ vs ∗ ownSliceCap V sl (DFrac.own 1) ∗ sl2 ↦*{dq} vs' : IProp GF) }}
      (App (App (Val #(functions go.append [st])) (Val #sl)) (Val #sl2)) @ s; E
    {{ (s' : GoSlice), RET #s';
        s' ↦*□ (vs ++ vs') ∗ ownSliceCap V s' (DFrac.own 1) ∗ sl2 ↦*{dq} vs' }} := by
  wp_start as ⟨#Hs, Hcap, Hs2⟩
  iapply wp_fupd
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hlen2 := ownSlice_len _ _ _ $$ Hs2
  ihave %Hwf1 := ownSlice_wf _ _ _ $$ Hs
  ihave %Hwf2 := ownSlice_wf _ _ _ $$ Hs2
  wp_apply wp_sumAssumeNoOverflowSigned with %Hoverflow
  wp_if_destruct
  · rw [ite_eq_left ⟨by word, by word, Hif⟩]
    wp_auto
    rw [ite_eq_left (by (try simp only [slice.slice]); word)]
    wp_auto
    rw [slice_slice sl (W64 0) (sl.len + sl2.len) sl.len (sl.len + sl2.len) (by word)]
    have h0 : ∀ x : w64, W64 0 + x = x := fun x => by word
    simp only [h0]
    icases ownSliceCap_split (sl.len + sl2.len) sl $$ [Hcap] with ⟨%vs'', Hs_new, Hcap⟩
    · iframe Hcap; ipureintro; exact ⟨by word, Hif⟩
    ihave %Hlen3 := ownSlice_len _ _ _ $$ Hs_new
    wp_apply wp_slice_copy _ _ sl2 vs' dq $$ [Hs_new Hs2] with %n ⟨%Hn, Hs_new, Hs2⟩
    · iframe Hs_new Hs2
    have hd : vs''.length = vs'.length := by
      rw [Hlen3.1]; simp only [slice.slice]; word
    rw [hd, List.take_length, List.drop_of_length_le (l := vs'')
      (i := vs'.length) (by omega), List.append_nil]
    imod ownSlice_persist _ _ _ $$ Hs_new with #Hs_new
    iapply HΦ
    iframe Hs2
    isplitl []
    · ihave Hs0 := (ownSlice_trivial_slice sl _ vs).1 $$ Hs
      iapply ownSlice_combine sl.len sl _ vs vs' (W64 0) (sl.len + sl2.len)
        ⟨by word, by word, by word, by word⟩ $$ Hs0 Hs_new
    · iapply ownSliceCap_slice_change_first sl sl.len (W64 0) (sl.len + sl2.len) _
        ⟨Hif, by word, by word, by word, by word⟩ $$ Hcap
  · wp_apply wp_new_cap with %cap %Hcap_ge
    wp_apply wp_slice_make3 (V := V) (sl.len + sl2.len) cap ⟨by word, Hcap_ge⟩
      with %nsl ⟨Hnew, Hnew_cap, %Hcap⟩
    ihave %Hsl_wf := ownSlice_wf _ _ _ $$ Hnew
    ihave %Hsl_len := ownSlice_len _ _ _ $$ Hnew
    simp only [List.length_replicate] at Hsl_len
    wp_apply wp_slice_copy nsl _ sl vs DFrac.discard $$ [Hnew Hs] with %n' ⟨%Hn', Hnew, _⟩
    · iframe Hnew Hs
    rw [ite_eq_left ⟨by word, by word, by rw [Hcap]; exact Hcap_ge⟩]
    wp_auto
    icases (ownSlice_slice sl.len (sl.len + sl2.len) nsl _ _ ⟨by word, by word, by word⟩).1 $$ Hnew
      with ⟨Hnew1, Hnew2, _⟩
    wp_apply wp_slice_copy _ _ sl2 vs' dq $$ [Hnew2 Hs2] with %n'' ⟨%Hn'', Hnew2, Hs2⟩
    · iframe Hnew2 Hs2
    have hN : sint.nat (sl.len + sl2.len) = vs.length + vs'.length := by word
    have ha : (vs.take (List.replicate (sint.nat (sl.len + sl2.len)) (zero_val V)).length ++
        (List.replicate (sint.nat (sl.len + sl2.len)) (zero_val V)).drop vs.length).take
          (sint.nat sl.len) = vs := by
      rw [List.length_replicate, List.take_of_length_le (l := vs) (i := sint.nat (sl.len + sl2.len)) (by omega),
        show sint.nat sl.len = vs.length from Hlen.1.symm, List.take_left]
    have hb : (subslice (sint.nat sl.len) (sint.nat (sl.len + sl2.len))
        (vs.take (List.replicate (sint.nat (sl.len + sl2.len)) (zero_val V)).length ++
          (List.replicate (sint.nat (sl.len + sl2.len)) (zero_val V)).drop vs.length)).length =
        vs'.length := by
      simp only [subslice, List.length_drop, List.length_take, List.length_append,
        List.length_replicate]
      omega
    rw [ha, hb, List.take_length, List.drop_of_length_le (i := vs'.length) (by omega),
      List.append_nil]
    have hnl : nsl.len = sl.len + sl2.len := by word
    have hs : slice.slice nsl V (W64 0) (sl.len + sl2.len) = nsl := by
      rw [← hnl]; exact (slice_slice_trivial nsl).symm
    ihave H := ownSlice_combine sl.len nsl _ vs vs' (W64 0) (sl.len + sl2.len)
      ⟨by word, by word, by word, by word⟩ $$ Hnew1 Hnew2
    rw [hs]
    imod ownSlice_persist _ _ _ $$ H with #H
    iapply HΦ
    iframe Hs2 Hnew_cap H

end append

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
    exact ⟨by dsimp only; omega, rfl, rfl⟩
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
    refine ⟨⟨?_, rfl, Hulg⟩, trivial⟩
    dsimp only
    omega
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
    refine ⟨?_, rfl, Hulg⟩
    dsimp only
    omega
  done

end proof

end EtcdGrove
end Perennial
