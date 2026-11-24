/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `Set.Minus`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set__Minus
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set__Has

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Set.Minus.wp_proof (wp_Has : Set.Has.spec (GF := GF) (hG := hG)) :
    Set.Minus.spec (GF := GF) (hG := hG) := by
  intro sl xs tl ys
  wp_start as ⟨#Hs, #Ht⟩
  ihave #Hxs := Hs
  iunfold strsRO at Hxs
  iapply wp_fupd
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hxs
  ihave #Hnil := ownSlice_nil (V := Str) (GF := GF) (DFrac.own 1)
  ihave Hcap0 := ownSliceCap_nil (V := Str) (GF := GF)
  ihave IH : iprop(∃ (n : w64) (y : Str) (osl : GoSlice) (L : List Str),
      "i" ∷ i_ptr ↦ n ∗ "x" ∷ x_ptr ↦ y ∗ "out" ∷ out_ptr ↦ osl ∗ "Hout" ∷ osl ↦* L ∗
      "Hcap" ∷ ownSliceCap Str osl (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        L = (xs.take (sint.nat n)).filter (fun z => !ys.has z)⌝)
      $$ [i x out Hcap0]
  · iexists _, _, slice.nil, []
    iframe
    isplitr
    · iexact Hnil
    isplitr
    · iexact Hcap0
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
  wp_for IH
  obtain ⟨hn0, hn1, hnL⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < xs.length := by rw [Hlen.1]; word
    obtain ⟨z, Hz⟩ : ∃ z, xs[sint.nat n]? = some z := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) xs DFrac.discard z hn0 $$ [Hxs] as -
    · isplitr
      · iexact Hxs
      ipureintro; exact Hz
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set.TypeAssumptions.ptr_Has_unfold.method_unfold]
    try wp_auto
    wp_apply wp_Has tl ys z $$ [Ht]
    · iexact Ht
    have htake : xs.take (sint.nat (n + W64 1)) = xs.take (sint.nat n) ++ [z] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hz]; simp
    cases hy : SSet.has ys z
    · try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [Hout Hcap Hsl1] as %s1 ⟨Hs1, Hcap1, -⟩
      · iframe
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [htake, List.filter_append, hnL]
      simp [hy]
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [htake, List.filter_append, hnL]
      simp [hy]
  · have hnx : sint.nat n = xs.length := by rw [Hlen.1]; word
    rw [hnx, List.take_length] at hnL
    imod ownSlice_persist $$ Hout with #Hout
    imodintro
    iapply HΦ
    iunfold strsRO
    rw [show xs.minus ys = L from hnL.symm]
    iexact Hout

end proof

end AntCheck
end EtcdGrove
end Perennial
