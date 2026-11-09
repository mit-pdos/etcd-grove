/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Set__Minus`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Minus
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Has

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem Set.Minus.wp_proof (wp_Has : Set.Has.spec (GF := GF) (hG := hG)) :
    Set.Minus.spec (GF := GF) (hG := hG) := by
  intro sl s tl t
  wp_start as ⟨#Hs, #Ht⟩
  ihave #Hs0 := Hs
  iunfold setRO at Hs0
  icases Hs0 with ⟨%xs, #Hxs, %Hmap⟩
  iapply wp_fupd
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hxs
  ihave #Hnil := ownSlice_nil (V := w64) (GF := GF) (DFrac.own 1)
  ihave Hcap0 := ownSliceCap_nil (V := w64) (GF := GF)
  ihave IH : iprop(∃ (n x : w64) (osl : GoSlice) (L : List w64),
      "i" ∷ i_ptr ↦ n ∗ "id" ∷ id_ptr ↦ x ∗ "out" ∷ out_ptr ↦ osl ∗ "Hout" ∷ osl ↦* L ∗
      "Hcap" ∷ ownSliceCap w64 osl (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        L.map (fun x => uint.nat x) = ((xs.take (sint.nat n)).map (fun x => uint.nat x)).filter
          (fun id => !t.contains id)⌝)
      $$ [i id out Hcap0]
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
    obtain ⟨y, Hy⟩ : ∃ y, xs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) xs DFrac.discard y hn0 $$ [Hxs] as -
    · isplitr
      · iexact Hxs
      ipureintro; exact Hy
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set.TypeAssumptions.ptr_Has_unfold.method_unfold]
    try wp_auto
    wp_apply wp_Has tl t y $$ [Ht]
    · iexact Ht
    have htake : (xs.take (sint.nat (n + W64 1))).map (fun x => uint.nat x) =
        (xs.take (sint.nat n)).map (fun x => uint.nat x) ++ [uint.nat y] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hy]; simp
    by_cases hy : uint.nat y ∈ t
    · simp only [hy, decide_true, Bool.not_true]
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [htake, List.filter_append, hnL]
      simp [hy]
    · simp only [hy, decide_false, Bool.not_false]
      try wp_auto
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
      rw [htake, List.filter_append, List.map_append, hnL]
      simp [hy]
  · have hnx : sint.nat n = xs.length := by rw [Hlen.1]; word
    rw [hnx, List.take_length, Hmap] at hnL
    imod ownSlice_persist $$ Hout with #Hout
    imodintro
    iapply HΦ
    iunfold setRO
    iexists L
    iframe Hout
    ipureintro; exact hnL

end proof

end Etcdraft
end EtcdGrove
end Perennial
