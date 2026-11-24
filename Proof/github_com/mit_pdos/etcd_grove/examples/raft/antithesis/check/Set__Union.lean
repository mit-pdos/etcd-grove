/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `Set.Union`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set__Union
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SetAdd

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

theorem Set_Union_setAdd_len (s : SSet) (x : Str) : (setAdd s x).length ≤ s.length + 1 := by
  unfold setAdd
  simp only
  split
  · omega
  · simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]; omega

theorem Set_Union_fold_len (l : List Str) : ∀ (s : SSet), (l.foldl setAdd s).length ≤ s.length + l.length := by
  induction l with
  | nil => intro s; simp
  | cons a t ih =>
    intro s
    simp only [List.foldl_cons, List.length_cons]
    have := ih (setAdd s a); have := Set_Union_setAdd_len s a; omega

theorem Set_Union_bound (xs ys : SSet) (n : Nat) (hn : n < ys.length) (h : (xs.length : Int) + ys.length < 2 ^ 62) :
    ((((ys.take n).foldl setAdd xs).length : Nat) : Int) + 1 < 2 ^ 63 := by
  have := Set_Union_fold_len (ys.take n) xs
  have : (ys.take n).length = n := by simp; omega
  omega

theorem Set.Union.wp_proof (wp_SetAdd : SetAdd.spec (GF := GF) (hG := hG)) :
    Set.Union.spec (GF := GF) (hG := hG) := by
  intro sl xs tl ys
  wp_start as ⟨#Hs, #Ht, %Hlen⟩
  ihave #Hys := Ht
  iunfold strsRO at Hys
  wp_auto
  ihave %Hl := ownSlice_len $$ Hys
  ihave IH : iprop(∃ (n : w64) (y : Str) (o : GoSlice),
      "i" ∷ i_ptr ↦ n ∗ "x" ∷ x_ptr ↦ y ∗ "out" ∷ out_ptr ↦ o ∗
      "#Ho" ∷ strsRO o ((ys.take (sint.nat n)).foldl setAdd xs) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z tl.len⌝) $$ [i x out]
  · iexists _, _, _
    iframe
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.foldl_nil]
    iframe Hs
    ipureintro
    refine ⟨by word, by word⟩
  wp_for IH
  obtain ⟨hn0, hn1⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < ys.length := by rw [Hl.1]; word
    obtain ⟨z, Hz⟩ : ∃ z, ys[sint.nat n]? = some z := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z tl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index tl (sint.Z n) ys DFrac.discard z hn0 $$ [Hys] as -
    · isplitr
      · iexact Hys
      ipureintro; exact Hz
    try wp_auto
    wp_apply wp_SetAdd o _ z $$ [Ho] as %u #Hu
    · iframe Ho; ipureintro; exact Set_Union_bound xs ys _ Hlt Hlen
    try wp_auto
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    have htake : (ys.take (sint.nat (n + W64 1))).foldl setAdd xs =
        setAdd ((ys.take (sint.nat n)).foldl setAdd xs) z := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hz]; simp
    rw [htake]
    iframe Hu
    ipureintro
    refine ⟨by word, by word⟩
  · have hnx : sint.nat n = ys.length := by rw [Hl.1]; word
    rw [hnx, List.take_length]
    try wp_auto
    iapply HΦ
    unfold SSet.union
    iexact Ho

end proof

end AntCheck
end EtcdGrove
end Perennial
