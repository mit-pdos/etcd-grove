/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `SetOf`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SetOf
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

theorem SetOf_setAdd_len (s : SSet) (x : Str) : (setAdd s x).length ≤ s.length + 1 := by
  unfold setAdd
  simp only
  split
  · omega
  · simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]; omega

theorem SetOf_fold_len (l : List Str) : ∀ (s : SSet), (l.foldl setAdd s).length ≤ s.length + l.length := by
  induction l with
  | nil => intro s; simp
  | cons a t ih =>
    intro s
    simp only [List.foldl_cons, List.length_cons]
    have := ih (setAdd s a); have := SetOf_setAdd_len s a; omega

theorem SetOf_bound (xs : List Str) (n : Nat) (hn : n < xs.length) (h : (xs.length : Int) < 2 ^ 62) :
    ((((xs.take n).foldl setAdd []).length : Nat) : Int) + 1 < 2 ^ 63 := by
  have := SetOf_fold_len (xs.take n) []
  have : (xs.take n).length = n := by simp; omega
  simp at *
  omega

theorem SetOf.wp_proof (wp_SetAdd : SetAdd.spec (GF := GF) (hG := hG)) :
    SetOf.spec (GF := GF) (hG := hG) := by
  intro sl xs
  wp_start as ⟨#Hs, %Hlen⟩
  iunfold strsRO at Hs
  wp_auto
  ihave %Hl := ownSlice_len $$ Hs
  ihave #Hnil := ownSlice_nil (V := Str) (GF := GF) DFrac.discard
  ihave IH : iprop(∃ (n : w64) (y : Str) (o : GoSlice),
      "i" ∷ i_ptr ↦ n ∗ "x" ∷ x_ptr ↦ y ∗ "s" ∷ s_ptr ↦ o ∗
      "#Ho" ∷ strsRO o ((xs.take (sint.nat n)).foldl setAdd []) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝) $$ [i x s]
  · iexists _, _, _
    iframe
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.foldl_nil]
    iunfold strsRO
    iframe Hnil
    ipureintro
    refine ⟨by word, by word⟩
  wp_for IH
  obtain ⟨hn0, hn1⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < xs.length := by rw [Hl.1]; word
    obtain ⟨z, Hz⟩ : ∃ z, xs[sint.nat n]? = some z := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) xs DFrac.discard z hn0 $$ [Hs] as -
    · isplitr
      · iexact Hs
      ipureintro; exact Hz
    try wp_auto
    wp_apply wp_SetAdd o _ z $$ [Ho] as %u #Hu
    · iframe Ho; ipureintro; exact SetOf_bound xs _ Hlt Hlen
    try wp_auto
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    have htake : (xs.take (sint.nat (n + W64 1))).foldl setAdd [] =
        setAdd ((xs.take (sint.nat n)).foldl setAdd []) z := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hz]; simp
    rw [htake]
    iframe Hu
    ipureintro
    refine ⟨by word, by word⟩
  · have hnx : sint.nat n = xs.length := by rw [Hl.1]; word
    rw [hnx, List.take_length]
    try wp_auto
    iapply HΦ
    unfold setOf
    iexact Ho

end proof

end AntCheck
end EtcdGrove
end Perennial
