/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `votesUnion`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.votesUnion
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.votesAdd
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

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

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx in
theorem votesUnion_length (xs ys : List VoteRec) : (lset.union xs ys).length ≤ xs.length + ys.length := by
  induction ys generalizing xs with
  | nil => simp [lset.union]
  | cons y ys ih =>
    simp only [lset.union, List.foldl_cons] at ih ⊢
    have h := ih (lset.add xs y)
    have : (lset.add xs y).length ≤ xs.length + 1 := by
      unfold lset.add; split <;> simp
    simp only [List.length_cons]; omega

theorem votesUnion.wp_proof (wp_votesAdd : votesAdd.spec (GF := GF) (hG := hG)) :
    votesUnion.spec (GF := GF) (hG := hG) := by
  intro sl xs tl ys
  wp_start as ⟨#Hs, #Ht, %Hb⟩
  ihave #Ht0 := Ht
  iunfold votesRO at Ht0
  icases Ht0 with ⟨%gs, #Hgs, %Hrel⟩
  ihave %Hlen := ownSlice_len $$ Hgs
  have Hl := Hrel.length_eq
  wp_auto
  ihave IH : iprop(∃ (n : w64) (y : G.VoteRec) (o : GoSlice),
      "i" ∷ i_ptr ↦ n ∗ "v" ∷ v_ptr ↦ y ∗ "out" ∷ out_ptr ↦ o ∗
      "Ho" ∷ votesRO o (lset.union xs (ys.take (sint.nat n))) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z tl.len⌝) $$ [i v out]
  · iexists _, _, _
    iframe
    isplitr
    · rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; simp only [lset.union, List.foldl_nil]; iexact Hs
    ipureintro
    refine ⟨?_, ?_⟩ <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < gs.length := by rw [Hlen.1]; word
    have Hlt' : sint.nat n < ys.length := Hl ▸ Hlt
    obtain ⟨y0, Hy⟩ : ∃ y, gs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨x', Hx'⟩ : ∃ x', ys[sint.nat n]? = some x' := ⟨_, List.getElem?_eq_getElem Hlt'⟩
    have Hyx := forall₂_getElem Hrel (sint.nat n) Hlt Hlt'
    rw [Option.some.inj ((List.getElem?_eq_getElem Hlt).symm.trans Hy),
      Option.some.inj ((List.getElem?_eq_getElem Hlt').symm.trans Hx')] at Hyx
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z tl.len from ⟨Hn.1, Hif⟩))]
    wp_apply wp_load_slice_index tl (sint.Z n) gs DFrac.discard y0 Hn.1 $$ [Hgs] as -
    · isplitr
      · iexact Hgs
      ipureintro; exact Hy
    try wp_auto
    have Hul := votesUnion_length xs (ys.take (sint.nat n))
    have Htl : (ys.take (sint.nat n)).length ≤ ys.length := List.length_take_le' _ _
    wp_apply wp_votesAdd o _ y0 x' $$ [Ho] as %o1 #Ho1
    · iframe Ho; ipureintro; refine ⟨Hyx, ?_⟩; omega
    try wp_auto
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    isplitr
    · rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hx']
      simp only [Option.toList_some, lset.union, List.foldl_append, List.foldl_cons, List.foldl_nil]
      iexact Ho1
    ipureintro
    refine ⟨?_, ?_⟩ <;> word
  · try wp_auto
    have hnx : sint.nat n = ys.length := by rw [← Hl, Hlen.1]; word
    have h : lset.union xs ys = lset.union xs (ys.take (sint.nat n)) := by rw [hnx, List.take_length]
    iapply HΦ
    rw [h]
    iexact Ho

end proof

end AntCheck
end EtcdGrove
end Perennial
