/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `votesMinus`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.votesMinus
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.votesHas
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

theorem votesMinus.wp_proof (wp_votesHas : votesHas.spec (GF := GF) (hG := hG)) :
    votesMinus.spec (GF := GF) (hG := hG) := by
  intro sl xs tl ys
  wp_start as ⟨#Hs, #Ht⟩
  ihave #Hs0 := Hs
  iunfold votesRO at Hs0
  icases Hs0 with ⟨%gs, #Hgs, %Hrel⟩
  ihave %Hlen := ownSlice_len $$ Hgs
  have Hl := Hrel.length_eq
  iapply wp_fupd
  wp_auto
  ihave #Hnil := ownSlice_nil (V := G.VoteRec) (GF := GF) (DFrac.own 1)
  ihave Hcap0 := ownSliceCap_nil (V := G.VoteRec) (GF := GF)
  ihave IH : iprop(∃ (n : w64) (y : G.VoteRec) (osl : GoSlice) (L : List G.VoteRec),
      "i" ∷ i_ptr ↦ n ∗ "v" ∷ v_ptr ↦ y ∗ "out" ∷ out_ptr ↦ osl ∗ "Hout" ∷ osl ↦* L ∗
      "Hcap" ∷ ownSliceCap G.VoteRec osl (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        List.Forall₂ voteRel L ((xs.take (sint.nat n)).filter (fun x => !ys.contains x))⌝)
      $$ [i v out Hcap0]
  · iexists _, _, slice.nil, []
    iframe
    isplitr
    · iexact Hnil
    isplitr
    · iexact Hcap0
    ipureintro
    refine ⟨?_, ?_, ?_⟩
    · word
    · word
    · rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for IH
  obtain ⟨hn0, hn1, hnL⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < gs.length := by rw [Hlen.1]; word
    have Hlt' : sint.nat n < xs.length := Hl ▸ Hlt
    obtain ⟨y0, Hy⟩ : ∃ y, gs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨x', Hx'⟩ : ∃ x', xs[sint.nat n]? = some x' := ⟨_, List.getElem?_eq_getElem Hlt'⟩
    have Hyx := forall₂_getElem Hrel (sint.nat n) Hlt Hlt'
    rw [Option.some.inj ((List.getElem?_eq_getElem Hlt).symm.trans Hy),
      Option.some.inj ((List.getElem?_eq_getElem Hlt').symm.trans Hx')] at Hyx
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) gs DFrac.discard y0 hn0 $$ [Hgs] as -
    · isplitr
      · iexact Hgs
      ipureintro; exact Hy
    try wp_auto
    wp_apply wp_votesHas tl ys y0 x' $$ [Ht]
    · iframe Ht; ipureintro; exact Hyx
    have htake : xs.take (sint.nat (n + W64 1)) = xs.take (sint.nat n) ++ [x'] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hx']; simp
    cases hy : ys.contains x'
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
      refine ⟨?_, ?_, ?_⟩
      · word
      · word
      · rw [htake, List.filter_append]
        simp only [List.filter_cons, List.filter_nil, hy, Bool.not_false, ite_true]
        exact List.Forall₂.append hnL (List.Forall₂.cons Hyx List.Forall₂.nil)
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨?_, ?_, ?_⟩
      · word
      · word
      · rw [htake, List.filter_append]
        simp only [List.filter_cons, List.filter_nil, hy, Bool.not_true, Bool.false_eq_true, ite_false, List.append_nil]
        exact hnL
  · have hnx : sint.nat n = xs.length := by rw [← Hl, Hlen.1]; word
    rw [hnx, List.take_length] at hnL
    imod ownSlice_persist $$ Hout with #Hout
    imodintro
    iapply HΦ
    iunfold votesRO
    iexists L
    iframe Hout
    ipureintro; exact hnL

end proof

end AntCheck
end EtcdGrove
end Perennial
