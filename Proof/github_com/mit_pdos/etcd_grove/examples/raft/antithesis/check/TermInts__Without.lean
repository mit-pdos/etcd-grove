/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `TermInts.Without`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts__Without
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.intsHas
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

theorem TermInts.Without.wp_proof (wp_intsHas : intsHas.spec (GF := GF) (hG := hG)) :
    TermInts.Without.spec (GF := GF) (hG := hG) := by
  intro sl f tl ts
  wp_start as ⟨#Hs, #Ht⟩
  iunfold termIntsRO at Hs
  icases Hs with ⟨%gs, #Hgs, %Hrel⟩
  ihave %Hlen := ownSlice_len $$ Hgs
  have Hl := Hrel.length_eq
  iapply wp_fupd
  wp_auto
  ihave #Hnil := ownSlice_nil (V := G.TermInt) (GF := GF) (DFrac.own 1)
  ihave Hcap0 := ownSliceCap_nil (V := G.TermInt) (GF := GF)
  ihave IH : iprop(∃ (n : w64) (y : G.TermInt) (osl : GoSlice) (L : List G.TermInt),
      "i" ∷ i_ptr ↦ n ∗ "p" ∷ p_ptr ↦ y ∗ "out" ∷ out_ptr ↦ osl ∗ "Hout" ∷ osl ↦* L ∗
      "Hcap" ∷ ownSliceCap G.TermInt osl (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        List.Forall₂ (fun (g : G.TermInt) (p : Int × Int) => sint.Z g.T' = p.1 ∧ sint.Z g.V' = p.2) L
          ((f.take (sint.nat n)).filter (fun p => !ts.contains p.1))⌝)
      $$ [i p out Hcap0]
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
  · have Hlt : sint.nat n < f.length := by rw [← Hl, Hlen.1]; word
    obtain ⟨y0, Hy⟩ : ∃ y, gs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem (Hl ▸ Hlt)⟩
    obtain ⟨p0, Hp0⟩ : ∃ p, f[sint.nat n]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have HTV := forall₂_getElem Hrel (sint.nat n) (Hl ▸ Hlt) Hlt
    rw [Option.some.inj ((List.getElem?_eq_getElem (Hl ▸ Hlt)).symm.trans Hy),
      Option.some.inj ((List.getElem?_eq_getElem Hlt).symm.trans Hp0)] at HTV
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) gs DFrac.discard y0 hn0 $$ [Hgs] as -
    · isplitr
      · iexact Hgs
      ipureintro; exact Hy
    try wp_auto
    have htake : f.take (sint.nat (n + W64 1)) = f.take (sint.nat n) ++ [p0] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hp0]; simp
    have Hnext : 0 ≤ sint.Z (n + W64 1) ∧ sint.Z (n + W64 1) ≤ sint.Z sl.len := by
      constructor <;> word
    wp_apply wp_intsHas tl ts y0.T' $$ [Ht]
    · iexact Ht
    cases hy : ts.contains (sint.Z y0.T')
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
      refine ⟨Hnext.1, Hnext.2, ?_⟩
      rw [htake, List.filter_append]
      simp only [List.filter_cons, List.filter_nil, ← HTV.1, hy, Bool.not_false, ite_true]
      exact List.Forall₂.append hnL (List.Forall₂.cons HTV List.Forall₂.nil)
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨Hnext.1, Hnext.2, ?_⟩
      rw [htake, List.filter_append]
      simp only [List.filter_cons, List.filter_nil, ← HTV.1, hy, Bool.not_true, Bool.false_eq_true,
        ite_false, List.append_nil]
      exact hnL
  · have hnx : sint.nat n = f.length := by rw [← Hl, Hlen.1]; word
    rw [hnx, List.take_length] at hnL
    try wp_auto
    imod ownSlice_persist $$ Hout with #Hout
    imodintro
    iapply HΦ
    iunfold termIntsRO
    iexists L
    iframe Hout
    ipureintro; exact hnL

end proof

end AntCheck
end EtcdGrove
end Perennial
