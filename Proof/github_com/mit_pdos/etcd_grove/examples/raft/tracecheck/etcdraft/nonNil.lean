/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `nonNil`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.nonNil

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

theorem nonNil.wp_proof : nonNil.spec (GF := GF) (hG := hG) := by
  intro sl dq ps os P
  wp_start as ⟨Hsl, Hps, #HP⟩
  ihave %Hsll := ownSlice_len $$ Hsl
  ihave %Hpl := BigSepL2.bigSepL2_length $$ Hps
  iapply wp_fupd
  wp_auto
  ihave Hnil : (zero_val GoSlice : GoSlice) ↦* ([] : List Loc) $$ []
  · iapply ownSlice_nil
  ihave Hcap0 : ownSliceCap Loc (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave IH : iprop(∃ (n : w64) (sv : Loc) (osl : GoSlice) (qs : List Loc),
      "i" ∷ i_ptr ↦ n ∗ "s" ∷ s_ptr ↦ sv ∗ "out" ∷ out_ptr ↦ osl ∗ "Hout" ∷ osl ↦* qs ∗
      "Hcap" ∷ ownSliceCap Loc osl (DFrac.own 1) ∗
      "Hdone" ∷ ([∗list] q;s ∈ qs;somes (os.take (sint.nat n)), P q s) ∗
      "Hrest" ∷ ([∗list] p;o ∈ ps.drop (sint.nat n);os.drop (sint.nat n),
        match o with | none => ⌜p = null⌝ | some s => P p s) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝) $$ [i s out Hnil Hcap0 Hps]
  · iexists _, _, _, []
    iframe
    rw [show sint.nat (W64 0) = 0 from rfl]
    simp only [List.take_zero, List.drop_zero]
    iframe
    simp only [somes, List.filterMap_nil]
    isplitl []
    · iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
    ipureintro; constructor <;> word
  wp_for IH
  obtain ⟨hn0, hn1⟩ := Hn
  wp_if_destruct
  · have Hif : sint.Z n < sint.Z sl.len := by simpa using Hif
    have Hlt : sint.nat n < ps.length := by rw [Hsll.1]; word
    obtain ⟨x, Hx⟩ : ∃ x, ps[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨o, Ho⟩ : ∃ o, os[sint.nat n]? = some o := ⟨_, List.getElem?_eq_getElem (Hpl ▸ Hlt)⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) ps dq x hn0 $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; exact Hx
    try wp_auto
    have hdp : ps.drop (sint.nat n) = x :: ps.drop (sint.nat n + 1) := by
      rw [List.drop_eq_getElem_cons Hlt]; congr 1; exact (List.getElem?_eq_some_iff.1 Hx).2
    have hdo : os.drop (sint.nat n) = o :: os.drop (sint.nat n + 1) := by
      rw [List.drop_eq_getElem_cons (Hpl ▸ Hlt)]; congr 1; exact (List.getElem?_eq_some_iff.1 Ho).2
    have htk : os.take (sint.nat (n + W64 1)) = os.take (sint.nat n) ++ [o] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Ho]; rfl
    have hdrop : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    rw [hdp, hdo]
    icases BigSepL2.bigSepL2_cons.1 $$ Hrest with ⟨Hx, Hrest⟩
    cases o with
    | none =>
      icases Hx with %Hxn
      subst Hxn
      rw [decide_eq_true rfl]
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      rw [htk, hdrop]
      simp only [somes, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, id, List.append_nil]
      iframe
      ipureintro; constructor <;> word
    | some sv0 =>
      ihave %Hxnn := HP $$ Hx
      rw [decide_eq_false Hxnn]
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl0 ⟨Hsl0, -⟩
      wp_apply wp_slice_append $$ [Hout Hcap Hsl0] as %s2 ⟨Hs2, Hcap2, -⟩
      · iframe
      try wp_auto
      ihave Hdone : iprop([∗list] q;s ∈ qs ++ [x];somes (os.take (sint.nat n)) ++ [sv0], P q s) $$ [Hdone Hx]
      · iapply (BigSepL2.bigSepL2_snoc).2
        iframe
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      rw [htk, hdrop]
      simp only [somes, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, id]
      iframe
      ipureintro; constructor <;> word
  · have hnx : sint.nat n = ps.length := by rw [Hsll.1]; word
    try wp_auto
    iapply HΦ
    iexists qs
    iframe
    have htl : os.take (sint.nat n) = os := by rw [hnx, Hpl]; exact List.take_length
    rw [htl]
    iexact Hdone

end proof

end Etcdraft
end EtcdGrove
end Perennial
