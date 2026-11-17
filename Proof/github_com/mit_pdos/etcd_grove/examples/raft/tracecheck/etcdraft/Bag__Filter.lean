/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Bag__Filter`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__Filter

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

theorem Bag.Filter.wp_proof : Bag.Filter.spec (GF := GF) (hG := hG) := by
  intro g b pf pred
  wp_start as ⟨#Hg, #Hpred⟩
  iunfold bagRO at Hg
  icases Hg with ⟨%items, #Hits, #Hib⟩
  ihave %Hil := ownSlice_len $$ Hits
  ihave %Hbl := BigSepL2.bigSepL2_length $$ Hib
  iapply wp_fupd
  wp_auto
  ihave #Hnil := ownSlice_nil (V := G.bagItem) (GF := GF) (DFrac.own 1)
  ihave Hcap0 := ownSliceCap_nil (V := G.bagItem) (GF := GF)
  ihave IH : iprop(∃ (j : w64) (itv : G.bagItem) (osl : GoSlice) (L : List G.bagItem),
      "i" ∷ i_ptr ↦ j ∗ "it" ∷ it_ptr ↦ itv ∗ "items" ∷ items_ptr ↦ osl ∗
      "Hout" ∷ osl ↦* L ∗ "Hcap" ∷ ownSliceCap G.bagItem osl (DFrac.own 1) ∗
      "Hrel" ∷ ([∗list] it;q ∈ L;(b.take (sint.nat j)).filter (fun it => pred it.1),
        msgRO (GF := GF) it.msg' q.1 ∗ ⌜sint.Z it.count' = (q.2 : Int)⌝) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z g.items'.len⌝) $$ [i it items Hcap0]
  · iexists _, _, slice.nil, []
    iframe
    isplitr
    · iexact Hnil
    isplitr
    · iexact Hcap0
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil]
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; iempintro
    ipureintro; exact ⟨by word, by word⟩
  wp_for IH
  obtain ⟨hn0, hn1⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat j < items.length := by rw [Hil.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, items[sint.nat j]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨x, Hx⟩ : ∃ x, b[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem (Hbl ▸ Hlt)⟩
    ihave ⟨#Hyx, %Hyc⟩ := BigSepL2.bigSepL2_lookup
      (Φ := fun _ it p => iprop(msgRO (GF := GF) it.msg' p.1 ∗ ⌜sint.Z it.count' = (p.2 : Int)⌝)) Hy Hx $$ Hib
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z g.items'.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index _ (sint.Z j) items DFrac.discard y hn0 $$ [Hits] as -
    · isplitr
      · iexact Hits
      ipureintro; exact Hy
    try wp_auto
    ihave #Hf := Hpred $$ %y.msg' %x.1
    wp_apply Hf $$ [Hyx]
    · iexact Hyx
    try wp_auto
    have htake : (b.take (sint.nat (j + W64 1))).filter (fun it => pred it.1) =
        (b.take (sint.nat j)).filter (fun it => pred it.1) ++ (if pred x.1 then [x] else []) := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hx]
      simp only [Option.toList_some, List.filter_append, List.filter_cons, List.filter_nil]
    by_cases hp : pred x.1 = true
    · rw [hp]
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl0 ⟨Hsl0, -⟩
      wp_apply wp_slice_append $$ [Hout Hcap Hsl0] as %s2 ⟨Hs2, Hcap2, -⟩
      · iframe
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      isplitl [Hrel]
      · rw [htake, ite_eq_left hp]
        iapply (BigSepL2.bigSepL2_snoc).2
        iframe Hrel Hyx
        ipureintro; exact Hyc
      ipureintro; exact ⟨by word, by word⟩
    · rw [Bool.not_eq_true] at hp
      rw [hp]
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      isplitl [Hrel]
      · rw [htake, ite_eq_right (by simp [hp]), List.append_nil]
        iexact Hrel
      ipureintro; exact ⟨by word, by word⟩
  · have hjx : sint.nat j = b.length := by rw [← Hbl, Hil.1]; word
    rw [hjx, List.take_length] at *
    try wp_auto
    imod ownSlice_persist $$ Hout with #Hout
    imodintro
    iapply HΦ
    unfold Bag.filterMsgs
    iunfold bagRO
    iexists _
    iframe Hout
    iexact Hrel

end proof

end Etcdraft
end EtcdGrove
end Perennial
