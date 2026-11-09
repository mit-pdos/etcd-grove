/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Bag__Minus`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__Minus
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__sub

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section pure

/-- `Bag.sub` keeps the messages distinct. -/
theorem Bag.sub_nodup (b : Bag) (m : Msg) (n : Nat) (hnd : (b.map Prod.fst).Nodup) :
    ((b.sub m n).map Prod.fst).Nodup := by
  have hsub : ∀ l : Bag, List.Sublist ((l.sub m n).map Prod.fst) (l.map Prod.fst) := by
    intro l
    induction l with
    | nil => exact List.Sublist.slnil
    | cons x xs ih =>
      unfold Bag.sub at ih ⊢
      rw [List.filterMap_cons]
      by_cases hx : (x.1 == m) = true
      · by_cases hc : x.2 > n
        · simp only [hx, hc, ite_true, List.map_cons]; exact ih.cons_cons _
        · simp only [hx, hc, ite_true, ite_false, List.map_cons]; exact ih.cons _
      · simp only [hx, Bool.false_eq_true, ite_false, List.map_cons]; exact ih.cons_cons _
  exact hnd.sublist (hsub b)

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem Bag.Minus.wp_proof (wp_sub : Bag.sub.spec (GF := GF) (hG := hG)) :
    Bag.Minus.spec (GF := GF) (hG := hG) := by
  intro g b h c
  wp_start as ⟨#Hg, #Hh, %Hnd⟩
  ihave #Hh0 := Hh
  iunfold bagRO at Hh0
  icases Hh0 with ⟨%citems, #Hcits, #Hcib⟩
  ihave %Hcil := ownSlice_len $$ Hcits
  ihave %Hcbl := BigSepL2.bigSepL2_length $$ Hcib
  wp_auto
  ihave IH : iprop(∃ (j : w64) (itv : G.bagItem) (outv : G.Bag),
      "i" ∷ i_ptr ↦ j ∗ "it" ∷ it_ptr ↦ itv ∗ "out" ∷ out_ptr ↦ outv ∗
      "Hacc" ∷ bagRO outv ((c.take (sint.nat j)).foldl (fun acc it => acc.sub it.1 it.2) b) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z h.items'.len ∧
        List.Nodup (((c.take (sint.nat j)).foldl (fun acc it => acc.sub it.1 it.2) b).map Prod.fst)⌝) $$ [i it out]
  · iexists _, _, _
    iframe
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.foldl_nil]
    isplitr
    · iexact Hg
    ipureintro
    refine ⟨by word, by word, Hnd⟩
  wp_for IH
  obtain ⟨hn0, hn1, hacc⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat j < citems.length := by rw [Hcil.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, citems[sint.nat j]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨x, Hx⟩ : ∃ x, c[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem (Hcbl ▸ Hlt)⟩
    ihave ⟨#Hyx, %Hyc⟩ := BigSepL2.bigSepL2_lookup
      (Φ := fun _ it p => iprop(msgRO (GF := GF) it.msg' p.1 ∗ ⌜sint.Z it.count' = (p.2 : Int)⌝)) Hy Hx $$ Hcib
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z h.items'.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index _ (sint.Z j) citems DFrac.discard y hn0 $$ [Hcits] as -
    · isplitr
      · iexact Hcits
      ipureintro; exact Hy
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_sub_unfold.method_unfold]
    try wp_auto
    have htake : (c.take (sint.nat (j + W64 1))).foldl (fun acc it => acc.sub it.1 it.2) b =
        ((c.take (sint.nat j)).foldl (fun acc it => acc.sub it.1 it.2) b).sub x.1 x.2 := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hx]
      simp
    wp_apply wp_sub _ _ y.msg' x.1 y.count' x.2 $$ [Hacc Hyx] as %g' Hg'
    · iframe Hacc Hyx
      ipureintro
      exact ⟨hacc, Hyc⟩
    try wp_auto
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    rw [htake]
    iframe Hg'
    ipureintro
    refine ⟨by word, by word, ?_⟩
    exact Bag.sub_nodup _ _ _ hacc
  · try wp_auto
    have hjx : sint.nat j = c.length := by rw [← Hcbl, Hcil.1]; word
    rw [hjx, List.take_length]
    iapply HΦ
    unfold Bag.minus
    iexact Hacc

end proof

end Etcdraft
end EtcdGrove
end Perennial
