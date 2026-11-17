/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Bag__Domain`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__Domain

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

theorem Bag.Domain.wp_proof : Bag.Domain.spec (GF := GF) (hG := hG) := by
  intro g b
  wp_start as #Hg
  iunfold bagRO at Hg
  icases Hg with ⟨%items, #Hits, #Hib⟩
  ihave %Hil := ownSlice_len $$ Hits
  ihave %Hbl := BigSepL2.bigSepL2_length $$ Hib
  iapply wp_fupd
  wp_auto
  wp_apply wp_slice_make2 (V := Loc) g.items'.len $$ [] as %out ⟨Hout, -⟩
  · ipureintro; exact Hil.2
  try wp_auto
  ihave IH : iprop(∃ (n : w64) (itv : G.bagItem) (kv : w64) (L : List Loc),
      "i" ∷ i_ptr ↦ n ∗ "it" ∷ it_ptr ↦ itv ∗ "k" ∷ k_ptr ↦ kv ∗ "Hout" ∷ out ↦* L ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z g.items'.len ∧ L.length = items.length ∧
        ∀ j < sint.nat n, L[j]? = (items[j]?).map (fun it => it.msg')⌝) $$ [i it k Hout]
  · iexists _, _, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by simp [Hil.1], fun j hj => by rw [show sint.nat (W64 0) = 0 from rfl] at hj; omega⟩
  wp_for IH
  obtain ⟨hn0, hn1, hnL, hnj⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < items.length := by rw [Hil.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, items[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z g.items'.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index _ (sint.Z n) items DFrac.discard y hn0 $$ [Hits] as -
    · isplitr
      · iexact Hits
      ipureintro; exact Hy
    try wp_auto
    ihave %HoL := ownSlice_len $$ Hout
    have hno : sint.Z n < sint.Z out.len := by
      have : sint.nat n < L.length := by rw [hnL]; exact Hlt
      rw [HoL.1] at this; word
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z out.len from ⟨hn0, hno⟩))]
    wp_apply wp_store_slice_index out (sint.Z n) L y.msg' $$ [Hout] as Hout
    · iframe Hout; ipureintro
      refine ⟨hn0, ?_⟩
      have : sint.nat n < L.length := by rw [hnL]; exact Hlt
      word
    try wp_auto
    wp_for_post
    iframe
    iexists _, _, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [List.length_set, hnL], ?_⟩
    rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
    intro j hj
    rw [show (sint.Z n).toNat = sint.nat n from rfl, List.getElem?_set]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [ite_eq_right (Nat.ne_of_gt hj)]; exact hnj j hj
    · subst hj
      have : sint.nat n < L.length := by rw [hnL]; exact Hlt
      rw [ite_eq_left rfl, Hy]; simp [this]
  · have hnx : sint.nat n = items.length := by rw [Hil.1]; word
    have hLe : L = items.map (fun it => it.msg') := by
      apply List.ext_getElem?
      intro j
      rw [List.getElem?_map]
      by_cases hj : j < sint.nat n
      · exact hnj j hj
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]; rfl
    subst hLe
    imod ownSlice_persist $$ Hout with #Hout
    imodintro
    iapply HΦ
    iunfold msgsRO
    iexists _
    iframe Hout
    unfold Bag.domain
    iapply (BigSepL2.bigSepL2_map (PROP := IProp GF) (fun it : G.bagItem => it.msg') (Prod.fst : Msg × Nat → Msg)
      (Φ := fun _ q m => msgRO (GF := GF) q m)).2
    iapply BigSepL2.bigSepL2_mono_of_forall (Φ := fun _ it p => iprop(msgRO (GF := GF) it.msg' p.1 ∗ ⌜sint.Z it.count' = (p.2 : Int)⌝))
    · intro k x1 x2; exact sep_elim_left
    iexact Hib

end proof

end Etcdraft
end EtcdGrove
end Perennial
