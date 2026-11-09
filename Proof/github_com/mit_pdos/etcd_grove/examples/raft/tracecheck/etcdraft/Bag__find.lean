/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Bag__find`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__find
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Msg__Equal

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

theorem Bag.find.wp_proof (wp_MsgEqual : Msg.Equal.spec (GF := GF) (hG := hG)) :
    Bag.find.spec (GF := GF) (hG := hG) := by
  intro g b p m
  wp_start as ⟨#Hg, #Hm⟩
  iunfold bagRO at Hg
  icases Hg with ⟨%items, #Hits, #Hib⟩
  ihave %Hil := ownSlice_len $$ Hits
  ihave %Hbl := BigSepL2.bigSepL2_length $$ Hib
  wp_auto
  ihave IH : iprop(∃ (n : w64) (itv : G.bagItem) (kv : w64),
      "i" ∷ i_ptr ↦ n ∗ "it" ∷ it_ptr ↦ itv ∗ "k" ∷ k_ptr ↦ kv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z g.items'.len ∧
        ∀ j < sint.nat n, ∀ x, b[j]? = some x → (x.1 == m) = false⌝) $$ [i it k]
  · iexists _, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, fun j hj => by rw [show sint.nat (W64 0) = 0 from rfl] at hj; omega⟩
  wp_for IH
  obtain ⟨hn0, hn1, hnb⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < items.length := by rw [Hil.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, items[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨x, Hx⟩ : ∃ x, b[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem (Hbl ▸ Hlt)⟩
    ihave ⟨#Hyx, %Hyc⟩ := BigSepL2.bigSepL2_lookup
      (Φ := fun _ it p => iprop(msgRO (GF := GF) it.msg' p.1 ∗ ⌜sint.Z it.count' = (p.2 : Int)⌝)) Hy Hx $$ Hib
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z g.items'.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index _ (sint.Z n) items DFrac.discard y hn0 $$ [Hits] as -
    · isplitr
      · iexact Hits
      ipureintro; exact Hy
    try wp_auto
    wp_apply wp_MsgEqual _ x.1 _ m $$ [Hyx Hm]
    · iframe Hyx Hm
    try wp_auto
    by_cases hxm : x.1 = m
    · rw [decide_eq_true hxm]
      wp_auto
      wp_for_post
      try wp_auto
      have : b.findIdx? (fun it => it.1 == m) = some (sint.nat n) := by
        rw [List.findIdx?_eq_some_iff_getElem]
        refine ⟨Hbl ▸ Hlt, ?_, fun j hj => ?_⟩
        · rw [List.getElem?_eq_some_iff] at Hx
          obtain ⟨_, Hx⟩ := Hx
          simp [Hx, hxm]
        · have hjb : j < b.length := Hbl ▸ Nat.lt_trans hj Hlt
          have := hnb j hj _ (List.getElem?_eq_getElem hjb)
          simpa using this
      rw [this]
      iapply HΦ; ipureintro; simp only; word
    · rw [decide_eq_false hxm]
      wp_auto
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
      intro j hj z hz
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact hnb j hj z hz
      · subst hj; rw [Hx] at hz; cases hz; simpa using hxm
  · try wp_auto
    have : b.findIdx? (fun it => it.1 == m) = none := by
      rw [List.findIdx?_eq_none_iff]
      intro z hz
      obtain ⟨j, hj, hjz⟩ := List.getElem_of_mem hz
      have hnl : sint.nat n = b.length := by rw [← Hbl, Hil.1]; word
      exact hnb j (by omega) z (by rw [List.getElem?_eq_some_iff]; exact ⟨hj, hjz⟩)
    rw [this]
    iapply HΦ; ipureintro; simp only; rfl

end proof

end Etcdraft
end EtcdGrove
end Perennial
