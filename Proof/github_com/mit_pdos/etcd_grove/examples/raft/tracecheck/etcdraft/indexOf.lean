/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `indexOf`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.indexOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.TState__Equal

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

theorem findIdx?_of_prefix {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (n : Nat) (x : α), xs[n]? = some x → (xs.take n).all (fun y => !p y) = true →
      p x = true → xs.findIdx? p = some n
  | [], _, _, h, _, _ => by simp at h
  | y :: ys, 0, x, h, _, hx => by
    simp at h; subst h; simp [List.findIdx?_cons, hx]
  | y :: ys, n + 1, x, h, hall, hx => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.take_succ_cons, List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hall
    rw [List.findIdx?_cons, hall.1]
    simp only [Bool.false_eq_true, ite_false]
    rw [findIdx?_of_prefix p ys n x h hall.2 hx]
    rfl

theorem findIdx?_none_of_all {α : Type} (p : α → Bool) (xs : List α)
    (h : xs.all (fun y => !p y) = true) : xs.findIdx? p = none := by
  rw [List.findIdx?_eq_none_iff]
  intro y hy
  have := List.all_eq_true.1 h y hy
  simpa using this

theorem indexOf.wp_proof (wp_Equal : TState.Equal.spec (GF := GF) (hG := hG)) :
    indexOf.spec (GF := GF) (hG := hG) := by
  intro sl dq gs xs g ts
  wp_start as ⟨Hsl, #Hl, #Hts⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hl
  wp_auto
  ihave IH : iprop(∃ (n kk : w64) (u : G.TState),
      "i" ∷ i_ptr ↦ n ∗ "us" ∷ us_ptr ↦ u ∗ "k" ∷ k_ptr ↦ kk ∗ "Hsl" ∷ sl ↦*{dq} gs ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        (xs.take (sint.nat n)).all (fun y => !y.eq ts) = true⌝) $$ [i us k Hsl]
  · iexists _, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
  wp_for IH
  obtain ⟨hn0, hn1, hna⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < gs.length := by clear hna; rw [Hlen.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, gs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨x, Hx⟩ : ∃ x, xs[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem (Hll ▸ Hlt)⟩
    ihave #Hyx := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => tstateRO (GF := GF) a b) Hy Hx $$ Hl
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index _ (sint.Z n) gs dq y hn0 $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; exact Hy
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.TState.TypeAssumptions.ptr_Equal_unfold.method_unfold]
    try wp_auto
    wp_apply wp_Equal y x g ts $$ [Hyx Hts]
    · iframe Hyx Hts
    cases he : x.eq ts
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      refine ⟨by clear hna; word, by clear hna; word, ?_⟩
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by clear hna; word, List.take_add_one, Hx]
      simp [hna, he]
    · try wp_auto
      wp_for_post
      try wp_auto
      iapply HΦ
      iframe
      ipureintro
      rw [findIdx?_of_prefix _ xs (sint.nat n) x Hx hna he]
      clear hna; word
  · try wp_auto
    have hnx : sint.nat n = xs.length := by clear hna; rw [← Hll, Hlen.1]; word
    rw [hnx, List.take_length] at hna
    iapply HΦ
    iframe
    ipureintro
    rw [findIdx?_none_of_all _ xs hna]; rfl

end proof

end Etcdraft
end EtcdGrove
end Perennial
