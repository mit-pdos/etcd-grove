module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.firstBookmark

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel WEvent change)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem findIdx?_at {α : Type} (p : α → Bool) (l : List α) (j : Nat) (e : α)
    (hj : l[j]? = some e) (he : p e = true) (hpre : ∀ x ∈ l.take j, p x = false) :
    l.findIdx? p = some j := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    cases j with
    | zero =>
      simp at hj; subst hj; simp [List.findIdx?_cons, he]
    | succ j =>
      have ha : p a = false := hpre a (by simp)
      simp at hj
      rw [List.findIdx?_cons, ha]
      simp [ih j hj (fun x hx => hpre x (by simp [hx]))]

theorem firstBookmark.wp_proof : firstBookmark.spec (GF := GF) (hG := hG) := by
  intro s evs
  wp_start as #Hs
  unfold wevsOwn
  icases Hs with ⟨%ws, #Hk, %He⟩
  subst He
  ihave %Hl := ownSlice_len $$ Hk
  wp_auto
  rename_i iu_ptr
  irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
  ihave HI : (∃ (j k : w64) (evv : WEvent),
      "i" ∷ i_ptr ↦ j ∗ "Hiu" ∷ iu_ptr ↦ k ∗ "ev" ∷ ev_ptr ↦ evv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len ∧
        ∀ e ∈ (ws.map wevOf).take (sint.nat j), decide (e.t = 3) = false⌝ : IProp GF) $$ [i ev Hiu]
  · iexists W64 0, zero_val w64, _
    iframe
    ipureintro; refine ⟨by word, by word, ?_⟩
    intro e he
    simp [show sint.nat (0#64 : w64) = 0 from rfl] at he
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len :=
      ⟨Hj.1, by first | exact Hif | exact dec_true Hif⟩
    list_elem ws (sint.nat j) as w
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index s (sint.Z j) ws _ w Hj.1 $$ [Hk] as -
    · isplit
      · iexact Hk
      · ipureintro; exact Hw_lookup
    have hl : (ws.map wevOf)[sint.nat j]? = some (wevOf w) := by simp [Hw_lookup]
    have h3 : uint.nat w.Type' = 3 ↔ w.Type' = W64 3 := by
      constructor
      · intro h; word
      · intro h; rw [h]; rfl
    have ht : (wevOf w).t = uint.nat w.Type' := rfl
    (try wp_auto)
    wp_if_destruct
    · wp_for_post
      iapply HΦ
      ipureintro
      rw [findIdx?_at _ _ (sint.nat j) (wevOf w) hl (by simp [ht, h3, Hif]) Hj.2.2]
      simp only
      word
    · wp_for_post
      iframe
      iexists j + W64 1, _, w
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, hl]
      intro e he
      simp only [List.mem_append, Option.toList_some, List.mem_singleton] at he
      rcases he with he | rfl
      · exact Hj.2.2 e he
      · simpa [ht, h3] using Hif
  · have hge : ¬ sint.Z j < sint.Z s.len := by first | exact Hif | exact dec_false Hif
    (try rw [decide_eq_false hge, if_pos (decide_eq_true rfl)])
    (try wp_auto)
    iapply HΦ
    ipureintro
    have hfull : (ws.map wevOf).take (sint.nat j) = ws.map wevOf := List.take_of_length_le (by simp; word)
    rw [hfull] at Hj
    rw [List.findIdx?_eq_none_iff.mpr (fun x hx => by simpa using Hj.2.2 x hx)]
    rfl

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
