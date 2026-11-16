module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.lastObj

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input WEvent Obj)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem find_rev_some {α : Type} (p : α → Bool) (l : List α) (k : Nat) (a : α)
    (h : l[k]? = some a) (hp : p a = true) (hr : ∀ x ∈ l.drop (k + 1), p x = false) :
    l.reverse.find? p = some a := by
  obtain ⟨hk, hka⟩ := List.getElem?_eq_some_iff.mp h
  have hsplit : l = l.take k ++ a :: l.drop (k + 1) := by
    rw [← hka, List.getElem_cons_drop hk]; simp
  rw [hsplit]
  simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.find?_append,
    List.singleton_append, List.find?_cons, hp]
  rw [List.find?_eq_none.mpr (fun x hx => by simpa using hr x (List.mem_reverse.mp hx))]
  simp

theorem find_rev_none {α : Type} (p : α → Bool) (l : List α) (h : ∀ x ∈ l, p x = false) :
    l.reverse.find? p = none :=
  List.find?_eq_none.mpr (fun x hx => by simpa using h x (List.mem_reverse.mp hx))

theorem lastObj.wp_proof : lastObj.spec (GF := GF) (hG := hG) := by
  intro s evs
  wp_start as #Hs
  unfold wevsOwn
  icases Hs with ⟨%ws, #Hk, %He⟩
  subst He
  ihave %Hl := ownSlice_len $$ Hk
  wp_auto
  ihave HI : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗
      "%Hj" ∷ ⌜-1 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len ∧
        ∀ x ∈ (ws.map wevOf).drop (sint.Z j + 1).toNat,
          (fun e : WEv => decide (e.t ≠ 4 ∧ e.t ≠ 5)) x = false⌝ : IProp GF) $$ [i]
  · iexists _
    iframe
    ipureintro
    refine ⟨by word, by word, fun x hx => ?_⟩
    have h1 : (sint.Z (s.len - W64 1) + 1).toNat = ws.length := by
      have := Hl.2; rw [Hl.1]; word
    rw [h1, List.drop_of_length_le (by simp)] at hx
    cases hx
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := ⟨Hif, Hj.2.1⟩
    list_elem ws (sint.nat j) as w
    icases ownSlice_elem_acc (sint.Z j) w s DFrac.discard _ Hb'.1 Hw_lookup $$ Hk with ⟨#Hel, -⟩
    iStructNamed Hel
    simp only [Hb', _root_.and_self, ↓reduceIte]
    (try wp_auto)
    have hl : (ws.map wevOf)[sint.nat j]? = some (wevOf w) := by simp [Hw_lookup]
    have hj1 : (sint.Z j + 1).toNat = sint.nat j + 1 := by word
    have hrest := Hj.2.2
    rw [hj1] at hrest
    have hcont : (fun e : WEv => decide (e.t ≠ 4 ∧ e.t ≠ 5)) (wevOf w) = false →
        ∀ x ∈ (ws.map wevOf).drop (sint.Z (j - W64 1) + 1).toNat,
          (fun e : WEv => decide (e.t ≠ 4 ∧ e.t ≠ 5)) x = false := by
      intro hw x hx
      have hj2 : (sint.Z (j - W64 1) + 1).toNat = sint.nat j := by word
      rw [hj2, List.drop_eq_getElem_cons (by simp; word)] at hx
      have he : (ws.map wevOf)[sint.nat j]'(by simp; word) = wevOf w :=
        Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hl)
      rw [he] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hw
      · exact hrest x hx
    have h4 : uint.nat w.Type' = 4 ↔ w.Type' = W64 4 := by
      constructor
      · intro h; word
      · intro h; rw [h]; rfl
    have h5 : uint.nat w.Type' = 5 ↔ w.Type' = W64 5 := by
      constructor
      · intro h; word
      · intro h; rw [h]; rfl
    wp_if_destruct
    · have hT4 := Hif
      (try simp only [Hb', _root_.and_self, ↓reduceIte])
      (try wp_auto)
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      refine ⟨by word, by word, hcont (by simp [wevOf, hT4])⟩
    · have hT4 := Hif
      (try simp only [Hb', _root_.and_self, ↓reduceIte])
      (try wp_auto)
      wp_if_destruct
      · have hT5 := Hif
        (try simp only [Hb', _root_.and_self, ↓reduceIte])
        (try wp_auto)
        wp_for_post
        iframe
        iexists _
        iframe
        ipureintro
        refine ⟨by word, by word, hcont (by simp [wevOf, hT5])⟩
      · have hT5 := Hif
        (try simp only [Hb', _root_.and_self, ↓reduceIte])
        (try wp_auto)
        wp_for_post
        iapply HΦ
        ipureintro
        simp only [lastObjL, ↓reduceIte]
        rw [find_rev_some _ _ (sint.nat j) (wevOf w) hl
          (by simp only [wevOf, ne_eq, h4, h5, decide_eq_true_eq]; exact ⟨hT4, hT5⟩) hrest]
        rfl
  · (try wp_auto)
    iapply HΦ
    ipureintro
    have hj : sint.Z j = -1 := by have := Hj.1; word
    rw [hj] at Hj
    simp only [lastObjL, Bool.false_eq_true, ↓reduceIte]
    rw [find_rev_none _ _ (by simpa using Hj.2.2)]
    rfl

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
