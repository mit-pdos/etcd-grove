/-
**`fieldpath`'s laws of owned managed fields, proved** (`fieldpath/Vocab.lean`: `ownMF_persist`,
`ownMF_empty`, `ownMF_access`), and the facts on `isMFL` (a map's entries) behind them and behind
`ManagedFields.Equals`.

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

namespace fpL

/-! ## Sorted association lists -/

theorem gsLt_iff (a b : GoString) : gsLt a b = true ↔ gsCompare a b < 0 := by
  unfold gsLt
  have := gs_range a b
  constructor
  · intro h; simp at h; omega
  · intro h; simp; omega

theorem gsLt_trans (a b c : GoString) (h1 : gsLt a b = true) (h2 : gsLt b c = true) :
    gsLt a c = true := by
  rw [gsLt_iff] at *; exact gs_trans a b c h1 h2

theorem gsLt_irrefl (a : GoString) : gsLt a a = false := by
  have := (gs_zero a a).2 rfl
  unfold gsLt; simp [this]

/-- In a sorted list, the head key is below every later key. -/
theorem keysSorted_head {α : Type} (k : GoString) (e : α) :
    ∀ (rest : List (GoString × α)), keysSorted ((k, e) :: rest) = true →
      ∀ k' e', (k', e') ∈ rest → gsLt k k' = true
  | [], _, _, _, h => by simp at h
  | (k2, e2) :: rest, hs, k', e', hm => by
    simp only [keysSorted, Bool.and_eq_true] at hs
    rcases List.mem_cons.1 hm with h | h
    · cases h; exact hs.1
    · exact gsLt_trans _ _ _ hs.1 (keysSorted_head k2 e2 rest hs.2 k' e' h)

theorem keysSorted_tail {α : Type} (p : GoString × α) (rest : List (GoString × α))
    (h : keysSorted (p :: rest) = true) : keysSorted rest = true := by
  match rest, h with
  | [], _ => rfl
  | (k2, e2) :: rest, h => simp only [keysSorted, Bool.and_eq_true] at h; exact h.2

theorem lookupKV_mem {α : Type} (k : GoString) (e : α) :
    ∀ (l : List (GoString × α)), lookupKV k l = some e → (k, e) ∈ l
  | [], h => by simp [lookupKV] at h
  | (k', e') :: rest, h => by
    simp only [lookupKV] at h
    split at h
    · cases h; subst ‹k' = k›; simp
    · exact List.mem_cons_of_mem _ (lookupKV_mem k e rest h)

end fpL

/-! ## A map's entries -/

section mfl
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

namespace fpL

theorem isMFL_cons_eq (M : GMap GoString GoInterface) (k : GoString) (e : VSet) (rest : MF) :
    isMFL (GF := GF) M ((k, e) :: rest) =
      iprop(∃ i : GoInterface, ⌜M !! k = some i⌝ ∗ isVSet i e ∗ isMFL M rest) := by
  simp only [isMFL]

/-- Every entry of the model, read from the map. -/
theorem isMFL_get (M : GMap GoString GoInterface) :
    ∀ (mf : MF), isMFL (GF := GF) M mf ⊢
      □ (∀ k i e, ⌜M !! k = some i ∧ mf.get k = some e⌝ -∗ isVSet i e)
  | [] => by
    iintro _; imodintro; iintro %k %i %e %h
    simp [MF.get, lookupKV] at h
  | (k', e') :: rest => by
    rw [isMFL_cons_eq]
    iintro ⟨%i', %hi', #Hv, #Hr⟩
    ihave #IH := isMFL_get M rest $$ Hr
    imodintro
    iintro %k %i %e %h
    obtain ⟨hk, he⟩ := h
    simp only [MF.get, lookupKV] at he
    by_cases hkk : k' = k
    · subst hkk
      simp only [↓reduceIte, Option.some.injEq] at he
      subst he
      rw [hi'] at hk; cases hk
      iexact Hv
    · simp only [hkk, ↓reduceIte] at he
      iapply IH $$ %k %i %e
      ipureintro; exact ⟨hk, he⟩

/-- A map's entries, from a model whose keys are the map's and whose entries are readable. -/
theorem isMFL_intro (M : GMap GoString GoInterface) (mf : MF)
    (hkeys : ∀ k, (M !! k).isSome = (mf.get k).isSome) :
    ∀ (l : MF), keysSorted l = true → (∀ k e, lookupKV k l = some e → mf.get k = some e) →
      □ (∀ k i e, ⌜M !! k = some i ∧ mf.get k = some e⌝ -∗ isVSet (GF := GF) i e) ⊢ isMFL M l
  | [], _, _ => by iintro _; unfold isMFL; itrivial
  | (k, e) :: rest, hs, hl => by
    iintro #H
    rw [isMFL_cons_eq]
    have he : mf.get k = some e := hl k e (by simp [lookupKV])
    have hsome := hkeys k
    rw [he] at hsome
    obtain ⟨i, hi⟩ : ∃ i, M !! k = some i := Option.isSome_iff_exists.1 (by simpa using hsome)
    iexists i
    isplitr
    · ipureintro; exact hi
    isplitr
    · iapply H $$ %k %i %e; ipureintro; exact ⟨hi, he⟩
    have hrest : ∀ k2 e2, lookupKV k2 rest = some e2 → mf.get k2 = some e2 := by
      intro k2 e2 h2
      apply hl
      simp only [lookupKV]
      have hne : k ≠ k2 := by
        intro hkk; subst hkk
        have := keysSorted_head k e rest hs k e2 (lookupKV_mem k e2 rest h2)
        rw [gsLt_irrefl] at this; cases this
      simp only [hne, ↓reduceIte]
      exact h2
    iapply isMFL_intro M mf hkeys rest (keysSorted_tail _ _ hs) hrest
    iexact H

end fpL

/-! ## The laws -/

theorem ownMF_persist_law_holds : ownMF_persist.law (GF := GF) := by
  intro m mf
  unfold ownMF isMF
  iintro ⟨%M, Hm, %h, #Hl⟩
  imod ownMap_persist $$ Hm with Hm
  imodintro
  iexists M; iframe; isplitr
  · ipureintro; exact h
  · iexact Hl

theorem ownMF_empty_law_holds : ownMF_empty.law (GF := GF) := by
  intro m
  unfold ownMF
  iintro Hm
  iexists ∅; iframe
  isplitr
  · ipureintro
    refine ⟨rfl, fun k => ?_⟩
    simp [MF.none, MF.get, lookupKV]
  · unfold MF.none isMFL; itrivial

theorem ownMF_access_law_holds : ownMF_access.law (GF := GF) := by
  intro m mf
  unfold ownMF
  iintro ⟨%M, Hm, %h, #Hl⟩
  iexists M; iframe
  isplitr
  · ipureintro; exact h
  isplitr
  · iapply fpL.isMFL_get M mf; iexact Hl
  iintro %M' %mf' Hm' %h' #H'
  iexists M'; iframe
  isplitr
  · ipureintro; exact h'
  iapply fpL.isMFL_intro M' mf' h'.2 mf' h'.1 (fun k e he => he)
  iexact H'

end mfl

end smd
end EtcdGrove
end Perennial
