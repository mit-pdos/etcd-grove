/-
**Helpers of `fieldpath`'s iterating proofs** (`ManagedFields.Equals`, `Set.Iterate`,
`iteratePrefix`, `EnsureNamedFieldsAreMembers`): managed fields' association lists (sorted keys,
lookups, extensionality, the map's size), and the views of a set's representation they need.

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

namespace fpD

/-! ## Association lists sorted by key -/

section alist
variable {α : Type}

/-- Strictly sorted keys, as a pairwise relation. -/
abbrev KSorted (l : List (GoString × α)) : Prop := l.Pairwise (fun p q => gsCompare p.1 q.1 < 0)

theorem gsLt_iff (a b : GoString) : gsLt a b = true ↔ gsCompare a b < 0 := by
  unfold gsLt
  have := fpL.gs_range a b
  constructor
  · intro h; simp at h; omega
  · intro h; simp; omega

theorem keysSorted_pairwise : ∀ l : List (GoString × α), keysSorted l = true → KSorted l
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | x :: y :: rest, h => by
    simp only [keysSorted, Bool.and_eq_true] at h
    have ih := keysSorted_pairwise (y :: rest) h.2
    have hxy := (gsLt_iff _ _).1 h.1
    refine List.Pairwise.cons ?_ ih
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact hxy
    · exact fpL.gs_trans _ _ _ hxy ((List.pairwise_cons.1 ih).1 z hz)

theorem lookupKV_some_mem : ∀ (l : List (GoString × α)) (k : GoString) (e : α),
    lookupKV k l = some e → (k, e) ∈ l
  | [], _, _, h => by simp [lookupKV] at h
  | (k', v) :: rest, k, e, h => by
    unfold lookupKV at h
    split at h
    · next hk => cases h; subst hk; simp
    · exact List.mem_cons_of_mem _ (lookupKV_some_mem rest k e h)

theorem mem_lookupKV : ∀ (l : List (GoString × α)) (k : GoString) (e : α), KSorted l →
    (k, e) ∈ l → lookupKV k l = some e
  | [], _, _, _, h => by simp at h
  | (k', v) :: rest, k, e, hs, h => by
    unfold lookupKV
    simp only [KSorted, List.pairwise_cons] at hs
    rcases List.mem_cons.1 h with h | h
    · cases h; simp
    · have hne : k' ≠ k := by
        intro hk; subst hk
        have := hs.1 (k', e) h
        have := (fpL.gs_zero k' k').2 rfl
        simp at *; omega
      rw [if_neg hne]
      exact mem_lookupKV rest k e hs.2 h

theorem lookupKV_iff (l : List (GoString × α)) (k : GoString) (e : α) (hs : KSorted l) :
    lookupKV k l = some e ↔ (k, e) ∈ l :=
  ⟨lookupKV_some_mem l k e, mem_lookupKV l k e hs⟩

theorem lookupKV_isSome_iff : ∀ (l : List (GoString × α)) (k : GoString),
    (lookupKV k l).isSome = true ↔ k ∈ l.map Prod.fst
  | [], _ => by simp [lookupKV]
  | (k', v) :: rest, k => by
    unfold lookupKV
    split
    · next hk => subst hk; simp
    · next hk =>
      rw [lookupKV_isSome_iff rest k]
      simp only [List.map_cons, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (h | h)
        · exact absurd h.symm hk
        · exact h

theorem keys_nodup (l : List (GoString × α)) (hs : KSorted l) : (l.map Prod.fst).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons p rest ih =>
    simp only [KSorted, List.pairwise_cons] at hs
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, ih hs.2⟩
    rintro ⟨q, hq, he⟩
    have := hs.1 q hq
    rw [he] at this
    have := (fpL.gs_zero p.1 p.1).2 rfl
    omega

/-- Two strictly sorted lists with the same members are equal. -/
theorem ksorted_ext : ∀ (a b : List (GoString × α)), KSorted a → KSorted b →
    (∀ x, x ∈ a ↔ x ∈ b) → a = b
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, h => by have := (h y).2 (by simp); simp at this
  | x :: _, [], _, _, h => by have := (h x).1 (by simp); simp at this
  | x :: xs, y :: ys, ha, hb, h => by
    simp only [KSorted, List.pairwise_cons] at ha hb
    have irr : ∀ k : GoString, ¬ gsCompare k k < 0 := fun k => by
      have := (fpL.gs_zero k k).2 rfl; omega
    have hxy : x = y := by
      rcases List.mem_cons.1 ((h x).1 (by simp)) with e | hx
      · exact e
      rcases List.mem_cons.1 ((h y).2 (by simp)) with e | hy
      · exact e.symm
      exact absurd (fpL.gs_trans _ _ _ (ha.1 y hy) (hb.1 x hx)) (irr _)
    subst hxy
    congr 1
    apply ksorted_ext xs ys ha.2 hb.2
    intro z
    constructor
    · intro hz
      rcases List.mem_cons.1 ((h z).1 (by simp [hz])) with e | h'
      · subst e; exact absurd (ha.1 z hz) (irr _)
      · exact h'
    · intro hz
      rcases List.mem_cons.1 ((h z).2 (by simp [hz])) with e | h'
      · subst e; exact absurd (hb.1 z hz) (irr _)
      · exact h'

/-- Managed fields with the same entries are equal (sorted). -/
theorem mf_ext (a b : MF) (ha : keysSorted a = true) (hb : keysSorted b = true)
    (h : ∀ k, a.get k = b.get k) : a = b := by
  have sa := keysSorted_pairwise a ha
  have sb := keysSorted_pairwise b hb
  apply ksorted_ext a b sa sb
  rintro ⟨k, e⟩
  rw [← lookupKV_iff a k e sa, ← lookupKV_iff b k e sb]
  exact Eq.to_iff (congrArg (· = some e) (h k))

/-- Managed fields of the same length, the first's entries the second's, are equal. -/
theorem mf_eq_of_sub (a b : MF) (ha : keysSorted a = true) (hb : keysSorted b = true)
    (hlen : a.length = b.length) (h : ∀ k e, a.get k = some e → b.get k = some e) : a = b := by
  have sa := keysSorted_pairwise a ha
  have sb := keysSorted_pairwise b hb
  have nda : a.Nodup := sa.imp (fun {p q} hpq e => by
    subst e; have := (fpL.gs_zero p.1 p.1).2 rfl; omega)
  have sub : a ⊆ b := by
    rintro ⟨k, e⟩ hx
    exact (lookupKV_iff b k e sb).1 (h k e ((lookupKV_iff a k e sa).2 hx))
  have hp := (List.subperm_of_subset nda sub).perm_of_length_le (by omega)
  exact ksorted_ext a b sa sb (fun x => hp.mem_iff)

/-- The size of a Go map whose keys are those of a sorted association list. -/
theorem size_eq {β : Type} (M : GMap GoString β) (l : List (GoString × α)) (hs : KSorted l)
    (hM : ∀ k, (M !! k).isSome = (lookupKV k l).isSome) : GMap.size M = l.length := by
  rw [GMap.size_eq_length M (l.map Prod.fst) (keys_nodup l hs), List.length_map]
  intro k
  rw [← lookupKV_isSome_iff, hM]

end alist

/-! ## Managed fields' maps -/

section rep
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem isMFL_lookup (M : GMap GoString GoInterface) : ∀ (mf : MF) (k : GoString) (e : VSet),
    KSorted mf → mf.get k = some e →
    isMFL (GF := GF) M mf ⊢ ∃ i, ⌜M !! k = some i⌝ ∗ isVSet i e
  | [], _, _, _, h => by simp [MF.get, lookupKV] at h
  | (k', e') :: rest, k, e, hs, h => by
    unfold isMFL
    iintro ⟨%i, %hi, #Hi, #Hr⟩
    by_cases hk : k' = k
    · subst hk
      simp [MF.get, lookupKV] at h; subst h
      iexists i; isplit
      · ipureintro; exact hi
      · iexact Hi
    · have h' : MF.get rest k = some e := by
        simp only [MF.get, lookupKV, if_neg hk] at h; exact h
      iapply isMFL_lookup M rest k e (List.pairwise_cons.1 hs).2 h'
      iexact Hr

theorem isVSet_mk (p : Loc) (e : VSet) :
    isSet (GF := GF) p e.set ⊢
      isVSet (interface.mkOk fieldpath.versionedSet.ty #(fieldpath.versionedSet.mk p e.version e.applied)) e := by
  iintro H; unfold isVSet; iexists p; iframe; ipureintro; rfl

end rep

end fpD

end smd
end EtcdGrove
end Perennial
