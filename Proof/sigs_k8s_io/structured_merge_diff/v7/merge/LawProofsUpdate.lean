/-
**`Updater.update`'s pure facts**: the conflicts map (`conflictsMF`) and the managers after the
update (`afterUpdate`) read key by key, kept sorted, and the laws `mfPairs_conflictsMF`,
`conflictsMF_nil_iff`, `conflictsMF_sorted`, `afterUpdate_sorted`; and `isMF` built from a
persistent map whose entries are read through a model.
Prove phase (2026-11-21).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.LawProofsM1
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

namespace MUpd

/-- Reading a key of a sorted list filtered by a key-keeping function. -/
theorem get_filterMap (f : GoString × VSet → Option (GoString × VSet))
    (hf : ∀ k e r, f (k, e) = some r → r.1 = k) :
    ∀ (mf : MF), keysSorted mf = true → ∀ k,
      MF.get (mf.filterMap f) k = (MF.get mf k).bind (fun e => (f (k, e)).map Prod.snd)
  | [], _, k => by simp [MF.get, lookupKV]
  | (k', e') :: rest, hs, k => by
    have ih := get_filterMap f hf rest (fpL.keysSorted_tail _ _ hs) k
    have hnot : ∀ e, lookupKV k' rest ≠ some e := by
      intro e he
      have := fpL.keysSorted_head k' e' rest hs k' e (fpL.lookupKV_mem k' e rest he)
      rw [fpL.gsLt_irrefl] at this; cases this
    simp only [List.filterMap_cons]
    by_cases hk : k' = k
    · subst hk
      cases hfe : f (k', e') with
      | none =>
        simp only [MF.get] at ih ⊢
        rw [ih]
        cases hl : lookupKV k' rest with
        | none => simp [lookupKV, hfe]
        | some e => exact absurd hl (hnot e)
      | some r =>
        obtain ⟨k1, e1⟩ := r
        have := hf _ _ _ hfe; simp only at this; subst this
        simp [MF.get, lookupKV, hfe]
    · cases hfe : f (k', e') with
      | none =>
        simp only [MF.get] at ih ⊢
        rw [ih]; simp [lookupKV, hk]
      | some r =>
        obtain ⟨k1, e1⟩ := r
        have := hf _ _ _ hfe; simp only at this; subst this
        simp only [MF.get] at ih ⊢
        simp only [lookupKV, hk, ite_false]
        exact ih

theorem filterMap_sorted (f : GoString × VSet → Option (GoString × VSet))
    (hf : ∀ k e r, f (k, e) = some r → r.1 = k) (mf : MF) (hs : keysSorted mf = true) :
    keysSorted (mf.filterMap f) = true := by
  rw [LawProofs.keysSorted_iff_pairwise] at hs ⊢
  refine List.Pairwise.filterMap f ?_ hs
  intro a b hab a' ha' b' hb'
  obtain ⟨ka, ea⟩ := a; obtain ⟨kb, eb⟩ := b
  have h1 := hf _ _ _ ha'; have h2 := hf _ _ _ hb'
  rw [h1, h2]; exact hab

theorem conflictsMF_key (mf : MF) (mgr : GoString) (c : Cmp) : ∀ k e r,
    (fun (me : GoString × VSet) =>
      if me.1 = mgr then none else
      let s := me.2.set.inter (c.modified.union c.added)
      if s.IsEmpty then none else some (me.1, (⟨s, me.2.version, false⟩ : VSet))) (k, e) = some r →
      r.1 = k := by
  intro k e r h
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

theorem conflictsMF_get (mf : MF) (mgr : GoString) (c : Cmp) (hs : keysSorted mf = true)
    (k : GoString) : (conflictsMF mf mgr c).get k = (mf.get k).bind (fun e =>
      if k = mgr then none else
      if (e.set.inter (c.modified.union c.added)).IsEmpty then none
      else some ⟨e.set.inter (c.modified.union c.added), e.version, false⟩) := by
  unfold conflictsMF
  rw [get_filterMap _ (conflictsMF_key mf mgr c) mf hs k]
  cases mf.get k with
  | none => rfl
  | some e =>
    simp only [Option.bind_some]
    split
    · rfl
    · split <;> rfl

theorem conflictsMF_sorted_law_holds : conflictsMF_sorted.law := by
  intro mf mgr c hs
  exact filterMap_sorted _ (conflictsMF_key mf mgr c) mf hs

theorem afterUpdate_key (mgr : GoString) (confl : FSet (GoString × Path)) (removed : PathSet) :
    ∀ k e r,
    (fun (me : GoString × VSet) =>
      let s := if me.1 = mgr then me.2.set
        else (me.2.set.diff (conflictsOfMgr confl me.1)).diff removed
      if s.IsEmpty then none else some (me.1, { me.2 with set := s })) (k, e) = some r →
      r.1 = k := by
  intro k e r h
  revert h
  dsimp only
  generalize (if k = mgr then e.set else (e.set.diff (conflictsOfMgr confl k)).diff removed) = s
  intro h
  split at h
  · cases h
  · cases h; rfl

theorem afterUpdate_get (mf : MF) (mgr : GoString) (confl : FSet (GoString × Path))
    (removed : PathSet) (hs : keysSorted mf = true) (k : GoString) :
    (afterUpdate mf mgr confl removed).get k = (mf.get k).bind (fun e =>
      let s := if k = mgr then e.set else (e.set.diff (conflictsOfMgr confl k)).diff removed
      if s.IsEmpty then none else some { e with set := s }) := by
  unfold afterUpdate
  rw [get_filterMap _ (afterUpdate_key mgr confl removed) mf hs k]
  cases mf.get k with
  | none => rfl
  | some e =>
    simp only [Option.bind_some]
    split <;> split <;> rfl

theorem afterUpdate_sorted_law_holds : afterUpdate_sorted.law := by
  intro mf mgr confl removed hs
  exact filterMap_sorted _ (afterUpdate_key mgr confl removed) mf hs

theorem mem_conflictsOf (mf : MF) (mgr : GoString) (c : Cmp) (x : GoString × Path) :
    x ∈ conflictsOf mf mgr c ↔
      ∃ me ∈ mf, me.1 ≠ mgr ∧ x.1 = me.1 ∧ x.2 ∈ me.2.set.inter (c.modified.union c.added) := by
  induction mf with
  | nil =>
    unfold conflictsOf
    simp only [List.foldr_nil, List.not_mem_nil, false_and, exists_false, iff_false]
    intro h
    exact (FSet_isEmpty_iff_law_holds (FSet.empty : FSet (GoString × Path))).1 (by rfl) x h
  | cons me rest ih =>
    unfold conflictsOf at ih ⊢
    simp only [List.foldr_cons]
    split
    · rename_i hme
      rw [ih]
      constructor
      · rintro ⟨me', h1, h2⟩; exact ⟨me', List.mem_cons_of_mem _ h1, h2⟩
      · rintro ⟨me', h1, h2, h3⟩
        rcases List.mem_cons.1 h1 with rfl | h1
        · exact absurd hme h2
        · exact ⟨me', h1, h2, h3⟩
    · rename_i hme
      rw [FSet_mem_union_law_holds, ih, FSet.mem_map']
      constructor
      · rintro (⟨p, hp, rfl⟩ | ⟨me', h1, h2⟩)
        · exact ⟨me, List.mem_cons_self, hme, rfl, hp⟩
        · exact ⟨me', List.mem_cons_of_mem _ h1, h2⟩
      · rintro ⟨me', h1, h2, h3, h4⟩
        rcases List.mem_cons.1 h1 with rfl | h1
        · exact Or.inl ⟨x.2, h4, by rw [← h3]⟩
        · exact Or.inr ⟨me', h1, h2, h3, h4⟩

theorem mfPairs_conflictsMF_law_holds : mfPairs_conflictsMF.law := by
  intro mf mgr c
  apply FSet.ext'
  intro x
  rw [mfPairs_mem_iff, mem_conflictsOf]
  unfold conflictsMF
  constructor
  · rintro ⟨me, hme, h1, h2⟩
    obtain ⟨me0, hme0, hf⟩ := List.mem_filterMap.1 hme
    simp only at hf
    split at hf
    · cases hf
    · split at hf
      · cases hf
      · cases hf
        exact ⟨me0, hme0, by assumption, h1, h2⟩
  · rintro ⟨me, hme, h1, h2, h3⟩
    have hne : ¬ (me.2.set.inter (c.modified.union c.added)).IsEmpty := by
      intro hem
      exact (FSet_isEmpty_iff_law_holds _).1 hem x.2 h3
    refine ⟨(me.1, ⟨me.2.set.inter (c.modified.union c.added), me.2.version, false⟩),
      List.mem_filterMap.2 ⟨me, hme, ?_⟩, h2, h3⟩
    simp only [h1, ite_false, hne]

theorem conflictsMF_nil_iff_law_holds : conflictsMF_nil_iff.law := by
  intro mf mgr c
  rw [FSet_isEmpty_iff_law_holds]
  constructor
  · intro h x hx
    rw [← mfPairs_conflictsMF_law_holds, h] at hx
    rw [mfPairs_mem_iff] at hx
    obtain ⟨me, hme, -⟩ := hx
    simp at hme
  · intro h
    apply List.eq_nil_iff_forall_not_mem.2
    intro me hme
    obtain ⟨me0, hme0, hf⟩ := List.mem_filterMap.1 hme
    simp only at hf
    split at hf
    · cases hf
    · split at hf
      · cases hf
      · rename_i h1 h2
        obtain ⟨p, hp⟩ : ∃ p, p ∈ me0.2.set.inter (c.modified.union c.added) :=
          Classical.byContradiction fun hc =>
            h2 ((FSet_isEmpty_iff_law_holds _).2 (fun p hp => hc ⟨p, hp⟩))
        exact h (me0.1, p) ((mem_conflictsOf _ _ _ _).2 ⟨me0, hme0, h1, rfl, hp⟩)

/-- The paths of a manager `k ≠ mgr` in the conflicts: its set's that the change modifies or
adds. -/
theorem mem_conflictsOfMgr (mf : MF) (mgr : GoString) (c : Cmp) (hs : keysSorted mf = true)
    (k : GoString) (e : VSet) (he : mf.get k = some e) (hk : k ≠ mgr) (p : Path) :
    p ∈ conflictsOfMgr (conflictsOf mf mgr c) k ↔ p ∈ e.set.inter (c.modified.union c.added) := by
  unfold conflictsOfMgr
  rw [FSet_mem_bind_law_holds]
  constructor
  · rintro ⟨x, hx, hpx⟩
    split at hpx
    · rename_i hx1
      simp at hpx; subst hpx
      obtain ⟨me, hme, -, h2, h3⟩ := (mem_conflictsOf _ _ _ _).1 hx
      have hget : mf.get me.1 = some me.2 :=
        fpD.mem_lookupKV mf me.1 me.2 (fpD.keysSorted_pairwise mf hs) hme
      rw [← h2, hx1, he] at hget; cases hget; exact h3
    · simp at hpx
  · intro hp
    refine ⟨(k, p), (mem_conflictsOf _ _ _ _).2 ⟨(k, e), fpD.lookupKV_some_mem mf k e he, hk, rfl, hp⟩,
      by simp⟩

theorem mem_take_succ {α : Type} (keys : List α) (j : Int) (key : α) (hj : 0 ≤ j)
    (Hkey : keys[j.toNat]? = some key) (k : α) :
    k ∈ keys.take (j + 1).toNat ↔ k ∈ keys.take j.toNat ∨ k = key := by
  rw [show (j + 1).toNat = j.toNat + 1 by omega, List.take_add_one, Hkey]
  simp

theorem key_notin_take {α : Type} (keys : List α) (j : Int) (key : α) (hnd : keys.Nodup)
    (Hkey : keys[j.toNat]? = some key) : key ∉ keys.take j.toNat := by
  intro hm
  have hk := List.getElem?_eq_some_iff.1 Hkey
  obtain ⟨i, hi, hik⟩ := List.mem_iff_getElem.1 hm
  rw [List.getElem_take] at hik
  have hilt : i < j.toNat := by simp [List.length_take] at hi; omega
  have hi' : keys[i]? = some key := by
    rw [List.getElem?_eq_some_iff]; exact ⟨by have := hk.1; omega, hik⟩
  have := list_nodup_getElem?_inj keys hnd i j.toNat key hi' Hkey
  omega

end MUpd

section iprop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A persistent map whose keys and entries are read through a sorted model is an `isMF`. -/
theorem isMF_of_map (m : fieldpath.ManagedFields) (M : GMap GoString GoInterface) (mf : MF)
    (hs : keysSorted mf = true) (hk : ∀ k, (M !! k).isSome = (mf.get k).isSome) :
    m ↦$□ M ∗ □ (∀ k i e, ⌜M !! k = some i ∧ mf.get k = some e⌝ -∗ isVSet (GF := GF) i e) ⊢
      isMF m mf := by
  iintro ⟨Hm, #H⟩
  unfold isMF
  iexists M
  iframe Hm
  isplitr
  · ipureintro; exact ⟨hs, hk⟩
  iapply fpL.isMFL_intro M mf hk mf hs (fun k e he => he)
  iexact H

end iprop

end smd
end EtcdGrove
end Perennial
