/-
**`Set.Insert`'s and `SetNodeMap.Descend`'s facts**: an owned raw trie's children (`trieOwnC`:
keys, splitting at a node, inserting a node), the binary search's index read over a children
list (`nodesLookup`, `nodesSet`), and the paths and canonical form of a trie after a path is put
in it.

Prove phase (2026-11-20, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsSet
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsPESet
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsCard
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

namespace fpI

/-! ## The binary search's index over a children list -/

abbrev ckeys (cs : List (PE × Trie)) : List PE := cs.map (·.1)

theorem lookup_none (pe : PE) : ∀ (cs : List (PE × Trie)), pe ∉ ckeys cs → nodesLookup pe cs = none
  | [], _ => rfl
  | (e, t) :: cs, h => by
    have h1 : e ≠ pe := fun he => h (by simp [ckeys, he])
    have h2 : pe ∉ ckeys cs := fun hm => h (by simp only [ckeys, List.map_cons, List.mem_cons]; exact Or.inr hm)
    simp only [nodesLookup, h1, ↓reduceIte]
    exact lookup_none pe cs h2

theorem lookup_at (pe : PE) (t : Trie) : ∀ (cs : List (PE × Trie)) (i : Nat),
    (∀ k (hk : k < i), ∀ x, cs[k]? = some x → x.1 ≠ pe) → cs[i]? = some (pe, t) →
    nodesLookup pe cs = some t
  | [], _, _, h => by simp at h
  | (e, t') :: cs, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [nodesLookup]
  | (e, t') :: cs, i + 1, hb, h => by
    have h1 : e ≠ pe := hb 0 (by omega) (e, t') rfl
    simp only [nodesLookup, h1, ↓reduceIte]
    exact lookup_at pe t cs i (fun k hk x hx => hb (k + 1) (by omega) x hx) h

theorem set_at (pe : PE) (t t' : Trie) : ∀ (cs : List (PE × Trie)) (i : Nat),
    (∀ k (hk : k < i), ∀ x, cs[k]? = some x → x.1 ≠ pe ∧ ¬ PE.compare pe x.1 < 0) →
    cs[i]? = some (pe, t) → nodesSet pe t' cs = cs.set i (pe, t')
  | [], _, _, h => by simp at h
  | (e, t0) :: cs, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [nodesSet]
  | (e, t0) :: cs, i + 1, hb, h => by
    obtain ⟨h1, h2⟩ := hb 0 (by omega) (e, t0) rfl
    simp only [nodesSet, h1, h2, ↓reduceIte, List.set_cons_succ]
    rw [set_at pe t t' cs i (fun k hk x hx => hb (k + 1) (by omega) x hx) h]

theorem set_ins (pe : PE) (t' : Trie) : ∀ (cs : List (PE × Trie)) (i : Nat), i ≤ cs.length →
    (∀ k (hk : k < i), ∀ x, cs[k]? = some x → x.1 ≠ pe ∧ ¬ PE.compare pe x.1 < 0) →
    (∀ x, cs[i]? = some x → x.1 ≠ pe ∧ PE.compare pe x.1 < 0) →
    nodesSet pe t' cs = cs.take i ++ (pe, t') :: cs.drop i
  | [], i, hi, _, _ => by
    have : i = 0 := by simp at hi; omega
    subst this; simp [nodesSet]
  | (e, t0) :: cs, 0, _, _, hn => by
    obtain ⟨h1, h2⟩ := hn (e, t0) rfl
    simp [nodesSet, h1, h2]
  | (e, t0) :: cs, i + 1, hi, hb, hn => by
    obtain ⟨h1, h2⟩ := hb 0 (by omega) (e, t0) rfl
    simp only [nodesSet, h1, h2, ↓reduceIte, List.take_succ_cons, List.drop_succ_cons,
      List.cons_append]
    rw [set_ins pe t' cs i (by simp at hi; omega) (fun k hk x hx => hb (k + 1) (by omega) x hx) hn]

/-- **The binary search found `pe` at `i`**. -/
theorem bs_found_cs {cs : List (PE × Trie)} {pe : PE} {i : Nat} (hw : fpA.AllWf (ckeys cs))
    (hp : pe.wf = true) (hb : fpA.BsIdx (ckeys cs) pe i)
    (hf : ∃ x, (ckeys cs)[i]? = some x ∧ PE.compare x pe = 0) :
    ∃ t, cs[i]? = some (pe, t) ∧ nodesLookup pe cs = some t ∧
      ∀ t', nodesSet pe t' cs = cs.set i (pe, t') := by
  obtain ⟨x, hx, hc⟩ := hf
  have hxw : x.wf = true := hw x (List.mem_of_getElem? hx)
  have hxe : x = pe := (PE_compare_eq_zero_law_holds x pe hxw hp).1 hc
  subst hxe
  simp only [ckeys, List.getElem?_map] at hx
  obtain ⟨⟨e, t⟩, hct, he⟩ := Option.map_eq_some_iff.1 hx
  simp only at he; subst he
  have hlt : ∀ k (hk : k < i), ∀ y, cs[k]? = some y → PE.lt y.1 e := fun k hk y hy =>
    (hb.2 k y.1 (by simp [ckeys, List.getElem?_map, hy])).1 hk
  have hyw : ∀ (k : Nat) (y : PE × Trie), cs[k]? = some y → y.1.wf = true := fun k y hy =>
    hw y.1 (by simp only [ckeys, List.mem_map]; exact ⟨y, List.mem_of_getElem? hy, rfl⟩)
  refine ⟨t, hct, lookup_at e t cs i (fun k hk y hy h => ?_) hct, fun t' => set_at e t t' cs i
    (fun k hk y hy => ⟨fun h => ?_, fun h => ?_⟩) hct⟩
  · have := hlt k hk y hy; rw [h] at this; exact fpA.lt_irrefl e hp this
  · have := hlt k hk y hy; rw [h] at this; exact fpA.lt_irrefl e hp this
  · have h1 := hlt k hk y hy
    exact fpA.lt_asymm (hyw k y hy) hp h1 h

/-- **The binary search did not find `pe`**: it goes in at `i`. -/
theorem bs_notfound_cs {cs : List (PE × Trie)} {pe : PE} {i : Nat} (hw : fpA.AllWf (ckeys cs))
    (hp : pe.wf = true) (hs : PE.Sorted (ckeys cs)) (hb : fpA.BsIdx (ckeys cs) pe i)
    (hn : pe ∉ ckeys cs) :
    nodesLookup pe cs = none ∧ ∀ t', nodesSet pe t' cs = cs.take i ++ (pe, t') :: cs.drop i := by
  refine ⟨lookup_none pe cs hn, fun t' => ?_⟩
  have hyw : ∀ (k : Nat) (y : PE × Trie), cs[k]? = some y → y.1.wf = true := fun k y hy =>
    hw y.1 (by simp only [ckeys, List.mem_map]; exact ⟨y, List.mem_of_getElem? hy, rfl⟩)
  have hne : ∀ (k : Nat) (y : PE × Trie), cs[k]? = some y → y.1 ≠ pe := fun k y hy h => hn (by
    simp only [ckeys, List.mem_map]; exact ⟨y, List.mem_of_getElem? hy, h⟩)
  have hkey : ∀ (k : Nat) (y : PE × Trie), cs[k]? = some y → (ckeys cs)[k]? = some y.1 := fun k y hy => by
    simp [ckeys, List.getElem?_map, hy]
  refine set_ins pe t' cs i (by simpa [ckeys] using hb.1) (fun k hk y hy => ⟨hne k y hy, fun h => ?_⟩)
    (fun y hy => ⟨hne i y hy, ?_⟩)
  · exact fpA.lt_asymm (hyw k y hy) hp ((hb.2 k y.1 (hkey k y hy)).1 hk) h
  · have hnl : ¬ PE.lt y.1 pe := fun h => by have := (hb.2 i y.1 (hkey i y hy)).2 h; omega
    rcases fpA.lt_total (hyw i y hy) hp with h | h | h
    · exact absurd h hnl
    · exact absurd h (hne i y hy)
    · exact h

/-! ## A trie with a path put in (`Set.Insert`) -/

theorem lookup_mem (a : PE) : ∀ (cs : List (PE × Trie)) (t : Trie), nodesLookup a cs = some t → (a, t) ∈ cs
  | [], _, h => by simp [nodesLookup] at h
  | (e, t0) :: cs, t, h => by
    unfold nodesLookup at h
    split at h
    · next he => cases h; subst he; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookup_mem a cs t h)

theorem pathsC_head : ∀ (cs : List (PE × Trie)) (x : Path), Trie.pathsC cs x →
    ∃ e r, x = e :: r ∧ e ∈ ckeys cs
  | [], _, h => by simp [Trie.pathsC] at h
  | (e, t) :: cs, x, h => by
    simp only [Trie.pathsC] at h
    rcases h with ⟨r, rfl, -⟩ | h
    · exact ⟨e, r, rfl, by simp [ckeys]⟩
    · obtain ⟨e', r, rfl, hm⟩ := pathsC_head cs x h
      exact ⟨e', r, rfl, by simp only [ckeys, List.map_cons, List.mem_cons]; exact Or.inr hm⟩

theorem pathsC_nokey {cs : List (PE × Trie)} {a : PE} (h : a ∉ ckeys cs) (r : Path) :
    ¬ Trie.pathsC cs (a :: r) := fun hp => by
  obtain ⟨e, r', he, hm⟩ := pathsC_head cs _ hp
  simp only [List.cons.injEq] at he
  rw [he.1] at h; exact h hm

theorem pathsC_cons_key (a : PE) : ∀ (cs : List (PE × Trie)), (ckeys cs).Nodup → ∀ (r : Path),
    Trie.pathsC cs (a :: r) ↔ ∃ t, nodesLookup a cs = some t ∧ Trie.paths t r
  | [], _, r => by simp [Trie.pathsC, nodesLookup]
  | (e, t0) :: cs, hnd, r => by
    simp only [ckeys, List.map_cons, List.nodup_cons] at hnd
    simp only [Trie.pathsC, nodesLookup, List.cons.injEq]
    by_cases he : e = a
    · subst he
      simp only [↓reduceIte, Option.some.injEq, true_and, exists_eq_left', exists_eq_left]
      exact ⟨fun h => h.elim id (fun h => absurd h (pathsC_nokey hnd.1 r)), Or.inl⟩
    · simp only [he, ↓reduceIte]
      rw [pathsC_cons_key a cs hnd.2 r]
      constructor
      · rintro (⟨r', ⟨h1, -⟩, -⟩ | h)
        · exact absurd h1.symm he
        · exact h
      · exact Or.inr

theorem pathsC_cons_key' (a : PE) : ∀ (cs : List (PE × Trie)) (t : Trie) (r : Path),
    nodesLookup a cs = some t → Trie.paths t r → Trie.pathsC cs (a :: r)
  | [], _, _, h, _ => by simp [nodesLookup] at h
  | (e, t0) :: cs, t, r, h, hr => by
    unfold nodesLookup at h
    simp only [Trie.pathsC]
    split at h
    · next he => cases h; subst he; exact Or.inl ⟨r, rfl, hr⟩
    · exact Or.inr (pathsC_cons_key' a cs t r h hr)

theorem keys_nodesSet (a : PE) (t' : Trie) : ∀ (cs : List (PE × Trie)) (k : PE),
    k ∈ ckeys (nodesSet a t' cs) → k ∈ ckeys cs ∨ k = a
  | [], k, h => by simp [nodesSet, ckeys] at h; exact Or.inr h
  | (e, t0) :: cs, k, h => by
    unfold nodesSet at h
    split at h
    · simp only [ckeys, List.map_cons, List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
    · split at h
      · simp only [ckeys, List.map_cons, List.mem_cons] at h ⊢
        rcases h with h | h | h
        · exact Or.inr h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
      · simp only [ckeys, List.map_cons, List.mem_cons] at h ⊢
        rcases h with h | h
        · exact Or.inl (Or.inl h)
        · rcases keys_nodesSet a t' cs k (by simpa [ckeys] using h) with h | h
          · exact Or.inl (Or.inr (by simpa [ckeys] using h))
          · exact Or.inr h

theorem sorted_nodesSet (a : PE) (t' : Trie) (ha : a.wf = true) : ∀ (cs : List (PE × Trie)),
    fpA.AllWf (ckeys cs) → PE.Sorted (ckeys cs) → PE.Sorted (ckeys (nodesSet a t' cs))
  | [], _, _ => by simp [nodesSet, ckeys, PE.Sorted]
  | (e, t0) :: cs, hw, hs => by
    simp only [ckeys, List.map_cons, PE.Sorted, List.pairwise_cons] at hs
    have hew : e.wf = true := hw e (by simp [ckeys])
    have hw' : fpA.AllWf (ckeys cs) := fun x hx => hw x (by simp only [ckeys, List.map_cons, List.mem_cons]; exact Or.inr hx)
    unfold nodesSet
    split
    · next he => subst he; simpa [ckeys, PE.Sorted, List.pairwise_cons] using hs
    · split
      · next he hlt =>
        simp only [ckeys, List.map_cons, PE.Sorted, List.pairwise_cons, List.mem_cons]
        refine ⟨fun k hk => ?_, hs.1, hs.2⟩
        rcases hk with rfl | hk
        · exact hlt
        · exact fpA.lt_trans' ha hew (hw' k (by simpa [ckeys] using hk)) hlt (hs.1 k hk)
      · next he hlt =>
        have hea : PE.lt e a := by
          rcases fpA.lt_total hew ha with h | h | h
          · exact h
          · exact absurd h he
          · exact absurd h hlt
        have ih := sorted_nodesSet a t' ha cs hw' (by simpa [PE.Sorted] using hs.2)
        simp only [ckeys, List.map_cons, PE.Sorted, List.pairwise_cons]
        refine ⟨fun k hk => ?_, by simpa [ckeys, PE.Sorted] using ih⟩
        rcases keys_nodesSet a t' cs k (by simpa [ckeys] using hk) with h | h
        · exact hs.1 k (by simpa [ckeys] using h)
        · rw [h]; exact hea

theorem canonC_nodesSet (a : PE) (t' : Trie) (hc : Trie.Canonical t') (hp : ∃ q, Trie.paths t' q) :
    ∀ (cs : List (PE × Trie)), Trie.CanonicalC cs → Trie.CanonicalC (nodesSet a t' cs)
  | [], _ => by simp only [nodesSet, Trie.CanonicalC]; exact ⟨hc, hp, trivial⟩
  | (e, t0) :: cs, h => by
    simp only [Trie.CanonicalC] at h
    unfold nodesSet
    split
    · simp only [Trie.CanonicalC]; exact ⟨hc, hp, h.2.2⟩
    · split
      · simp only [Trie.CanonicalC]; exact ⟨hc, hp, h⟩
      · simp only [Trie.CanonicalC]; exact ⟨h.1, h.2.1, canonC_nodesSet a t' hc hp cs h.2.2⟩

/-- A sorted list's head is below the rest, so not among them. -/
theorem head_notin {e : PE} {ks : List PE} (hw : e.wf = true) (h : ∀ k ∈ ks, PE.lt e k) : e ∉ ks :=
  fun hm => fpA.lt_irrefl e hw (h e hm)

theorem pathsC_nodesSet (a : PE) (t' : Trie) (ha : a.wf = true) : ∀ (cs : List (PE × Trie)),
    fpA.AllWf (ckeys cs) → PE.Sorted (ckeys cs) → ∀ x,
    Trie.pathsC (nodesSet a t' cs) x ↔
      (∃ r, x = a :: r ∧ Trie.paths t' r) ∨ (Trie.pathsC cs x ∧ ¬ ∃ r, x = a :: r)
  | [], _, _, x => by simp [nodesSet, Trie.pathsC]
  | (e, t0) :: cs, hw, hs, x => by
    simp only [ckeys, List.map_cons, PE.Sorted, List.pairwise_cons] at hs
    have hew : e.wf = true := hw e (by simp [ckeys])
    have hw' : fpA.AllWf (ckeys cs) := fun x hx => hw x (by simp only [ckeys, List.map_cons, List.mem_cons]; exact Or.inr hx)
    have hnot : e ∉ ckeys cs := head_notin hew (fun k hk => hs.1 k (by simpa [ckeys] using hk))
    unfold nodesSet
    split
    · next he =>
      subst he
      simp only [Trie.pathsC]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr h, fun ⟨r, hr⟩ => by subst hr; exact pathsC_nokey hnot r h⟩
      · rintro (h | ⟨h | h, hn⟩)
        · exact Or.inl h
        · exact absurd (let ⟨r, hr, _⟩ := h; ⟨r, hr⟩) hn
        · exact Or.inr h
    · split
      · next he hlt =>
        have hanot : a ∉ ckeys ((e, t0) :: cs) := by
          intro hm
          simp only [ckeys, List.map_cons, List.mem_cons] at hm
          rcases hm with hm | hm
          · exact he hm.symm
          · exact fpA.lt_irrefl a ha (fpA.lt_trans' ha hew (hw' a (by simpa [ckeys] using hm)) hlt
              (hs.1 a (by simpa [ckeys] using hm)))
        simp only [Trie.pathsC]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · refine Or.inr ⟨?_, fun ⟨r, hr⟩ => by subst hr; exact pathsC_nokey hanot r (by simpa [Trie.pathsC] using h)⟩
            simpa [Trie.pathsC] using h
        · rintro (h | ⟨h, -⟩)
          · exact Or.inl h
          · exact Or.inr (by simpa [Trie.pathsC] using h)
      · next he hlt =>
        have ih := pathsC_nodesSet a t' ha cs hw' (by simpa [PE.Sorted] using hs.2) x
        simp only [Trie.pathsC]
        rw [ih]
        constructor
        · rintro (⟨r, rfl, h⟩ | h | h)
          · exact Or.inr ⟨Or.inl ⟨r, rfl, h⟩, fun ⟨r', hr'⟩ => he (List.cons.inj hr').1⟩
          · exact Or.inl h
          · exact Or.inr ⟨Or.inr h.1, h.2⟩
        · rintro (h | ⟨h | h, hn⟩)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr ⟨h, hn⟩)

/-- **One descent's step**: the child at `a` replaced by `tq'`, which has the child's paths and
`rest`; the trie has its paths and `a :: rest`. -/
theorem descend_step {ms : List PE} {cs : List (PE × Trie)} {a : PE} {tch tq' : Trie} {rest : Path}
    (hcan : Trie.Canonical (.mk ms cs)) (hw : fpA.AllWf (ckeys cs)) (ha : a.wf = true)
    (hlk : nodesLookup a cs = some tch ∨ (nodesLookup a cs = none ∧ tch = Trie.empty))
    (hc' : Trie.Canonical tq') (hp' : ∀ x, Trie.paths tq' x ↔ Trie.paths tch x ∨ x = rest) :
    Trie.Canonical (.mk ms (nodesSet a tq' cs)) ∧
      ∀ x, Trie.paths (.mk ms (nodesSet a tq' cs)) x ↔ Trie.paths (.mk ms cs) x ∨ x = a :: rest := by
  obtain ⟨hms, hks, hcc⟩ := hcan
  have hs : PE.Sorted (ckeys cs) := hks
  have hnd : (ckeys cs).Nodup := fpA.sorted_nodup _ hw hs
  have hcol : ∀ r, Trie.pathsC cs (a :: r) ↔ Trie.paths tch r := fun r => by
    rw [pathsC_cons_key a cs hnd r]
    rcases hlk with h | ⟨h, rfl⟩
    · rw [h]; simp
    · rw [h]; simp [Trie.empty, Trie.paths, Trie.pathsC]
  refine ⟨⟨hms, sorted_nodesSet a tq' ha cs hw hs, canonC_nodesSet a tq' hc' ⟨rest, (hp' rest).2 (Or.inr rfl)⟩ cs hcc⟩,
    fun x => ?_⟩
  rw [fpC.paths_mk, fpC.paths_mk, pathsC_nodesSet a tq' ha cs hw hs x]
  by_cases hx : ∃ r, x = a :: r
  · obtain ⟨r, rfl⟩ := hx
    rw [hcol r]
    simp only [List.cons.injEq, true_and, exists_eq_left', hp']
    constructor
    · rintro (⟨e, h, hm⟩ | h | ⟨-, h⟩)
      · exact Or.inl (Or.inl ⟨e, h, hm⟩)
      · rcases h with h | rfl
        · exact Or.inl (Or.inr h)
        · exact Or.inr rfl
      · exact absurd ⟨r, rfl⟩ h
    · rintro ((⟨e, h, hm⟩ | h) | rfl)
      · exact Or.inl ⟨e, h, hm⟩
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr rfl))
  · constructor
    · rintro (h | ⟨r, rfl, -⟩ | ⟨h, -⟩)
      · exact Or.inl (Or.inl h)
      · exact absurd ⟨r, rfl⟩ hx
      · exact Or.inl (Or.inr h)
    · rintro ((h | h) | rfl)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨h, hx⟩)
      · exact absurd ⟨rest, rfl⟩ hx

/-- **The last element**: put in the members. -/
theorem members_step {ms ms' : List PE} {cs : List (PE × Trie)} {a : PE}
    (hcan : Trie.Canonical (.mk ms cs)) (hs' : PE.Sorted ms')
    (hm : FSet.ofList ms' = FSet.union (FSet.ofList ms) (FSet.ofList [a])) :
    Trie.Canonical (.mk ms' cs) ∧
      ∀ x, Trie.paths (.mk ms' cs) x ↔ Trie.paths (.mk ms cs) x ∨ x = [a] := by
  obtain ⟨-, hks, hcc⟩ := hcan
  refine ⟨⟨hs', hks, hcc⟩, fun x => ?_⟩
  have hmem : ∀ e, e ∈ ms' ↔ e ∈ ms ∨ e = a := fun e => by
    rw [← FSet.mem_ofList', hm, FSet.mem_union', FSet.mem_ofList', FSet.mem_ofList', List.mem_singleton]
  rw [fpC.paths_mk, fpC.paths_mk]
  simp only [hmem]
  constructor
  · rintro (⟨e, rfl, h | rfl⟩ | h)
    · exact Or.inl (Or.inl ⟨e, rfl, h⟩)
    · exact Or.inr rfl
    · exact Or.inl (Or.inr h)
  · rintro ((⟨e, rfl, h⟩ | h) | rfl)
    · exact Or.inl ⟨e, rfl, Or.inl h⟩
    · exact Or.inr h
    · exact Or.inl ⟨a, rfl, Or.inr rfl⟩

/-- Members given back with the same elements, sorted. -/
theorem members_congr {ms ms' : List PE} {cs : List (PE × Trie)}
    (hcan : Trie.Canonical (.mk ms cs)) (hs' : PE.Sorted ms') (hm : FSet.ofList ms' = FSet.ofList ms) :
    Trie.Canonical (.mk ms' cs) ∧ ∀ x, Trie.paths (.mk ms' cs) x ↔ Trie.paths (.mk ms cs) x := by
  obtain ⟨-, hks, hcc⟩ := hcan
  refine ⟨⟨hs', hks, hcc⟩, fun x => ?_⟩
  have hmem : ∀ e, e ∈ ms' ↔ e ∈ ms := fun e => by rw [← FSet.mem_ofList', hm, FSet.mem_ofList']
  rw [fpC.paths_mk, fpC.paths_mk]
  simp only [hmem]

theorem canon_empty : Trie.Canonical Trie.empty := ⟨List.Pairwise.nil, List.Pairwise.nil, trivial⟩

theorem paths_empty (x : Path) : ¬ Trie.paths Trie.empty x := by
  simp [Trie.empty, Trie.paths, Trie.pathsC]

theorem tset_empty_card : (fpC.tset Trie.empty).card = 0 := rfl

/-! ### Counts below a trie's -/

theorem card_members (ms : List PE) (cs : List (PE × Trie)) :
    (FSet.ofList ms).card ≤ (fpC.tset (.mk ms cs)).card := by
  rw [← fpK.card_map_inj (fun e : PE => [e]) (fun a b h => List.cons.inj h |>.1) (FSet.ofList ms)]
  apply FSet.card_le_of_subset
  intro x hx
  rw [FSet.mem_map'] at hx
  obtain ⟨e, he, rfl⟩ := hx
  rw [fpC.mem_tset, fpC.paths_mk]
  exact Or.inl ⟨e, rfl, (FSet.mem_ofList' _ _).1 he⟩

theorem card_child (ms : List PE) (cs : List (PE × Trie)) (a : PE) (t : Trie)
    (h : nodesLookup a cs = some t) : (fpC.tset t).card ≤ (fpC.tset (.mk ms cs)).card := by
  rw [← fpK.card_cons_map a (fpC.tset t)]
  apply FSet.card_le_of_subset
  intro x hx
  rw [FSet.mem_map'] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  rw [fpC.mem_tset] at hr ⊢
  rw [fpC.paths_mk]
  refine Or.inr ?_
  exact pathsC_cons_key' a cs t r h hr

/-- The set of the paths below a list of children. -/
def tsetC (cs : List (PE × Trie)) : PathSet := FSet.ofList (fpC.pathListC cs)

theorem mem_tsetC (cs : List (PE × Trie)) (q : Path) : q ∈ tsetC cs ↔ Trie.pathsC cs q := by
  unfold tsetC; rw [FSet.mem_ofList', fpC.mem_pathListC]

theorem card_pos {S : PathSet} {q : Path} (h : q ∈ S) : 1 ≤ S.card := by
  have : (FSet.ofList [q]).card ≤ S.card := FSet.card_le_of_subset _ _ (fun x hx => by
    rw [FSet.mem_ofList', List.mem_singleton] at hx; subst hx; exact h)
  have h1 : (FSet.ofList [q]).card = 1 := rfl
  omega

theorem card_childrenC : ∀ (cs : List (PE × Trie)), fpA.AllWf (ckeys cs) → PE.Sorted (ckeys cs) →
    Trie.CanonicalC cs → cs.length ≤ (tsetC cs).card
  | [], _, _, _ => by simp
  | (e, t) :: cs, hw, hs, hc => by
    simp only [ckeys, List.map_cons, PE.Sorted, List.pairwise_cons] at hs
    simp only [Trie.CanonicalC] at hc
    have hew : e.wf = true := hw e (by simp [ckeys])
    have hw' : fpA.AllWf (ckeys cs) := fun x hx => hw x (by simp only [ckeys, List.map_cons, List.mem_cons]; exact Or.inr hx)
    have hnot : e ∉ ckeys cs := head_notin hew (fun k hk => hs.1 k (by simpa [ckeys] using hk))
    have ih := card_childrenC cs hw' (by simpa [PE.Sorted] using hs.2) hc.2.2
    obtain ⟨q, hq⟩ := hc.2.1
    have h1 : 1 ≤ (fpC.tset t).card := card_pos ((fpC.mem_tset t q).2 hq)
    have e1 : (tsetC ((e, t) :: cs)).card = (FSet.map (e :: ·) (fpC.tset t)).card + (tsetC cs).card := by
      apply fpK.card_disj
      · intro x
        rw [mem_tsetC, mem_tsetC, FSet.mem_map']
        simp only [Trie.pathsC, fpC.mem_tset]
        constructor
        · rintro (⟨r, rfl, h⟩ | h)
          · exact Or.inl ⟨r, h, rfl⟩
          · exact Or.inr h
        · rintro (⟨r, h, rfl⟩ | h)
          · exact Or.inl ⟨r, rfl, h⟩
          · exact Or.inr h
      · intro x hx hy
        rw [FSet.mem_map'] at hx
        obtain ⟨r, -, rfl⟩ := hx
        exact pathsC_nokey hnot r ((mem_tsetC cs _).1 hy)
    rw [e1, fpK.card_cons_map]
    simp only [List.length_cons]
    omega

theorem card_children (ms : List PE) (cs : List (PE × Trie)) (hcan : Trie.Canonical (.mk ms cs))
    (hw : fpA.AllWf (ckeys cs)) : cs.length ≤ (fpC.tset (.mk ms cs)).card := by
  obtain ⟨-, hks, hcc⟩ := hcan
  refine Nat.le_trans (card_childrenC cs hw hks hcc) (FSet.card_le_of_subset _ _ (fun x hx => ?_))
  rw [mem_tsetC] at hx
  rw [fpC.mem_tset, fpC.paths_mk]
  exact Or.inr hx

end fpI

namespace fpI

/-! ## An owned raw trie's children -/

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem trieOwnC_nil_eq : trieOwnC (GF := GF) [] [] = iprop(True) := by simp only [trieOwnC]

theorem trieOwnC_cons_eq (n : fieldpath.setNode) (ns : List fieldpath.setNode) (pe : PE) (t : Trie)
    (cs : List (PE × Trie)) :
    trieOwnC (GF := GF) (n :: ns) ((pe, t) :: cs) =
      iprop(isPE n.pathElement' pe ∗ trieOwn n.set' t ∗ trieOwnC ns cs) := by
  simp only [trieOwnC]

theorem trieOwnC_keys : ∀ (ns : List fieldpath.setNode) (cs : List (PE × Trie)),
    trieOwnC (GF := GF) ns cs ⊢
      isPEL (ns.map (·.pathElement')) (ckeys cs) ∗ trieOwnC ns cs
  | [], [] => by
    rw [trieOwnC_nil_eq]; iintro -
    simp only [List.map_nil, ckeys]; rw [fpL.isPEL_nil_eq]; iframe; isplit <;> itrivial
  | [], _ :: _ => by unfold trieOwnC; iintro %h; exact h.elim
  | _ :: _, [] => by unfold trieOwnC; iintro %h; exact h.elim
  | n :: ns, (pe, t) :: cs => by
    rw [trieOwnC_cons_eq]
    iintro ⟨#Hpe, Ht, Hc⟩
    icases trieOwnC_keys ns cs $$ Hc with ⟨#Hk, Hc⟩
    simp only [List.map_cons, ckeys]
    rw [fpL.isPEL_cons_eq]
    iframe
    iframe #

theorem trieOwnC_app : ∀ (a b : List fieldpath.setNode) (c d : List (PE × Trie)), a.length = c.length →
    trieOwnC (GF := GF) (a ++ b) (c ++ d) ⊣⊢ trieOwnC a c ∗ trieOwnC b d
  | [], b, [], d, _ => by
    simp only [List.nil_append]; rw [trieOwnC_nil_eq]
    exact ⟨by iintro H; iframe, by iintro ⟨-, H⟩; iexact H⟩
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | n :: a, b, (pe, t) :: c, d, h => by
    simp only [List.cons_append]
    rw [trieOwnC_cons_eq, trieOwnC_cons_eq]
    have ih := trieOwnC_app a b c d (by simpa using h)
    constructor
    · iintro ⟨Hpe, Ht, H⟩
      icases ih.1 $$ H with ⟨H1, H2⟩
      iframe
    · iintro ⟨⟨Hpe, Ht, H1⟩, H2⟩
      iframe
      iapply ih.2; iframe

/-- The node at `i`, and the way back with any trie in its place. -/
theorem trieOwnC_at (ns : List fieldpath.setNode) (cs : List (PE × Trie)) (i : Nat)
    (n : fieldpath.setNode) (pe : PE) (t : Trie) (hn : ns[i]? = some n) (hc : cs[i]? = some (pe, t)) :
    trieOwnC (GF := GF) ns cs ⊢
      trieOwn n.set' t ∗ (∀ t', trieOwn n.set' t' -∗ trieOwnC ns (cs.set i (pe, t'))) := by
  have hi : i < ns.length := (List.getElem?_eq_some_iff.1 hn).1
  have hi' : i < cs.length := (List.getElem?_eq_some_iff.1 hc).1
  have hn' : ns[i] = n := by rw [List.getElem?_eq_getElem hi] at hn; exact Option.some.inj hn
  have hc' : cs[i] = (pe, t) := by rw [List.getElem?_eq_getElem hi'] at hc; exact Option.some.inj hc
  have en : ns = ns.take i ++ n :: ns.drop (i + 1) := by
    rw [← hn', ← fpA.drop_cons' ns i hi, List.take_append_drop]
  have ec : cs = cs.take i ++ (pe, t) :: cs.drop (i + 1) := by
    rw [← hc', ← fpA.drop_cons' cs i hi', List.take_append_drop]
  have hl : (ns.take i).length = (cs.take i).length := by simp; omega
  have hl2 : (cs.take i).length = i := by simp; omega
  generalize ns.take i = a, ns.drop (i + 1) = b, cs.take i = c, cs.drop (i + 1) = d at en ec hl hl2
  subst en ec
  have e2 : ∀ t', (c ++ (pe, t) :: d).set i (pe, t') = c ++ (pe, t') :: d := fun t' => by
    rw [List.set_append_right _ _ (by omega), hl2, Nat.sub_self]; rfl
  iintro H
  icases (trieOwnC_app _ _ _ _ hl).1 $$ H with ⟨H1, H2⟩
  rw [trieOwnC_cons_eq]
  icases H2 with ⟨#Hpe, Ht, H3⟩
  iframe Ht
  iintro %t' Ht'
  rw [e2 t']
  iapply (trieOwnC_app _ _ _ _ hl).2
  iframe H1
  rw [trieOwnC_cons_eq]
  iframe
  iframe #

theorem trieOwnC_length (ns : List fieldpath.setNode) (cs : List (PE × Trie)) :
    trieOwnC (GF := GF) ns cs ⊢ ⌜ns.length = cs.length⌝ ∗ trieOwnC ns cs := by
  iintro H
  icases trieOwnC_keys ns cs $$ H with ⟨#Hk, H⟩
  ihave %hl := fpL.isPEL_length $$ Hk
  iframe
  ipureintro; simpa [ckeys] using hl

/-- A new node put in at `i`. -/
theorem trieOwnC_ins (ns : List fieldpath.setNode) (cs : List (PE × Trie)) (i : Nat)
    (n : fieldpath.setNode) (pe : PE) (t : Trie) :
    trieOwnC (GF := GF) ns cs ∗ isPE n.pathElement' pe ∗ trieOwn n.set' t ⊢
      trieOwnC (ns.take i ++ n :: ns.drop i) (cs.take i ++ (pe, t) :: cs.drop i) := by
  iintro ⟨H, #Hpe, Ht⟩
  icases trieOwnC_length ns cs $$ H with ⟨%hl, H⟩
  have hl' : (ns.take i).length = (cs.take i).length := by simp [hl]
  have e : trieOwnC (GF := GF) ns cs = trieOwnC (ns.take i ++ ns.drop i) (cs.take i ++ cs.drop i) := by
    rw [List.take_append_drop, List.take_append_drop]
  rw [e]
  icases (trieOwnC_app _ _ _ _ hl').1 $$ H with ⟨H1, H2⟩
  iapply (trieOwnC_app _ _ _ _ hl').2
  iframe H1
  rw [trieOwnC_cons_eq]
  iframe
  iframe #

/-- A `setNode`'s two fields, and the way back. -/
theorem setnode_fields (l : Loc) (v : fieldpath.setNode) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊢
      l.[fieldpath.setNode, go!"pathElement"] ↦{dq} v.pathElement' ∗
      l.[fieldpath.setNode, go!"set"] ↦{dq} v.set' ∗
      (l.[fieldpath.setNode, go!"pathElement"] ↦{dq} v.pathElement' -∗
        l.[fieldpath.setNode, go!"set"] ↦{dq} v.set' -∗ l ↦{dq} v) := by
  iintro Hl
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %hn⟩
  iStructNamed Hl
  iframe pathElement set
  iintro Ha Hb
  iapply typedPointsto_combine _ _ _ hn
  simp only [TypedPointsto.typedPointstoDef]
  iframe Ha Hb

/-- A `SetNodeMap`'s one field, and the way back with any new value. -/
theorem nodemap_members_upd (l : Loc) (v : fieldpath.SetNodeMap) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊢ l.[fieldpath.SetNodeMap, go!"members"] ↦{dq} v.members' ∗
      (∀ w, l.[fieldpath.SetNodeMap, go!"members"] ↦{dq} w -∗
        l ↦{dq} ({ members' := w } : fieldpath.SetNodeMap)) := by
  iintro Hl
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %hn⟩
  iStructNamed Hl
  iframe members
  iintro %w Hm
  iapply typedPointsto_combine _ _ _ hn
  simp only [TypedPointsto.typedPointstoDef]
  iframe Hm

/-- `&Set{}`: the empty trie, owned. -/
theorem trieOwn_empty (p : Loc) : (p ↦ zero_val fieldpath.Set' : IProp GF) ⊢ trieOwn p Trie.empty := by
  iintro Hp
  unfold Trie.empty
  rw [trieOwn.eq_1]
  iexists (zero_val fieldpath.Set'), [], []
  have h1 : (zero_val fieldpath.Set').Members'.members' = slice.nil := rfl
  have h2 : (zero_val fieldpath.Set').Children'.members' = slice.nil := rfl
  rw [h1, h2, isPEL.eq_1, trieOwnC.eq_1]
  iframe
  ihave Hn1 := ownSlice_nil (V := fieldpath.PathElement) (GF := GF) (DFrac.own 1)
  ihave Hn2 := ownSlice_nil (V := fieldpath.setNode) (GF := GF) (DFrac.own 1)
  ihave Hc1 := ownSliceCap_nil (V := fieldpath.PathElement) (GF := GF)
  ihave Hc2 := ownSliceCap_nil (V := fieldpath.setNode) (GF := GF)
  iframe #

/-- A `Set`'s two fields, and the way back with any new values. -/
theorem set_fields (c : Loc) (v : fieldpath.Set') :
    (c ↦ v : IProp GF) ⊢
      c.[fieldpath.Set', go!"Members"] ↦ v.Members' ∗
      c.[fieldpath.Set', go!"Children"] ↦ v.Children' ∗
      (∀ a b, c.[fieldpath.Set', go!"Members"] ↦ a -∗
        c.[fieldpath.Set', go!"Children"] ↦ b -∗
        c ↦ ({ Members' := a, Children' := b } : fieldpath.Set')) := by
  iintro Hl
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %hn⟩
  iStructNamed Hl
  iframe Members Children
  iintro %a %b Ha Hb
  iapply typedPointsto_combine _ _ _ hn
  simp only [TypedPointsto.typedPointstoDef]
  iframe Ha Hb

/-- **An owned trie opened**: its members as an owned `PathElementSet`, its children as an owned
`SetNodeMap`, and the way back with new ones. -/
theorem trieOwn_open (c : Loc) (ms : List PE) (cs : List (PE × Trie)) (hs : PE.Sorted ms) :
    trieOwn (GF := GF) c (.mk ms cs) ⊢
      ⌜fpA.AllWf (ckeys cs)⌝ ∗
      ownPESet (c.[fieldpath.Set', go!"Members"]) (FSet.ofList ms) ∗
      ownNodesT (c.[fieldpath.Set', go!"Children"]) cs ∗
      (∀ M cs', ownPESet (c.[fieldpath.Set', go!"Members"]) M -∗
        ownNodesT (c.[fieldpath.Set', go!"Children"]) cs' -∗
        ∃ ms', ⌜PE.Sorted ms' ∧ FSet.ofList ms' = M⌝ ∗ trieOwn c (.mk ms' cs')) := by
  rw [trieOwn.eq_1]
  iintro ⟨%v, %es, %ns, Hc, Hes, Hcap1, #Hpel, Hns, Hcap2, Hcc⟩
  icases set_fields c v $$ Hc with ⟨Hm, Hch, Hback⟩
  icases trieOwnC_keys ns cs $$ Hcc with ⟨#Hk, Hcc⟩
  ihave %hw := fpL.isPEL_wf $$ Hk
  isplitr
  · ipureintro; exact hw
  isplitl [Hm Hes Hcap1]
  · unfold ownPESet ownPESetV
    iexists v.Members'
    isplitl [Hm]
    · iexact Hm
    iexists es, ms
    iframe
    iframe #
    ipureintro; exact ⟨hs, rfl⟩
  isplitl [Hch Hns Hcap2 Hcc]
  · unfold ownNodesT
    iexists v.Children', ns
    iframe
  iintro %M %cs' HM HN
  unfold ownPESet ownPESetV ownNodesT
  icases HM with ⟨%v1, Hm1, %es1, %xs1, Hes1, Hc1, #Hx1, %hx1⟩
  icases HN with ⟨%m2, %ns2, Hm2, Hns2, Hc2, Hcc2⟩
  iexists xs1
  isplitr
  · ipureintro; exact hx1
  rw [trieOwn.eq_1]
  ihave Hc := Hback $$ Hm1 Hm2
  iexists { Members' := v1, Children' := m2 }, es1, ns2
  iframe
  iexact Hx1

end own

end fpI

end smd
end EtcdGrove
end Perennial
