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

/-! ## Lists -/

theorem take_succ_of {α : Type} {l : List α} {k : Nat} {x : α} (h : l[k]? = some x) :
    l.take (k + 1) = l.take k ++ [x] := by
  rw [List.take_add_one, h]; rfl

theorem not_mem_take_of_nodup {α : Type} {l : List α} {k : Nat} {x : α} (hnd : l.Nodup)
    (h : l[k]? = some x) : x ∉ l.take k := by
  intro hx
  have hd : x ∈ l.drop k := by
    rw [List.mem_iff_getElem?]; exact ⟨0, by simp [h]⟩
  rw [← List.take_append_drop k l, List.nodup_append] at hnd
  exact hnd.2.2 x hx x hd rfl

/-! ## `iteratePrefix`'s paths done, child by child -/

/-- The paths done after the children of keys `keys.take k`. -/
def DoneK (pre : Path) (D : PathSet) (keys : List PE) (k : Nat) (ds : List Path) : Prop :=
  ds.Nodup ∧ ∀ x, x ∈ ds ↔ ∃ q, x = pre ++ q ∧ q ∈ D ∧ ∃ e, e ∈ keys.take k ∧ q.head? = some e

theorem doneK_zero (pre : Path) (D : PathSet) (keys : List PE) : DoneK pre D keys 0 [] := by
  refine ⟨List.nodup_nil, fun x => ?_⟩
  simp

theorem doneK_not_mem {pre : Path} {D : PathSet} {keys : List PE} {k : Nat} {ds : List Path}
    (h : DoneK pre D keys k ds) {e : PE} (hnd : keys.Nodup) (hkx : keys[k]? = some e) (r : Path) :
    pre ++ e :: r ∉ ds := by
  intro hx
  obtain ⟨q, hq, -, e', he', hh⟩ := (h.2 _).1 hx
  have := List.append_cancel_left hq
  subst this
  simp at hh; subst hh
  exact not_mem_take_of_nodup hnd hkx he'

theorem doneK_step {pre : Path} {D : PathSet} {keys : List PE} {k : Nat} {dsk dsc : List Path}
    {e : PE} (hnd : keys.Nodup) (hkx : keys[k]? = some e)
    (hD : ∀ q ∈ D, ∃ e r, q = e :: r ∧ r ≠ [])
    (h : DoneK pre D keys k dsk)
    (hc : dsc.Nodup ∧ FSet.ofList dsc = PathSet.prepend (pre ++ [e]) (D.under e)) :
    DoneK pre D keys (k + 1) (dsk ++ dsc) := by
  have hmc : ∀ x, x ∈ dsc ↔ ∃ r, r ≠ [] ∧ e :: r ∈ D ∧ x = pre ++ e :: r := by
    intro x
    have hu : ∀ (S : PathSet) e q, q ∈ S.under e ↔ q ≠ [] ∧ (e :: q) ∈ S :=
      PathSet_mem_under_law_holds
    rw [← FSet.mem_ofList', hc.2, PathSet_mem_prepend_law_holds]
    simp only [hu, List.append_assoc, List.singleton_append]
    constructor
    · rintro ⟨r, ⟨h1, h2⟩, h3⟩; exact ⟨r, h1, h2, h3⟩
    · rintro ⟨r, h1, h2, h3⟩; exact ⟨r, ⟨h1, h2⟩, h3⟩
  refine ⟨?_, fun x => ?_⟩
  · rw [List.nodup_append]
    refine ⟨h.1, hc.1, fun a ha b hb hab => ?_⟩
    subst hab
    obtain ⟨r, -, -, rfl⟩ := (hmc a).1 hb
    exact doneK_not_mem h hnd hkx r ha
  · rw [List.mem_append, h.2, hmc, take_succ_of hkx]
    constructor
    · rintro (⟨q, h1, h2, e', h3, h4⟩ | ⟨r, -, h2, h3⟩)
      · exact ⟨q, h1, h2, e', List.mem_append_left _ h3, h4⟩
      · exact ⟨e :: r, h3, h2, e, by simp, rfl⟩
    · rintro ⟨q, h1, h2, e', h3, h4⟩
      rcases List.mem_append.1 h3 with h3 | h3
      · exact Or.inl ⟨q, h1, h2, e', h3, h4⟩
      · simp at h3; subst h3
        obtain ⟨e'', r, rfl, hr⟩ := hD q h2
        simp at h4; subst h4
        exact Or.inr ⟨r, hr, h2, h1⟩

theorem doneK_all {pre : Path} {D : PathSet} {keys : List PE} {ds : List Path}
    (hD : ∀ q ∈ D, ∃ e, e ∈ keys ∧ q.head? = some e)
    (h : DoneK pre D keys keys.length ds) :
    ds.Nodup ∧ FSet.ofList ds = PathSet.prepend pre D := by
  refine ⟨h.1, FSet.ext' (fun x => ?_)⟩
  rw [FSet.mem_ofList', h.2, PathSet_mem_prepend_law_holds, List.take_length]
  constructor
  · rintro ⟨q, h1, h2, -⟩; exact ⟨q, h2, h1⟩
  · rintro ⟨q, h2, h1⟩; exact ⟨q, h1, h2, hD q h2⟩

/-! ## A set's children (`SetNodeMap`) -/

theorem paths_ne : ∀ (t : Trie) (q : Path), Trie.paths t q → q ≠ []
  | .mk ms cs, q, h => by
    simp only [Trie.paths] at h
    rcases h with ⟨e, rfl, -⟩ | h
    · simp
    · exact pathsC_ne cs q h
where pathsC_ne : ∀ (cs : List (PE × Trie)) (q : Path), Trie.pathsC cs q → q ≠ []
  | [], q, h => by simp [Trie.pathsC] at h
  | (e, t) :: cs, q, h => by
    simp only [Trie.pathsC] at h
    rcases h with ⟨r, rfl, -⟩ | h
    · simp
    · exact pathsC_ne cs q h

theorem pathsC_iff : ∀ (cs : List (PE × Trie)) (q : Path),
    Trie.pathsC cs q ↔ ∃ e t r, (e, t) ∈ cs ∧ q = e :: r ∧ Trie.paths t r
  | [], q => by simp [Trie.pathsC]
  | (e, t) :: cs, q => by
    simp only [Trie.pathsC, pathsC_iff cs q, List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro (⟨r, rfl, h⟩ | ⟨e', t', r, h1, h2, h3⟩)
      · exact ⟨e, t, r, Or.inl ⟨rfl, rfl⟩, rfl, h⟩
      · exact ⟨e', t', r, Or.inr h1, h2, h3⟩
    · rintro ⟨e', t', r, (⟨rfl, rfl⟩ | h1), h2, h3⟩
      · exact Or.inl ⟨r, h2, h3⟩
      · exact Or.inr ⟨e', t', r, h1, h2, h3⟩

/-- Every child of a canonical children list has a path. -/
theorem canonicalC_mem : ∀ (cs : List (PE × Trie)), Trie.CanonicalC cs →
    ∀ e t, (e, t) ∈ cs → Trie.Canonical t ∧ ∃ q, Trie.paths t q
  | [], _, _, _, h => by simp at h
  | (e', t') :: cs, h, e, t, hm => by
    simp only [Trie.CanonicalC] at h
    rcases List.mem_cons.1 hm with he | hm
    · cases he; exact ⟨h.1, h.2.1⟩
    · exact canonicalC_mem cs h.2.2 e t hm

theorem heads_iff (cs : List (PE × Trie)) (D : PathSet) (hc : Trie.CanonicalC cs)
    (hD : ∀ q, Trie.pathsC cs q ↔ q ∈ D) (e : PE) :
    e ∈ D.heads ↔ e ∈ cs.map Prod.fst := by
  rw [PathSet_mem_heads_law_holds]
  constructor
  · rintro ⟨q, hq, h⟩
    obtain ⟨e', t, r, hm, he, -⟩ := (pathsC_iff cs _).1 ((hD _).2 h)
    cases he
    exact List.mem_map.2 ⟨(e, t), hm, rfl⟩
  · intro h
    obtain ⟨⟨e', t⟩, hm, rfl⟩ := List.mem_map.1 h
    obtain ⟨-, r, hr⟩ := canonicalC_mem cs hc e' t hm
    exact ⟨r, paths_ne t r hr, (hD _).1 ((pathsC_iff cs _).2 ⟨e', t, r, hm, rfl, hr⟩)⟩

theorem mem_unique {β : Type} : ∀ (cs : List (PE × β)), (cs.map Prod.fst).Nodup →
    ∀ e t t', (e, t) ∈ cs → (e, t') ∈ cs → t = t'
  | [], _, _, _, _, h, _ => by simp at h
  | c :: cs, hnd, e, t, t', hm, hm' => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hm with h1 | h1 <;> rcases List.mem_cons.1 hm' with h2 | h2
    · rw [← h1] at h2; cases h2; rfl
    · subst h1; exact absurd (List.mem_map.2 ⟨_, h2, rfl⟩) hnd.1
    · subst h2; exact absurd (List.mem_map.2 ⟨_, h1, rfl⟩) hnd.1
    · exact mem_unique cs hnd.2 e t t' h1 h2

/-- Strictly sorted well-formed elements are distinct. -/
theorem sorted_nodup (xs : List PE) (hw : ∀ x ∈ xs, x.wf = true) (hs : PE.Sorted xs) : xs.Nodup :=
  List.Pairwise.imp_of_mem (fun {a b} ha _ hab e => by
    subst e
    have := (PE_compare_eq_zero_law_holds a a (hw a ha) (hw a ha)).2 rfl
    unfold PE.lt at hab; omega) hs

theorem nodes_mem (cs : List (PE × Trie)) (D : PathSet) (hD : ∀ q, Trie.pathsC cs q ↔ q ∈ D)
    (q : Path) (hq : q ∈ D) : ∃ e t r, (e, t) ∈ cs ∧ q = e :: r ∧ r ≠ [] ∧ Trie.paths t r := by
  obtain ⟨e, t, r, hm, rfl, h⟩ := (pathsC_iff cs q).1 ((hD q).2 hq)
  exact ⟨e, t, r, hm, rfl, paths_ne t r h, h⟩

/-- A child's paths are the paths below its key (keys distinct). -/
theorem under_iff (cs : List (PE × Trie)) (D : PathSet)
    (hnd : (cs.map Prod.fst).Nodup) (hD : ∀ q, Trie.pathsC cs q ↔ q ∈ D)
    (e : PE) (t : Trie) (hm : (e, t) ∈ cs) (r : Path) :
    Trie.paths t r ↔ r ∈ D.under e := by
  rw [PathSet_mem_under_law_holds, ← hD, pathsC_iff]
  constructor
  · intro h; exact ⟨paths_ne t r h, e, t, r, hm, rfl, h⟩
  · rintro ⟨-, e', t', r', hm', he, h⟩
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have : t = t' := mem_unique cs hnd e t t' hm hm'
    subst this; exact h

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

theorem trieRepC_nil_eq : trieRepC (GF := GF) [] [] = iprop(True) := by simp only [trieRepC]

theorem trieRepC_cons_eq (n : fieldpath.setNode) (ns : List fieldpath.setNode) (pe : PE) (t : Trie)
    (cs : List (PE × Trie)) :
    trieRepC (GF := GF) (n :: ns) ((pe, t) :: cs) =
      iprop(isPE n.pathElement' pe ∗ trieRep n.set' t ∗ trieRepC ns cs) := by
  simp only [trieRepC]

theorem trieRepC_length : ∀ (ns : List fieldpath.setNode) (cs : List (PE × Trie)),
    trieRepC (GF := GF) ns cs ⊢ ⌜ns.length = cs.length⌝
  | [], [] => by iintro _; ipureintro; rfl
  | [], _ :: _ => by unfold trieRepC; iintro %h; exact h.elim
  | _ :: _, [] => by unfold trieRepC; iintro %h; exact h.elim
  | n :: ns, (pe, t) :: cs => by
    rw [trieRepC_cons_eq]; iintro ⟨-, -, H⟩
    ihave %h := trieRepC_length ns cs $$ H
    ipureintro; simp [h]

theorem trieRepC_lookup : ∀ (ns : List fieldpath.setNode) (cs : List (PE × Trie)) (k : Nat)
    (n : fieldpath.setNode), ns[k]? = some n →
    trieRepC (GF := GF) ns cs ⊢ ∃ c, ⌜cs[k]? = some c⌝ ∗ isPE n.pathElement' c.1 ∗ trieRep n.set' c.2
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, _ => by unfold trieRepC; iintro %h; exact h.elim
  | n' :: ns, (pe, t) :: cs, 0, n, h => by
    simp at h; subst h
    rw [trieRepC_cons_eq]; iintro ⟨#He, #Ht, -⟩
    iexists (pe, t); isplit
    · ipureintro; rfl
    · isplit; iexact He; iexact Ht
  | n' :: ns, (pe, t) :: cs, k + 1, n, h => by
    simp at h
    rw [trieRepC_cons_eq]; iintro ⟨-, -, H⟩
    simp only [List.getElem?_cons_succ]
    iapply trieRepC_lookup ns cs k n h; iexact H

theorem trieRepC_wf : ∀ (ns : List fieldpath.setNode) (cs : List (PE × Trie)),
    trieRepC (GF := GF) ns cs ⊢ ⌜∀ x ∈ cs.map Prod.fst, x.wf = true⌝
  | [], [] => by iintro _; ipureintro; simp
  | [], _ :: _ => by unfold trieRepC; iintro %h; exact h.elim
  | _ :: _, [] => by unfold trieRepC; iintro %h; exact h.elim
  | n :: ns, (pe, t) :: cs => by
    rw [trieRepC_cons_eq]; iintro ⟨He, -, H⟩
    ihave %h1 := fpL.isPE_wf' _ pe $$ He
    ihave %h2 := trieRepC_wf ns cs $$ H
    ipureintro; intro x hx
    simp only [List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h1
    · exact h2 x hx

theorem isVSet_mk (p : Loc) (e : VSet) :
    isSet (GF := GF) p e.set ⊢
      isVSet (interface.mkOk fieldpath.versionedSet.ty #(fieldpath.versionedSet.mk p e.version e.applied)) e := by
  iintro H; unfold isVSet; iexists p; iframe; ipureintro; rfl

end rep

end fpD

end smd
end EtcdGrove
end Perennial
