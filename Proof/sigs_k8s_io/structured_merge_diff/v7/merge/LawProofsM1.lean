/-
**Helpers of `merge`'s map-iterating stage proofs** (`reconcileManagedFieldsWithSchemaChanges`,
`addBackOwnedItems`, `ConflictsFromManagers`, `Updater.update`): reading an `isMF` map (its
points-to and its entries), and the pure facts on `reconcileMF` and `mfUnion` they use
(`reconcileMF_get`, `reconcileMF_sorted`, `mfUnion_nodes`).
Prove phase (2026-11-21).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.LawProofsStage
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsMF
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsIter
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

/-! ## Pure facts -/

theorem reconcileMF_get_law_holds : reconcileMF_get.law := by
  intro S t mf m
  unfold reconcileMF MF.get
  induction mf with
  | nil => simp [lookupKV]
  | cons me rest ih =>
    obtain ⟨k, e⟩ := me
    simp only [List.map_cons, lookupKV]
    by_cases h : k = m
    · simp [h]
    · simp only [h, ite_false]; exact ih

theorem reconcileMF_sorted_law_holds : reconcileMF_sorted.law := by
  intro S t mf h
  unfold reconcileMF
  rw [LawProofs.keysSorted_iff_pairwise] at h ⊢
  rw [List.pairwise_map]
  exact h.imp (fun h => h)

theorem mfUnion_mem (mf : MF) (m : GoString) (e : VSet) (h : mf.get m = some e) (q : Path)
    (hq : q ∈ e.set) : q ∈ mfUnion mf := by
  induction mf with
  | nil => simp [MF.get, lookupKV] at h
  | cons me rest ih =>
    obtain ⟨k, e'⟩ := me
    unfold mfUnion
    simp only [List.foldr_cons]
    rw [show (fun me acc => PathSet.union me.2.set acc) = fun (me : GoString × VSet) acc =>
      PathSet.union me.2.set acc from rfl]
    unfold PathSet.union
    rw [FSet_mem_union_law_holds]
    simp only [MF.get, lookupKV] at h
    by_cases hk : k = m
    · simp only [hk, ite_true, Option.some.injEq] at h
      subst h; exact Or.inl hq
    · simp only [hk, ite_false] at h
      exact Or.inr (ih h)

theorem mfUnion_nodes_law_holds : mfUnion_nodes.law := by
  intro mf m e h
  apply FSet.card_le_of_subset
  intro q hq
  unfold PathSet.nodes at hq ⊢
  rw [FSet_mem_bind_law_holds] at hq ⊢
  obtain ⟨x, hx, hqx⟩ := hq
  exact ⟨x, mfUnion_mem mf m e h x hx, hqx⟩

/-- A manager's set is small enough for `CardLt (2 ^ 63)` callees. -/
theorem mf_entry_cardLt (mf : MF) (m : GoString) (e : VSet) (h : mf.get m = some e)
    (hne : [] ∉ e.set) (hs : (mfUnion mf).nodes.card < smdSizeMax) : e.set.CardLt (2 ^ 63) :=
  nodes_cardLt _ hne (Nat.lt_of_le_of_lt (mfUnion_nodes_law_holds mf m e h) hs)

/-- A `for range` loop's visited keys, one more. -/
theorem take_dom_step {K V : Type} [DecidableEq K] (R : GMap K V) (keys : List K) (j : Int) (key : K)
    (ni : V) (hj : 0 ≤ j) (Hkey : keys[j.toNat]? = some key)
    (HR : ∀ k, (R !! k).isSome = true ↔ k ∈ keys.take j.toNat) :
    ∀ k, ((<[key := ni]> R) !! k).isSome = true ↔ k ∈ keys.take (j + 1).toNat := by
  intro k
  have Htake : keys.take (j + 1).toNat = keys.take j.toNat ++ [key] := by
    rw [show (j + 1).toNat = j.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
  rw [Htake]
  by_cases hk : key = k
  · subst hk; simp
  · rw [GMap.lookup_insert_ne _ _ hk, HR k]
    simp [List.mem_append, Ne.symm hk]

/-- The paths of the managers among `ks`. -/
def mfVis (mf : MF) (ks : List GoString) (q : Path) : Prop :=
  ∃ k ∈ ks, ∃ e, mf.get k = some e ∧ q ∈ e.set

theorem mfVis_nil (mf : MF) (q : Path) : ¬ mfVis mf [] q := by
  rintro ⟨k, hk, -⟩; simp at hk

/-- One more manager's set in a union. -/
theorem mfVis_step (mf : MF) (keys : List GoString) (j : Int) (key : GoString) (e : VSet)
    (U : PathSet) (hj : 0 ≤ j) (Hkey : keys[j.toNat]? = some key) (he : mf.get key = some e)
    (hU : ∀ q, q ∈ U ↔ mfVis mf (keys.take j.toNat) q) :
    ∀ q, q ∈ PathSet.union U e.set ↔ mfVis mf (keys.take (j + 1).toNat) q := by
  intro q
  have Htake : keys.take (j + 1).toNat = keys.take j.toNat ++ [key] := by
    rw [show (j + 1).toNat = j.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
  unfold PathSet.union
  rw [FSet_mem_union_law_holds, hU, Htake]
  unfold mfVis
  constructor
  · rintro (⟨k, hk, e', he', hq⟩ | hq)
    · exact ⟨k, List.mem_append_left _ hk, e', he', hq⟩
    · exact ⟨key, by simp, e, he, hq⟩
  · rintro ⟨k, hk, e', he', hq⟩
    rcases List.mem_append.1 hk with hk | hk
    · exact Or.inl ⟨k, hk, e', he', hq⟩
    · simp at hk; subst hk; rw [he] at he'; cases he'; exact Or.inr hq

theorem mfUnion_mem_iff (mf : MF) (q : Path) : q ∈ mfUnion mf ↔ ∃ me ∈ mf, q ∈ me.2.set := by
  induction mf with
  | nil =>
    unfold mfUnion
    simp only [List.foldr_nil, List.not_mem_nil, false_and, exists_false, iff_false]
    intro h
    have := (FSet_isEmpty_iff_law_holds (PathSet.empty)).1 (by rfl) q
    exact this h
  | cons me rest ih =>
    unfold mfUnion at ih ⊢
    simp only [List.foldr_cons]
    unfold PathSet.union at ih ⊢
    rw [FSet_mem_union_law_holds, ih]
    simp

/-- Every manager visited: the union. -/
theorem mfVis_all (mf : MF) (keys : List GoString) (hs : keysSorted mf = true)
    (hk : ∀ k, k ∈ keys ↔ (mf.get k).isSome = true) :
    ∀ q, mfVis mf keys q ↔ q ∈ mfUnion mf := by
  intro q
  rw [mfUnion_mem_iff]
  constructor
  · rintro ⟨k, -, e, he, hq⟩
    exact ⟨(k, e), fpD.lookupKV_some_mem mf k e he, hq⟩
  · rintro ⟨⟨k, e⟩, hme, hq⟩
    have hget : mf.get k = some e :=
      fpD.mem_lookupKV mf k e (fpD.keysSorted_pairwise mf hs) hme
    exact ⟨k, (hk k).2 (by rw [hget]; rfl), e, hget, hq⟩

/-! ## `ConflictsFromManagers`' pairs -/

/-- The (manager, path) pairs of the managers among `ks`. -/
def pairVis (mf : MF) (ks : List GoString) (c : GoString × Path) : Prop :=
  c.1 ∈ ks ∧ ∃ e, mf.get c.1 = some e ∧ c.2 ∈ e.set

theorem mfPairs_mem_iff (mf : MF) (c : GoString × Path) :
    c ∈ mfPairs mf ↔ ∃ me ∈ mf, c.1 = me.1 ∧ c.2 ∈ me.2.set := by
  induction mf with
  | nil =>
    unfold mfPairs
    simp only [List.foldr_nil, List.not_mem_nil, false_and, exists_false, iff_false]
    intro h
    exact (FSet_isEmpty_iff_law_holds (FSet.empty : FSet (GoString × Path))).1 (by rfl) c h
  | cons me rest ih =>
    unfold mfPairs at ih ⊢
    simp only [List.foldr_cons]
    rw [FSet_mem_union_law_holds, ih, FSet.mem_map']
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨me', hme', h1, h2⟩)
      · exact ⟨me, List.mem_cons_self, rfl, hx⟩
      · exact ⟨me', List.mem_cons_of_mem _ hme', h1, h2⟩
    · rintro ⟨me', hme', h1, h2⟩
      rcases List.mem_cons.1 hme' with rfl | hme'
      · exact Or.inl ⟨c.2, h2, by rw [← h1]⟩
      · exact Or.inr ⟨me', hme', h1, h2⟩

theorem pairVis_all (mf : MF) (keys : List GoString) (hs : keysSorted mf = true)
    (hk : ∀ k, k ∈ keys ↔ (mf.get k).isSome = true) (c : GoString × Path) :
    pairVis mf keys c ↔ c ∈ mfPairs mf := by
  rw [mfPairs_mem_iff]
  constructor
  · rintro ⟨-, e, he, hq⟩
    exact ⟨(c.1, e), fpD.lookupKV_some_mem mf c.1 e he, rfl, hq⟩
  · rintro ⟨⟨k, e⟩, hme, h1, hq⟩
    simp only at h1 hq
    have hget : mf.get k = some e :=
      fpD.mem_lookupKV mf k e (fpD.keysSorted_pairwise mf hs) hme
    subst h1
    exact ⟨(hk _).2 (by rw [hget]; rfl), e, hget, hq⟩

/-- One more manager's pairs. -/
theorem pairVis_step (mf : MF) (keys : List GoString) (j : Int) (key : GoString) (e : VSet)
    (l : List (GoString × Path)) (done : List Path) (hj : 0 ≤ j) (Hkey : keys[j.toNat]? = some key)
    (hnd : keys.Nodup) (he : mf.get key = some e)
    (hl : l.Nodup ∧ ∀ c, c ∈ l ↔ pairVis mf (keys.take j.toNat) c)
    (hdone : done.Nodup ∧ FSet.ofList done = e.set) :
    (l ++ done.map (fun q => (key, q))).Nodup ∧
      ∀ c, c ∈ l ++ done.map (fun q => (key, q)) ↔ pairVis mf (keys.take (j + 1).toNat) c := by
  have Htake : keys.take (j + 1).toNat = keys.take j.toNat ++ [key] := by
    rw [show (j + 1).toNat = j.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
  have hjlt : j.toNat < keys.length := by
    have := List.getElem?_eq_some_iff.1 Hkey; exact this.1
  have hkey_notin : key ∉ keys.take j.toNat := by
    intro hm
    have hk := List.getElem?_eq_some_iff.1 Hkey
    obtain ⟨i, hi, hik⟩ := List.mem_iff_getElem.1 hm
    rw [List.getElem_take] at hik
    have hilt : i < j.toNat := by simp [List.length_take] at hi; omega
    have hi' : keys[i]? = some key := by
      rw [List.getElem?_eq_some_iff]; exact ⟨by omega, hik⟩
    have := list_nodup_getElem?_inj keys hnd i j.toNat key hi' Hkey
    omega
  have hmemd : ∀ q, q ∈ done ↔ q ∈ e.set := by
    intro q; rw [← hdone.2, FSet.mem_ofList']
  refine ⟨?_, fun c => ?_⟩
  · refine List.nodup_append.2 ⟨hl.1, List.pairwise_map.2 (hdone.1.imp (fun h e => h (by cases e; rfl))), ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hb
    exact hkey_notin ((hl.2 _).1 ha).1
  · rw [List.mem_append, hl.2, Htake]
    unfold pairVis
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · exact ⟨List.mem_append_left _ h1, h2⟩
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
        exact ⟨by simp, e, he, (hmemd q).1 hq⟩
    · rintro ⟨h1, e', he', hq⟩
      rcases List.mem_append.1 h1 with h1 | h1
      · exact Or.inl ⟨h1, e', he', hq⟩
      · simp at h1
        right
        rw [h1] at he'; rw [he] at he'; cases he'
        exact List.mem_map.2 ⟨c.2, (hmemd _).2 hq, by rw [← h1]⟩

/-! ## Reading an `isMF` map -/

section iprop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A persistent `ManagedFields` map: its points-to and its entries' views. -/
theorem isMF_read (m : fieldpath.ManagedFields) (mf : MF) :
    isMF (GF := GF) m mf ⊢ ∃ M : GMap GoString GoInterface, m ↦$□ M ∗
      ⌜keysSorted mf = true ∧ ∀ k, (M !! k).isSome = (mf.get k).isSome⌝ ∗
      □ (∀ k i e, ⌜M !! k = some i ∧ mf.get k = some e⌝ -∗ isVSet i e) := by
  unfold isMF
  iintro ⟨%M, Hm, %h, #Hl⟩
  iexists M; iframe
  isplitr
  · ipureintro; exact h
  iapply fpL.isMFL_get M mf; iexact Hl

/-- A set is at a non-nil pointer. -/
theorem isSet_not_null (p : Loc) (S : PathSet) : isSet (GF := GF) p S ⊢ ⌜p ≠ null⌝ := by
  unfold isSet
  iintro ⟨%t, -, H⟩
  cases t with
  | mk ms cs =>
    simp only [trieRep]
    icases H with ⟨%v, %es, %ns, Hp, -⟩
    iapply typedPointsto_not_null $$ Hp

/-- One more conflict at the end of a `Conflicts` slice. -/
theorem isConflictL_snoc : ∀ (xs : List merge.Conflict) (cs : List (GoString × Path))
    (x : merge.Conflict) (m : GoString) (p : Path),
    isConflictL (GF := GF) xs cs ∗ isPath x.Path' p ⊢ ⌜x.Manager' = m⌝ -∗
      isConflictL (xs ++ [x]) (cs ++ [(m, p)])
  | [], [], x, m, p => by
    iintro ⟨-, Hp⟩ %hm
    simp only [List.nil_append, isConflictL]
    iframe Hp
    ipureintro; exact hm
  | y :: ys, (m', p') :: cs, x, m, p => by
    iintro ⟨Hl, Hp⟩ %hm
    simp only [List.cons_append, isConflictL]
    icases Hl with ⟨%hy, Hy, Hl⟩
    iframe Hy
    isplitr
    · ipureintro; exact hy
    iapply isConflictL_snoc ys cs x m p $$ [Hl Hp] %hm
    iframe Hl Hp
  | [], _ :: _, _, _, _ => by
    iintro ⟨Hl, -⟩; simp only [isConflictL]; icases Hl with %h; exact h.elim
  | _ :: _, [], _, _, _ => by
    iintro ⟨Hl, -⟩; simp only [isConflictL]; icases Hl with %h; exact h.elim

end iprop

end smd
end EtcdGrove
end Perennial
