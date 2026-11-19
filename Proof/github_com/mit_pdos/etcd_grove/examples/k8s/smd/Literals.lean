/-
The driver's literals in the model: a `map[string]interface{}` literal (`m ↦$` the map its
entries' insertions build) is an `ownUMap` of its sorted entries (`mkKVs`), and a
`fieldpath.ManagedFields` literal an `ownMF`. Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open Iris Iris.BI Iris.ProofMode
open smd

/-! ## Sorted insertion (`insertKV`) and a literal's Go map -/

theorem lookupKV_insertKV {α : Type} (k k' : GoString) (v : α) (L : List (GoString × α)) :
    lookupKV k (insertKV k' v L) = if k' = k then some v else lookupKV k L := by
  induction L with
  | nil => simp [insertKV, lookupKV]
  | cons hd tl ih =>
    obtain ⟨k'', v''⟩ := hd
    by_cases h1 : k'' = k'
    · subst h1; by_cases h : k'' = k <;> simp [insertKV, lookupKV, h]
    · by_cases h2 : gsLt k' k'' = true
      · simp only [insertKV, h1, h2, ite_false, ite_true]
        by_cases h3 : k' = k
        · simp [lookupKV, h3]
        · simp [lookupKV, h3]
      · simp only [insertKV, h1, h2, ite_false, Bool.false_eq_true]
        by_cases h3 : k'' = k
        · subst h3
          have : k' ≠ k'' := fun h => h1 h.symm
          simp [lookupKV, this]
        · simp [lookupKV, h3, ih]

/-- A literal's entries, sorted: the keys are those of the entries. -/
theorem lookupKV_foldl_isSome {α : Type} (kvs L : List (GoString × α)) (k : GoString) :
    (lookupKV k (kvs.foldl (fun m (p : GoString × α) => insertKV p.1 p.2 m) L)).isSome =
      (decide (k ∈ kvs.map Prod.fst) || (lookupKV k L).isSome) := by
  induction kvs generalizing L with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, ih, lookupKV_insertKV, List.map_cons, List.mem_cons]
    by_cases h : hd.1 = k
    · simp [h]
    · have h' : k ≠ hd.1 := fun e => h e.symm
      simp [h, h']

theorem mem_insertKV {α : Type} (p : GoString × α) (k : GoString) (v : α) (L : List (GoString × α))
    (h : p ∈ insertKV k v L) : p = (k, v) ∨ p ∈ L := by
  induction L with
  | nil => simp [insertKV] at h; exact Or.inl h
  | cons hd tl ih =>
    obtain ⟨k'', v''⟩ := hd
    simp only [insertKV] at h
    split at h
    · simp at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · split at h
      · simp at h
        rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · simp at h
        rcases h with h | h
        · exact Or.inr (by simp [h])
        · rcases ih h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (List.mem_cons_of_mem _ h')

theorem mem_foldl_insertKV {α : Type} (kvs L : List (GoString × α)) (p : GoString × α)
    (h : p ∈ kvs.foldl (fun m (q : GoString × α) => insertKV q.1 q.2 m) L) : p ∈ kvs ∨ p ∈ L := by
  induction kvs generalizing L with
  | nil => exact Or.inr h
  | cons hd tl ih =>
    rcases ih _ h with h' | h'
    · exact Or.inl (List.mem_cons_of_mem _ h')
    · rcases mem_insertKV _ _ _ _ h' with h'' | h''
      · exact Or.inl (by simp [h''])
      · exact Or.inr h''

/-- The Go map a literal builds: its entries inserted in order. -/
def litMap {V : Type} (ps : List (GoString × V)) (M0 : GMap GoString V) : GMap GoString V :=
  ps.foldl (fun M e => <[e.1 := e.2]> M) M0

theorem litMap_isSome {V : Type} (ps : List (GoString × V)) (M0 : GMap GoString V) (k : GoString) :
    (litMap ps M0 !! k).isSome = (decide (k ∈ ps.map Prod.fst) || (M0 !! k).isSome) := by
  induction ps generalizing M0 with
  | nil => simp [litMap]
  | cons hd tl ih =>
    simp only [litMap, List.foldl_cons] at ih ⊢
    rw [ih]
    by_cases h : hd.1 = k
    · simp [h]
    · have h' : k ≠ hd.1 := fun e => h e.symm
      simp only [List.map_cons, List.mem_cons, h', false_or]
      simp [h]

theorem litMap_notmem {V : Type} (ps : List (GoString × V)) (M0 : GMap GoString V) (k : GoString)
    (hk : k ∉ ps.map Prod.fst) : litMap ps M0 !! k = M0 !! k := by
  induction ps generalizing M0 with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hk
    simp only [litMap, List.foldl_cons] at ih ⊢
    rw [ih _ hk.2]
    simp [Ne.symm hk.1]

theorem litMap_lookup {V : Type} (ps : List (GoString × V)) (M0 : GMap GoString V) (k : GoString)
    (x : V) (hm : (k, x) ∈ ps) (hnd : (ps.map Prod.fst).Nodup) : litMap ps M0 !! k = some x := by
  induction ps generalizing M0 with
  | nil => simp at hm
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hm with h | h
    · subst h
      have := litMap_notmem tl (<[k := x]> M0) k hnd.1
      simp only [litMap, List.foldl_cons] at this ⊢
      rw [this]; simp
    · have := ih (<[hd.1 := hd.2]> M0) h hnd.2
      simpa [litMap] using this

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]

/-- `ownUM` of entries each found in the map, holding a value owned as given. -/
theorem ownUM_of (M : GMap GoString GoInterface) (es : List (GoString × GoInterface × UVal))
    (L : List (GoString × UVal))
    (hL : ∀ p ∈ L, ∃ e ∈ es, e.1 = p.1 ∧ e.2.2 = p.2 ∧ M !! p.1 = some e.2.1) :
    iprop(□ (∀ e, ⌜e ∈ es⌝ -∗ ownU (GF := GF) e.2.1 e.2.2)) ⊢ ownUM M L := by
  induction L with
  | nil => iintro _; simp only [ownUM]; itrivial
  | cons p L ih =>
    iintro #Hes
    obtain ⟨k, v⟩ := p
    obtain ⟨e, he, h1, h2, h3⟩ := hL (k, v) (by simp)
    have ih' := ih (fun p hp => hL p (List.mem_cons_of_mem _ hp))
    simp only [ownUM]
    iexists e.2.1
    isplitr
    · ipureintro; exact h3
    isplitl
    · ihave He := Hes $$ %e %he
      simp only at h2; subst h2; iexact He
    · iapply ih'; iexact Hes

/-- A `map[string]interface{}` literal: the map of its entries' insertions, each value owned
as its model, is (made persistent) an `ownUMap` of the sorted entries. -/
theorem ownUMap_lit (m : GoMap) (es : List (GoString × GoInterface × UVal))
    (hnd : (es.map (·.1)).Nodup)
    (hs : keysSorted (mkKVs (es.map fun e => (e.1, e.2.2))) = true) :
    iprop(m ↦$ litMap (es.map fun e => (e.1, e.2.1)) ∅ ∗ □ (∀ e, ⌜e ∈ es⌝ -∗ ownU (GF := GF) e.2.1 e.2.2)) ⊢
      |==> □ ownUMap m (mkKVs (es.map fun e => (e.1, e.2.2))) := by
  iintro ⟨Hm, #Hes⟩
  imod ownMap_persist _ _ _ $$ Hm with #Hm
  imodintro
  imodintro
  unfold ownUMap
  iexists _
  iframe Hm
  isplitr
  · ipureintro
    refine ⟨hs, fun k => ?_⟩
    rw [litMap_isSome, mkKVs, lookupKV_foldl_isSome]
    simp [List.map_map, Function.comp_def, lookupKV]
  · iapply ownUM_of _ es
    · intro p hp
      rcases mem_foldl_insertKV _ _ _ hp with h | h
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
        refine ⟨e, he, rfl, rfl, ?_⟩
        apply litMap_lookup
        · exact List.mem_map.2 ⟨e, he, rfl⟩
        · simpa [Function.comp_def] using hnd
      · simp at h
    · iexact Hes

/-- `ownMFL` of entries each found in the map, holding a versioned set owned as given. -/
theorem ownMFL_of (M : GMap GoString GoInterface) (es : List (GoString × GoInterface × VSet))
    (L : MF) (hL : ∀ p ∈ L, ∃ e ∈ es, e.1 = p.1 ∧ e.2.2 = p.2 ∧ M !! p.1 = some e.2.1) :
    iprop(□ (∀ e, ⌜e ∈ es⌝ -∗ ownVSet (GF := GF) e.2.1 e.2.2)) ⊢ ownMFL M L := by
  induction L with
  | nil => iintro _; simp only [ownMFL]; itrivial
  | cons p L ih =>
    iintro #Hes
    obtain ⟨k, v⟩ := p
    obtain ⟨e, he, h1, h2, h3⟩ := hL (k, v) (by simp)
    have ih' := ih (fun p hp => hL p (List.mem_cons_of_mem _ hp))
    simp only [ownMFL]
    iexists e.2.1
    isplitr
    · ipureintro; exact h3
    isplitl
    · ihave He := Hes $$ %e %he
      simp only at h2; subst h2; iexact He
    · iapply ih'; iexact Hes

/-- A `fieldpath.ManagedFields` literal: as `ownUMap_lit`, an `ownMF` of the sorted entries. -/
theorem ownMF_lit (m : GoMap) (es : List (GoString × GoInterface × VSet))
    (hnd : (es.map (·.1)).Nodup)
    (hs : keysSorted (mkMF (es.map fun e => (e.1, e.2.2))) = true) :
    iprop(m ↦$ litMap (es.map fun e => (e.1, e.2.1)) ∅ ∗ □ (∀ e, ⌜e ∈ es⌝ -∗ ownVSet (GF := GF) e.2.1 e.2.2)) ⊢
      |==> □ ownMF m (mkMF (es.map fun e => (e.1, e.2.2))) := by
  iintro ⟨Hm, #Hes⟩
  imod ownMap_persist _ _ _ $$ Hm with #Hm
  imodintro
  imodintro
  unfold ownMF
  iexists _
  iframe Hm
  isplitr
  · ipureintro
    refine ⟨hs, fun k => ?_⟩
    rw [litMap_isSome, mkMF, lookupKV_foldl_isSome]
    simp [List.map_map, Function.comp_def, lookupKV]
  · iapply ownMFL_of _ es
    · intro p hp
      rcases mem_foldl_insertKV _ _ _ hp with h | h
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
        refine ⟨e, he, rfl, rfl, ?_⟩
        apply litMap_lookup
        · exact List.mem_map.2 ⟨e, he, rfl⟩
        · simpa [Function.comp_def] using hnd
      · simp at h
    · iexact Hes

/-! ## Unstructured values in interfaces -/

theorem ownU_str (x : GoString) : ⊢ ownU (GF := GF) (interface.mkOk go.string #x) (.str x) := by
  simp only [ownU]; ipureintro; trivial

theorem ownU_int (n : w64) : ⊢ ownU (GF := GF) (interface.mkOk go.int64 #n) (.int n) := by
  simp only [ownU]; ipureintro; trivial

theorem ownU_map (m : GoMap) (kvs : List (GoString × UVal)) :
    ownUMap (GF := GF) m kvs ⊢ ownU (interface.mkOk mapStrIfaceTy #m) (.map kvs) := by
  simp only [ownU, ownUMap]
  iintro ⟨%M, Hm, %h, HM⟩
  iexists m, M
  iframe
  ipureintro; exact ⟨rfl, h⟩

/-- A `schema.TypeRef{NamedType: &name}` literal. -/
theorem ownTypeRef_named (p : Loc) (n : GoString) :
    p ↦□ n ⊢ ownTypeRef (GF := GF) false
      ({ NamedType' := p, Inlined' := zeroValDef, ElementRelationship' := null, Nullable' := false } :
        sigs_k8s_io.structured_merge_diff.v7.schema.TypeRef) (named n) := by
  iintro #Hp
  simp only [named, zeroAtom, ownTypeRef, ownAtom, ownStrPtr, ownOptList, ownOptMap]
  isplitr
  · ipureintro; simp
  isplitr
  · iexact Hp
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; rfl
  · ipureintro; rfl

end own

end k8s_smd
end EtcdGrove
end Perennial
