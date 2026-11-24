/-
Lean-first (no Rocq counterpart).

# The items map's lemmas (k8s 7g step 3)

`itemsRO M items` (`Defs.lean`) relates a `*Model`'s `Items` map's contents `M` to the objects
`items`, key by key, each value a read-only `*Obj`: lookup, insert, delete and the empty map, for
the proofs of `Clone`, `create`, `update`, `delete` and the reads.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProofMode map k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj)

@[simp] theorem pm_insert_gmap {K V : Type} [DecidableEq K] [Hashable K] (m : GMap K V) (k : K)
    (v : V) : Iris.Std.PartialMap.insert m k v = <[k := v]> m := rfl

@[simp] theorem pm_delete_gmap {K V : Type} [DecidableEq K] [Hashable K] (m : GMap K V) (k : K) :
    Iris.Std.PartialMap.delete m k = GMap.delete k m := rfl

theorem pm_get_gmap {K V : Type} [DecidableEq K] [Hashable K] (m : GMap K V) (k : K) :
    Iris.Std.PartialMap.get? m k = m !! k := rfl

/-- An insertion into fewer than `2^62` items leaves at most `2^62`. -/
theorem size_insert_le_of_lt {V : Type} (items : GMap GoString V) (k : GoString) (o : V)
    (h : GMap.size items < 2 ^ 62) : GMap.size (<[k := o]> items) ≤ 2 ^ 62 := by
  have := GMap.map_size_insert items k o
  split at this <;> omega

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]

/-- The `Items` value of an object at `p`. -/
abbrev objIface (p : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #p

/-- A model carries the driver's package initialization. -/
theorem modelAt_pkg (mp : Loc) (m : RM) :
    modelAt (GF := GF) mp m ⊢ isPkgInit pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 := by
  unfold modelAt modelRep
  iintro ⟨#H, -⟩
  iexact H

/-- The items are at most `2^62`. -/
theorem itemsRO_size (M : GMap GoString GoInterface) (items : GMap GoString Obj) :
    itemsRO (GF := GF) M items ⊢ ⌜GMap.size items ≤ 2 ^ 62⌝ := by
  unfold itemsRO
  iintro ⟨%h, -⟩
  ipureintro; exact h

theorem itemsRO_dom (M : GMap GoString GoInterface) (items : GMap GoString Obj) (k : GoString) :
    itemsRO (GF := GF) M items ⊢ ⌜(M !! k).isSome ↔ (items !! k).isSome⌝ := by
  unfold itemsRO mapRep
  iintro ⟨-, H⟩
  ihave %h := (BigSepM2.bigSepM2_lookup_iff (PROP := IProp GF)) $$ H
  ipureintro
  have := h k
  simp only [pm_get_gmap, GMap.lookup_fmap, Option.isSome_map] at this
  exact this

theorem itemsRO_dom_all (M : GMap GoString GoInterface) (items : GMap GoString Obj) :
    itemsRO (GF := GF) M items ⊢ ⌜∀ k, (M !! k).isSome ↔ (items !! k).isSome⌝ := by
  unfold itemsRO mapRep
  iintro ⟨-, H⟩
  ihave %h := (BigSepM2.bigSepM2_lookup_iff (PROP := IProp GF)) $$ H
  ipureintro
  intro k
  have := h k
  simp only [pm_get_gmap, GMap.lookup_fmap, Option.isSome_map] at this
  exact this

theorem itemsRO_none (M : GMap GoString GoInterface) (items : GMap GoString Obj) (k : GoString) :
    itemsRO (GF := GF) M items ⊢ ⌜M !! k = none ↔ items !! k = none⌝ := by
  iintro H
  ihave %h := itemsRO_dom M items k $$ H
  ipureintro
  cases h1 : M !! k <;> cases h2 : items !! k <;> simp_all

/-- A value of the map: a read-only object, the key's object. -/
theorem itemsRO_lookup (M : GMap GoString GoInterface) (items : GMap GoString Obj) (k : GoString)
    (x : GoInterface) (h : M !! k = some x) :
    itemsRO (GF := GF) M items ⊢ ∃ (p : Loc) (o : Obj),
      ⌜items !! k = some o ∧ x = objIface p⌝ ∗ p ↦□ o := by
  iintro #H
  ihave %hd := itemsRO_dom M items k $$ H
  have : (items !! k).isSome := hd.1 (by simp [h])
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp this
  iunfold itemsRO at H
  icases H with ⟨-, #H⟩
  iunfold mapRep at H
  ihave Hx := (BigSepM2.bigSepM2_lookup (Φ := fun _ x d => deepRep (GF := GF) DFrac.discard x d)
    (m1 := M) (m2 := GMap.fmap DeepV.obj items) (i := k) (x1 := x) (x2 := DeepV.obj o)
    h (by simp [pm_get_gmap, ho])) $$ H
  iunfold deepRep at Hx
  icases Hx with ⟨%p, %hx, #Hp⟩
  iexists p, o
  iframe Hp
  ipureintro
  exact ⟨ho, hx⟩

theorem itemsRO_empty : ⊢ itemsRO (GF := GF) (∅ : GMap GoString GoInterface) ∅ := by
  unfold itemsRO mapRep
  rw [GMap.fmap_empty]
  isplitr
  · ipureintro; rw [GMap.map_size_empty]; omega
  iapply (BigSepM2.bigSepM2_empty (PROP := IProp GF) _).2
  itrivial

/-- The model's items and the map's keys are as many. -/
theorem itemsRO_size_map (M : GMap GoString GoInterface) (items : GMap GoString Obj) :
    itemsRO (GF := GF) M items ⊢ ⌜GMap.size M ≤ 2 ^ 62⌝ := by
  iintro #H
  ihave %hs := itemsRO_size M items $$ H
  ihave %hd := itemsRO_dom_all M items $$ H
  ipureintro
  have e : GMap.size M = GMap.size items :=
    (GMap.size_eq_length M items.domList (GMap.nodup_dom_list items)
      (fun k => by rw [GMap.mem_dom_list, hd k])).trans (GMap.size_eq_dom_list_length items).symm
  omega

/-- Storing a read-only object at a key. -/
theorem itemsRO_insert (M : GMap GoString GoInterface) (items : GMap GoString Obj) (k : GoString)
    (p : Loc) (o : Obj) (hs : GMap.size (<[k := o]> items) ≤ 2 ^ 62) :
    itemsRO (GF := GF) M items ∗ p ↦□ o ⊢ itemsRO (<[k := objIface p]> M) (<[k := o]> items) := by
  iintro ⟨#H, #Hp⟩
  ihave #Hx := deepRO_obj (GF := GF) p o $$ Hp
  ihave %hd := itemsRO_none M items k $$ H
  iunfold itemsRO at H
  unfold itemsRO mapRep
  icases H with ⟨-, #H⟩
  isplitr
  · ipureintro; exact hs
  rw [GMap.fmap_insert]
  cases hm : M !! k with
  | none =>
    have ho : GMap.fmap DeepV.obj items !! k = none := by simp [hd.1 hm]
    have e := (BigSepM2.bigSepM2_insert (Φ := fun _ x d => deepRep (GF := GF) DFrac.discard x d)
      (m1 := M) (m2 := GMap.fmap DeepV.obj items) (i := k) (x1 := objIface p) (x2 := DeepV.obj o)
      hm ho)
    simp only [pm_insert_gmap] at e
    iapply e.2
    iframe Hx H
  | some y =>
    have : (items !! k).isSome := by
      cases h' : items !! k <;> simp_all
    obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.mp this
    icases (BigSepM2.bigSepM2_insert_acc (Φ := fun _ x d => deepRep (GF := GF) DFrac.discard x d)
      (m1 := M) (m2 := GMap.fmap DeepV.obj items) (i := k) (x1 := y) (x2 := DeepV.obj o')
      hm (by simp [pm_get_gmap, ho'])) $$ H with ⟨-, Hback⟩
    ihave H' := Hback $$ %(objIface p) %(DeepV.obj o) Hx
    simp only [pm_insert_gmap]
    iexact H'

/-- Removing a key. -/
theorem itemsRO_delete (M : GMap GoString GoInterface) (items : GMap GoString Obj) (k : GoString) :
    itemsRO (GF := GF) M items ⊢ itemsRO (GMap.delete k M) (GMap.delete k items) := by
  iintro #H
  ihave %hd := itemsRO_none M items k $$ H
  iunfold itemsRO at H
  unfold itemsRO mapRep
  icases H with ⟨%hs, #H⟩
  isplitr
  · ipureintro; have := GMap.map_size_delete items k; split at this <;> omega
  rw [show GMap.fmap DeepV.obj (GMap.delete k items) = GMap.delete k (GMap.fmap DeepV.obj items)
    from GMap.map_eq (fun k' => by
      by_cases hk : k = k'
      · subst hk; simp
      · simp [hk])]
  cases hm : M !! k with
  | none =>
    have ho : GMap.fmap DeepV.obj items !! k = none := by simp [hd.1 hm]
    rw [GMap.delete_notin _ _ hm, GMap.delete_notin _ _ ho]
    iexact H
  | some y =>
    have : (items !! k).isSome := by
      cases h' : items !! k <;> simp_all
    obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.mp this
    have e := (BigSepM2.bigSepM2_delete (Φ := fun _ x d => deepRep (GF := GF) DFrac.discard x d)
      (m1 := M) (m2 := GMap.fmap DeepV.obj items) (i := k) (x1 := y) (x2 := DeepV.obj o')
      hm (by simp [pm_get_gmap, ho']))
    simp only [pm_delete_gmap] at e
    icases e.1 $$ H with ⟨-, H'⟩
    iexact H'

end lemmas

end k8s_correctness
end EtcdGrove
end Perennial
