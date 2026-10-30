/-
**The stored objects' map** (lemmas on `tableLocked`'s `[∗map] _k ↦ x;o ∈ M;O, objAt x 1 o`):
lookup, insert and delete keep the physical and abstract maps in step. Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode

@[simp] theorem pm_insert_key {V : Type} [GooseExts] (m : GMap Key V) (k : Key) (v : V) :
    Iris.Std.PartialMap.insert m k v = <[k := v]> m := rfl

@[simp] theorem pm_delete_key {V : Type} [GooseExts] (m : GMap Key V) (k : Key) :
    Iris.Std.PartialMap.delete m k = GMap.delete k m := rfl

theorem pm_get_key {V : Type} [GooseExts] (m : GMap Key V) (k : Key) :
    Iris.Std.PartialMap.get? m k = m !! k := rfl

/-- What a map's range in key order `keys` collects (`filterMap`) is a list of the map's values
of the selected keys, in some order. -/
theorem perm_keys_filterMap [GooseExts] {V : Type} (O : GMap Key V) (keys : List Key)
    (hnd : keys.Nodup) (hmem : ∀ k, k ∈ keys ↔ (O !! k).isSome) (p : Key → Bool) :
    List.Perm (keys.filterMap (fun k => if p k then O !! k else none))
      ((O.toList.filter (fun kv => p kv.1)).map Prod.snd) := by
  have hperm : List.Perm keys (O.toList.map Prod.fst) := by
    rw [List.perm_ext_iff_of_nodup hnd (GMap.toList_keys_nodup O)]
    intro k
    rw [hmem k]
    constructor
    · intro h
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
      exact List.mem_map.mpr ⟨(k, v), (GMap.mem_toList O k v).mpr hv, rfl⟩
    · intro h
      obtain ⟨⟨k', v⟩, hkv, rfl⟩ := List.mem_map.mp h
      simp [(GMap.mem_toList O k' v).mp hkv]
  have h1 := hperm.filterMap (fun k => if p k then O !! k else none)
  refine h1.trans ?_
  rw [List.filterMap_map]
  have key : ∀ l : List (Key × V), (∀ kv ∈ l, O !! kv.1 = some kv.2) →
      l.filterMap ((fun k => if p k then O !! k else none) ∘ Prod.fst) =
        (l.filter (fun kv => p kv.1)).map Prod.snd := by
    intro l hl
    induction l with
    | nil => rfl
    | cons kv l ih =>
      have hkv := hl kv (by simp)
      have ih' := ih (fun x hx => hl x (by simp [hx]))
      by_cases hp : p kv.1 = true
      · simp [Function.comp, hp, hkv, ih']
      · simp [Function.comp, hp]
        simpa [Function.comp] using ih'
  rw [key O.toList (fun kv h => (GMap.mem_toList O kv.1 kv.2).mp h)]

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A key is a safe map key: comparing it with another (field by field) does not panic and is
equality of values (as the consistency store's `owner_safeMapKey`, a `Prop` instance of the same
class). -/
instance key_safeMapKey [ApiDeps] (k : Key) :
    SafeMapKey (GF := GF) k8s_io.apimachinery.pkg.types.NamespacedName.ty k where
  key_ok := trivial
  wp_go_eq_map_key k' _ s E Φ := by
    iintro HΦ
    wp_pures
    by_cases h1 : k.Namespace' = k'.Namespace'
    · rw [decide_eq_true h1]
      wp_pures
      rw [show decide (k.Name' = k'.Name') = decide (k = k') by cases k; cases k'; simp_all]
      iapply HΦ
    · rw [decide_eq_false h1]
      wp_pures
      rw [show (false : Bool) = decide (k = k') by cases k; cases k'; simp_all]
      iapply HΦ

/-- A deep pointer to a basic value, read: `nil`, or the value. -/
theorem ownPtrD_base_some {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (dq : DFrac)
    (e : V) :
    (ownPtrD (V := V) ownBaseD) p dq (some e) ⊣⊢ (p ↦{dq} e : IProp GF) := by
  simp only [ownPtrD, ownBaseD]
  constructor
  · iintro ⟨%x, Hp, %h⟩
    subst h
    iexact Hp
  · iintro Hp
    iexists e
    iframe
    ipureintro; rfl

/-- An object at a value equal to another. -/
theorem objAt_cast {x : GoInterface} {q : DFrac} {a b : Obj} (h : a = b) :
    objAt (GF := GF) x q a ⊢ objAt x q b := by
  subst h; exact .rfl

/-- The stored objects' relation. -/
abbrev objsRel (M : GMap Key GoInterface) (O : GMap Key Obj) : IProp GF :=
  iprop([∗map] _k ↦ x;o ∈ M;O, objAt x (DFrac.own 1) o)

theorem objsRel_dom (M : GMap Key GoInterface) (O : GMap Key Obj) (k : Key) :
    objsRel (GF := GF) M O ⊢ ⌜(M !! k).isSome ↔ (O !! k).isSome⌝ := by
  iintro H
  ihave %h := (BigSepM2.bigSepM2_lookup_iff (PROP := IProp GF)) $$ H
  ipureintro
  exact h k

theorem objsRel_lookup (M : GMap Key GoInterface) (O : GMap Key Obj) (k : Key) (x : GoInterface)
    (h : M !! k = some x) :
    objsRel (GF := GF) M O ⊢ ∃ o, ⌜O !! k = some o⌝ ∗ objAt x (DFrac.own 1) o ∗
      (objAt x (DFrac.own 1) o -∗ objsRel M O) := by
  iintro H
  ihave %hd := objsRel_dom M O k $$ H
  have : (O !! k).isSome := hd.1 (by simp [h])
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp this
  icases (BigSepM2.bigSepM2_lookup_acc (Φ := fun _ x o => objAt (GF := GF) x (DFrac.own 1) o)
    (m1 := M) (m2 := O) (i := k) h ho) $$ H with ⟨Hx, Hback⟩
  iexists o
  iframe
  ipureintro; exact ho

theorem objsRel_insert (M : GMap Key GoInterface) (O : GMap Key Obj) (k : Key) (x : GoInterface)
    (o : Obj) :
    objsRel (GF := GF) M O ∗ objAt x (DFrac.own 1) o ⊢ objsRel (<[k := x]> M) (<[k := o]> O) := by
  iintro ⟨H, Hx⟩
  ihave %hd := objsRel_dom M O k $$ H
  cases hm : M !! k with
  | none =>
    have ho : O !! k = none := by
      cases h' : O !! k with
      | none => rfl
      | some _ => simp [hm, h'] at hd
    unfold objsRel
    have e := (BigSepM2.bigSepM2_insert (Φ := fun _ x o => objAt (GF := GF) x (DFrac.own 1) o)
      (m1 := M) (m2 := O) (i := k) (x1 := x) (x2 := o) hm ho)
    simp only [pm_insert_key] at e
    iapply e.2
    iframe
  | some y =>
    have : (O !! k).isSome := hd.1 (by simp [hm])
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp this
    unfold objsRel
    icases (BigSepM2.bigSepM2_insert_acc (Φ := fun _ x o => objAt (GF := GF) x (DFrac.own 1) o)
      (m1 := M) (m2 := O) (i := k) hm hp) $$ H with ⟨-, Hback⟩
    ihave H := Hback $$ %x %o Hx
    simp only [pm_insert_key]
    iexact H

theorem objsRel_delete (M : GMap Key GoInterface) (O : GMap Key Obj) (k : Key) :
    objsRel (GF := GF) M O ⊢ objsRel (GMap.delete k M) (GMap.delete k O) := by
  iintro H
  ihave %hd := objsRel_dom M O k $$ H
  cases hm : M !! k with
  | none =>
    have ho : O !! k = none := by
      cases h' : O !! k with
      | none => rfl
      | some _ => simp [hm, h'] at hd
    have e1 : GMap.delete k M = M := GMap.delete_notin _ _ hm
    have e2 : GMap.delete k O = O := GMap.delete_notin _ _ ho
    rw [e1, e2]
    iexact H
  | some y =>
    have : (O !! k).isSome := hd.1 (by simp [hm])
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp this
    unfold objsRel
    icases ((BigSepM2.bigSepM2_delete (Φ := fun _ x o => objAt (GF := GF) x (DFrac.own 1) o)
      (m1 := M) (m2 := O) (i := k) hm hp).1) $$ H with ⟨-, H⟩
    simp only [pm_delete_key]
    iexact H

end lemmas

end apimodel
end EtcdGrove
end Perennial
