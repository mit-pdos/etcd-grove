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

@[simp] theorem pm_insert_key {V : Type} [FfiSyntax] (m : GMap Key V) (k : Key) (v : V) :
    Iris.Std.PartialMap.insert m k v = <[k := v]> m := rfl

@[simp] theorem pm_delete_key {V : Type} [FfiSyntax] (m : GMap Key V) (k : Key) :
    Iris.Std.PartialMap.delete m k = GMap.delete k m := rfl

theorem pm_get_key {V : Type} [FfiSyntax] (m : GMap Key V) (k : Key) :
    Iris.Std.PartialMap.get? m k = m !! k := rfl

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A key is a safe map key: comparing it with itself (field by field) does not panic (as the
consistency store's `owner_safeMapKey`, a `Prop` instance of the same class). -/
instance key_safeMapKey [ApiDeps] (k : Key) :
    SafeMapKey (GF := GF) k8s_io.apimachinery.pkg.types.NamespacedName.ty k where
  wp_go_eq_safe_map_key s E Φ := by
    iintro HΦ
    wp_pures
    iapply HΦ

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
