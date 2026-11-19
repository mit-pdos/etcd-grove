/-
Laws of SMD's representation predicates (`Own.lean`): every predicate but the schema's is
persistent (its ownership is discarded fractions and pure facts). Lean-first (2026-11-19,
notes/smd-robustness.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.Own

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : merge.Assumptions]

mutual
theorem ownU_persistent : (x : UVal) → (i : GoInterface) → Persistent (ownU (GF := GF) i x)
  | .null, _ => by simp only [ownU]; infer_instance
  | .bool _, _ => by simp only [ownU]; infer_instance
  | .int _, _ => by simp only [ownU]; infer_instance
  | .str _, _ => by simp only [ownU]; infer_instance
  | .list vs, _ => by
    have := fun xs => ownUL_persistent vs xs
    simp only [ownU]; infer_instance
  | .map kvs, _ => by
    have := fun M => ownUM_persistent kvs M
    simp only [ownU]; infer_instance
  termination_by structural x => x
theorem ownUL_persistent : (vs : List UVal) → (xs : List GoInterface) → Persistent (ownUL (GF := GF) xs vs)
  | [], [] => by simp only [ownUL]; infer_instance
  | [], _ :: _ => by simp only [ownUL]; infer_instance
  | _ :: _, [] => by simp only [ownUL]; infer_instance
  | v :: vs, x :: xs => by
    have := ownU_persistent v x
    have := ownUL_persistent vs xs
    simp only [ownUL]; infer_instance
  termination_by structural vs => vs
theorem ownUM_persistent : (kvs : List (GoString × UVal)) → (M : GMap GoString GoInterface) →
    Persistent (ownUM (GF := GF) M kvs)
  | [], _ => by simp only [ownUM]; infer_instance
  | (_, v) :: kvs, M => by
    have := fun x => ownU_persistent v x
    have := ownUM_persistent kvs M
    simp only [ownUM]; infer_instance
  termination_by structural kvs => kvs
end

attribute [instance] ownU_persistent ownUL_persistent ownUM_persistent

instance ownUMap_persistent (m : GoMap) (kvs : List (GoString × UVal)) :
    Persistent (ownUMap (GF := GF) m kvs) := by unfold ownUMap; infer_instance

instance ownValue_persistent (v : value.Value) (x : UVal) :
    Persistent (ownValue (GF := GF) v x) := by unfold ownValue; infer_instance

instance ownValueOpt_persistent (v : value.Value) (x : Option UVal) :
    Persistent (ownValueOpt (GF := GF) v x) := by cases x <;> simp only [ownValueOpt] <;> infer_instance

theorem ownFieldsL_persistent : (fs : List value.Field) → (fl : FieldList) →
    Persistent (ownFieldsL (GF := GF) fs fl)
  | [], [] => by simp only [ownFieldsL]; infer_instance
  | [], _ :: _ => by simp only [ownFieldsL]; infer_instance
  | _ :: _, [] => by simp only [ownFieldsL]; infer_instance
  | _ :: fs, (_, _) :: fl => by
    have := ownFieldsL_persistent fs fl
    simp only [ownFieldsL]; infer_instance
attribute [instance] ownFieldsL_persistent

instance ownFieldList_persistent (s : GoSlice) (fl : FieldList) :
    Persistent (ownFieldList (GF := GF) s fl) := by unfold ownFieldList; infer_instance

instance ownPE_persistent (e : fieldpath.PathElement) (pe : PE) :
    Persistent (ownPE (GF := GF) e pe) := by cases pe <;> simp only [ownPE] <;> infer_instance

theorem ownPEL_persistent : (es : List fieldpath.PathElement) → (ps : List PE) →
    Persistent (ownPEL (GF := GF) es ps)
  | [], [] => by simp only [ownPEL]; infer_instance
  | [], _ :: _ => by simp only [ownPEL]; infer_instance
  | _ :: _, [] => by simp only [ownPEL]; infer_instance
  | _ :: es, _ :: ps => by
    have := ownPEL_persistent es ps
    simp only [ownPEL]; infer_instance
attribute [instance] ownPEL_persistent

instance ownPath_persistent (s : GoSlice) (p : Path) :
    Persistent (ownPath (GF := GF) s p) := by unfold ownPath; infer_instance

theorem ownPaths_persistent : (ss : List GoSlice) → (ps : List Path) →
    Persistent (ownPaths (GF := GF) ss ps)
  | [], [] => by simp only [ownPaths]; infer_instance
  | [], _ :: _ => by simp only [ownPaths]; infer_instance
  | _ :: _, [] => by simp only [ownPaths]; infer_instance
  | _ :: ss, _ :: ps => by
    have := ownPaths_persistent ss ps
    simp only [ownPaths]; infer_instance
attribute [instance] ownPaths_persistent

mutual
theorem ownSet_persistent : (s : PSet) → (p : Loc) → Persistent (ownSet (GF := GF) p s)
  | .mk ms cs, _ => by
    have := fun ns => ownNodes_persistent cs ns
    simp only [ownSet]; infer_instance
  termination_by structural s => s
theorem ownNodes_persistent : (cs : List (PE × PSet)) → (ns : List fieldpath.setNode) →
    Persistent (ownNodes (GF := GF) ns cs)
  | [], [] => by simp only [ownNodes]; infer_instance
  | [], _ :: _ => by simp only [ownNodes]; infer_instance
  | _ :: _, [] => by simp only [ownNodes]; infer_instance
  | (_, s) :: cs, n :: ns => by
    have := ownSet_persistent s n.set'
    have := ownNodes_persistent cs ns
    simp only [ownNodes]; infer_instance
  termination_by structural cs => cs
end
attribute [instance] ownSet_persistent ownNodes_persistent

instance ownVSet_persistent (i : fieldpath.VersionedSet) (vs : VSet) :
    Persistent (ownVSet (GF := GF) i vs) := by unfold ownVSet; infer_instance

theorem ownMFL_persistent : (mf : MF) → (M : GMap GoString GoInterface) →
    Persistent (ownMFL (GF := GF) M mf)
  | [], _ => by simp only [ownMFL]; infer_instance
  | (_, _) :: mf, M => by
    have := ownMFL_persistent mf M
    simp only [ownMFL]; infer_instance
attribute [instance] ownMFL_persistent

instance ownMF_persistent (m : fieldpath.ManagedFields) (mf : MF) :
    Persistent (ownMF (GF := GF) m mf) := by unfold ownMF; infer_instance

instance ownStrPtr_persistent (p : Loc) (o : Option GoString) :
    Persistent (ownStrPtr (GF := GF) p o) := by cases o <;> simp only [ownStrPtr] <;> infer_instance

mutual
theorem ownTypeRef_persistent : (t : TypeRef) → (tr : schema.TypeRef) →
    Persistent (ownTypeRef (GF := GF) false tr t)
  | .mk _ a _, tr => by
    have := ownAtom_persistent a tr.Inlined'
    simp only [ownTypeRef]; infer_instance
  termination_by structural x => x
theorem ownAtom_persistent : (a : Atom) → (sa : schema.Atom) → Persistent (ownAtom (GF := GF) false sa a)
  | .mk _ l m, sa => by
    have := ownOptList_persistent l sa.List'
    have := ownOptMap_persistent m sa.Map'
    simp only [ownAtom]; infer_instance
  termination_by structural x => x
theorem ownOptList_persistent : (l : OptListT) → (p : Loc) → Persistent (ownOptList (GF := GF) false p l)
  | .none, _ => by simp only [ownOptList]; infer_instance
  | .some l, p => by
    have := ownListT_persistent l p
    simp only [ownOptList]; infer_instance
  termination_by structural x => x
theorem ownOptMap_persistent : (m : OptMapT) → (p : Loc) → Persistent (ownOptMap (GF := GF) false p m)
  | .none, _ => by simp only [ownOptMap]; infer_instance
  | .some m, p => by
    have := ownMapT_persistent m p
    simp only [ownOptMap]; infer_instance
  termination_by structural x => x
theorem ownListT_persistent : (l : ListT) → (p : Loc) → Persistent (ownListT (GF := GF) false p l)
  | .mk et _ _, _ => by
    have := fun v => ownTypeRef_persistent et v
    simp only [ownListT]; infer_instance
  termination_by structural x => x
theorem ownMapT_persistent : (m : MapT) → (p : Loc) → Persistent (ownMapT (GF := GF) false p m)
  | .mk fs et _, _ => by
    have := fun v => ownTypeRef_persistent et v
    have := fun sfs => ownSFields_persistent fs sfs
    simp only [ownMapT, Bool.false_eq_true, ite_false]; infer_instance
  termination_by structural x => x
theorem ownSFields_persistent : (fs : Fields) → (sfs : List schema.StructField) →
    Persistent (ownSFields (GF := GF) false sfs fs)
  | .nil, [] => by simp only [ownSFields]; infer_instance
  | .nil, _ :: _ => by simp only [ownSFields]; infer_instance
  | .cons _ _, [] => by simp only [ownSFields]; infer_instance
  | .cons (.mk _ t) rest, f :: sfs => by
    have := ownTypeRef_persistent t f.Type'
    have := ownSFields_persistent rest sfs
    simp only [ownSFields]; infer_instance
  termination_by structural x => x
end
attribute [instance] ownTypeRef_persistent

instance ownTV_persistent (p sc : Loc) (tv : TV) : Persistent (ownTV (GF := GF) p sc tv) := by
  unfold ownTV; infer_instance

instance ownTVOpt_persistent (p sc : Loc) (o : Option TV) : Persistent (ownTVOpt (GF := GF) p sc o) := by
  cases o <;> simp only [ownTVOpt] <;> infer_instance

theorem ownConflictL_persistent : (xs : List merge.Conflict) → (cs : List Conflict) →
    Persistent (ownConflictL (GF := GF) xs cs)
  | [], [] => by simp only [ownConflictL]; infer_instance
  | [], _ :: _ => by simp only [ownConflictL]; infer_instance
  | _ :: _, [] => by simp only [ownConflictL]; infer_instance
  | _ :: xs, _ :: cs => by
    have := ownConflictL_persistent xs cs
    simp only [ownConflictL]; infer_instance
attribute [instance] ownConflictL_persistent

instance ownConflicts_persistent (s : merge.Conflicts) (cs : List Conflict) :
    Persistent (ownConflicts (GF := GF) s cs) := by unfold ownConflicts; infer_instance

instance isIdentityConverter_persistent (cv : merge.Converter) :
    Persistent (isIdentityConverter (GF := GF) cv) := by unfold isIdentityConverter; infer_instance

instance ownUpdater_persistent (u : Loc) (b : Bool) : Persistent (ownUpdater (GF := GF) u b) := by
  unfold ownUpdater; infer_instance

end laws

end smd
end EtcdGrove
end Perennial
