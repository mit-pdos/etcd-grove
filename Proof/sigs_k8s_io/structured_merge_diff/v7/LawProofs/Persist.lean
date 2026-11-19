/-
**The root laws' persistence part, proved** (`v7/Laws.lean`, "Persistence"): every persistent
representation predicate as a `Persistent` instance, and each `<P>_persistent.law` from it.

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.Laws
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

namespace LawProofs

/-! ## `value` -/

mutual
theorem isIface_pers (i : GoInterface) : (x : UVal) → Persistent (isIface (GF := GF) i x)
  | .null => by unfold isIface; infer_instance
  | .bool _ => by unfold isIface; infer_instance
  | .int _ => by unfold isIface; infer_instance
  | .str _ => by unfold isIface; infer_instance
  | .list vs => by
      unfold isIface
      have := fun xs => isIfaceL_pers xs vs
      infer_instance
  | .map kvs => by
      unfold isIface
      have := fun M => isIfaceM_pers M kvs
      infer_instance
  termination_by structural x => x
theorem isIfaceL_pers : (xs : List GoInterface) → (vs : List UVal) →
    Persistent (isIfaceL (GF := GF) xs vs)
  | [], [] => by unfold isIfaceL; infer_instance
  | [], _ :: _ => by unfold isIfaceL; infer_instance
  | _ :: _, [] => by unfold isIfaceL; infer_instance
  | x :: xs, v :: vs => by
      unfold isIfaceL
      have := isIface_pers x v
      have := isIfaceL_pers xs vs
      infer_instance
  termination_by structural _ vs => vs
theorem isIfaceM_pers (M : GMap GoString GoInterface) : (kvs : List (GoString × UVal)) →
    Persistent (isIfaceM (GF := GF) M kvs)
  | [] => by unfold isIfaceM; infer_instance
  | (k, v) :: kvs => by
      unfold isIfaceM
      have := fun x => isIface_pers x v
      have := isIfaceM_pers M kvs
      infer_instance
  termination_by structural kvs => kvs
end

attribute [instance] isIface_pers isIfaceL_pers isIfaceM_pers

instance isVal_pers (v : value.Value) (x : UVal) : Persistent (isVal (GF := GF) v x) := by
  unfold isVal isValF; infer_instance

instance isFieldsL_pers : (fs : List value.Field) → (fl : FieldList) →
    Persistent (isFieldsL (GF := GF) fs fl)
  | [], [] => by unfold isFieldsL; infer_instance
  | [], _ :: _ => by unfold isFieldsL; infer_instance
  | _ :: _, [] => by unfold isFieldsL; infer_instance
  | f :: fs, (n, x) :: rest => by
      unfold isFieldsL
      have := isFieldsL_pers fs rest
      infer_instance

instance isFieldList_pers (s : GoSlice) (fl : FieldList) : Persistent (isFieldList (GF := GF) s fl) := by
  unfold isFieldList; infer_instance

/-! ## `fieldpath` -/

instance isPE_pers (e : fieldpath.PathElement) : (pe : PE) → Persistent (isPE (GF := GF) e pe)
  | .field _ => by unfold isPE; infer_instance
  | .key _ => by unfold isPE; infer_instance
  | .value _ => by unfold isPE; infer_instance
  | .index _ => by unfold isPE; infer_instance

instance isPEL_pers : (es : List fieldpath.PathElement) → (pes : List PE) →
    Persistent (isPEL (GF := GF) es pes)
  | [], [] => by unfold isPEL; infer_instance
  | [], _ :: _ => by unfold isPEL; infer_instance
  | _ :: _, [] => by unfold isPEL; infer_instance
  | e :: es, pe :: pes => by
      unfold isPEL
      have := isPEL_pers es pes
      infer_instance

instance isPath_pers (s : GoSlice) (p : Path) : Persistent (isPath (GF := GF) s p) := by
  unfold isPath; infer_instance

instance isPaths_pers : (ss : List GoSlice) → (ps : List Path) → Persistent (isPaths (GF := GF) ss ps)
  | [], [] => by unfold isPaths; infer_instance
  | [], _ :: _ => by unfold isPaths; infer_instance
  | _ :: _, [] => by unfold isPaths; infer_instance
  | s :: ss, p :: ps => by
      unfold isPaths
      have := isPaths_pers ss ps
      infer_instance

mutual
theorem trieRep_pers (p : Loc) : (t : Trie) → Persistent (trieRep (GF := GF) p t)
  | .mk ms cs => by
      unfold trieRep
      have := fun ns => trieRepC_pers ns cs
      infer_instance
  termination_by structural t => t
theorem trieRepC_pers : (ns : List fieldpath.setNode) → (cs : List (PE × Trie)) →
    Persistent (trieRepC (GF := GF) ns cs)
  | [], [] => by unfold trieRepC; infer_instance
  | [], _ :: _ => by unfold trieRepC; infer_instance
  | _ :: _, [] => by unfold trieRepC; infer_instance
  | n :: ns, (pe, t) :: cs => by
      unfold trieRepC
      have := trieRep_pers n.set' t
      have := trieRepC_pers ns cs
      infer_instance
  termination_by structural _ cs => cs
end

attribute [instance] trieRep_pers trieRepC_pers

instance isSet_pers (p : Loc) (S : PathSet) : Persistent (isSet (GF := GF) p S) := by
  unfold isSet; infer_instance

instance isVSet_pers (i : fieldpath.VersionedSet) (e : VSet) : Persistent (isVSet (GF := GF) i e) := by
  unfold isVSet; infer_instance

instance isMFL_pers (M : GMap GoString GoInterface) : (mf : MF) → Persistent (isMFL (GF := GF) M mf)
  | [] => by unfold isMFL; infer_instance
  | (k, e) :: rest => by
      unfold isMFL
      have := isMFL_pers M rest
      infer_instance

instance isMF_pers (m : fieldpath.ManagedFields) (mf : MF) : Persistent (isMF (GF := GF) m mf) := by
  unfold isMF; infer_instance

/-! ## `schema` -/

instance isTypeRef_pers (tr : schema.TypeRef) (t : TypeRef) : Persistent (isTypeRef (GF := GF) tr t) := by
  unfold isTypeRef; infer_instance

instance isTypeRefOpt_pers (tr : schema.TypeRef) : (ot : Option TypeRef) →
    Persistent (isTypeRefOpt (GF := GF) tr ot)
  | none => by unfold isTypeRefOpt; infer_instance
  | some _ => by unfold isTypeRefOpt; infer_instance

instance lazyIndex_pers {T : Type} [ZeroVal T] (o u : Loc) (ok : GMap GoString T → Prop) :
    Persistent (lazyIndex (GF := GF) (T := T) false o u ok) := by
  unfold lazyIndex; simp only [Bool.false_eq_true, ↓reduceIte]; infer_instance

instance isStructField_pers (sf : schema.StructField) (f : GoString × TypeRef) :
    Persistent (isStructField (GF := GF) sf f) := by
  unfold isStructField; infer_instance

instance isFields_pers : (sfs : List schema.StructField) → (fs : List (GoString × TypeRef)) →
    Persistent (isFields (GF := GF) sfs fs)
  | [], [] => by unfold isFields; infer_instance
  | [], _ :: _ => by unfold isFields; infer_instance
  | _ :: _, [] => by unfold isFields; infer_instance
  | f :: fs, nt :: rest => by
      unfold isFields
      have := isFields_pers fs rest
      infer_instance

instance isListRep_pers (l : Loc) (e : TypeRef) (rel : ElemRel) (ks : List GoString) :
    Persistent (isListRep (GF := GF) l e rel ks) := by
  unfold isListRep; infer_instance

instance mapRep_pers (m : Loc) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel) :
    Persistent (mapRep (GF := GF) false m fs e rel) := by
  unfold mapRep; infer_instance

instance isMapRep_pers (m : Loc) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel) :
    Persistent (isMapRep (GF := GF) m fs e rel) := by
  unfold isMapRep; infer_instance

instance isAtom_pers (a : schema.Atom) : (A : Atom) → Persistent (isAtom (GF := GF) false a A)
  | .scalar _ => by unfold isAtom; infer_instance
  | .list _ _ _ => by unfold isAtom; infer_instance
  | .map _ _ _ => by unfold isAtom; infer_instance

instance isAtomOpt_pers (a : schema.Atom) : (oA : Option Atom) → Persistent (isAtomOpt (GF := GF) a oA)
  | none => by unfold isAtomOpt; infer_instance
  | some _ => by unfold isAtomOpt; infer_instance

instance isTypeDefs_pers : (tds : List schema.TypeDef) → (ts : List (GoString × Atom)) →
    Persistent (isTypeDefs (GF := GF) false tds ts)
  | [], [] => by unfold isTypeDefs; infer_instance
  | [], _ :: _ => by unfold isTypeDefs; infer_instance
  | _ :: _, [] => by unfold isTypeDefs; infer_instance
  | td :: tds, (n, a) :: rest => by
      unfold isTypeDefs
      have := isTypeDefs_pers tds rest
      infer_instance

instance isSchema_pers (sc : Loc) (S : Schema) : Persistent (isSchema (GF := GF) sc S) := by
  unfold isSchema schemaRep; infer_instance

/-! ## `typed`, `merge` -/

instance isTV_pers (p sc : Loc) (S : Schema) (t : TypeRef) (x : UVal) :
    Persistent (isTV (GF := GF) p sc S t x) := by
  unfold isTV; infer_instance

instance isConflictL_pers : (xs : List merge.Conflict) → (cs : List (GoString × Path)) →
    Persistent (isConflictL (GF := GF) xs cs)
  | [], [] => by unfold isConflictL; infer_instance
  | [], _ :: _ => by unfold isConflictL; infer_instance
  | _ :: _, [] => by unfold isConflictL; infer_instance
  | x :: xs, (m, p) :: cs => by
      unfold isConflictL
      have := isConflictL_pers xs cs
      infer_instance

instance isConflicts_pers (s : merge.Conflicts) (cs : List (GoString × Path)) :
    Persistent (isConflicts (GF := GF) s cs) := by
  unfold isConflicts; infer_instance

instance isIdentityConverter_pers (cv : merge.Converter) :
    Persistent (isIdentityConverter (GF := GF) cv) := by
  unfold isIdentityConverter; infer_instance

instance isUpdater_pers (u : Loc) (cv : merge.Converter) (igf igfl : GoMap) (rion : Bool) :
    Persistent (isUpdater (GF := GF) u cv igf igfl rion) := by
  unfold isUpdater; infer_instance

theorem pers_box {P : IProp GF} [Persistent P] : P ⊢ □ P := by
  iintro #H; imodintro; iexact H

end LawProofs

open LawProofs

/-! ## The laws -/

theorem isIface_persistent_law_holds : isIface_persistent.law (GF := GF) := fun _ _ => pers_box
theorem isVal_persistent_law_holds : isVal_persistent.law (GF := GF) := fun _ _ => pers_box
theorem isFieldList_persistent_law_holds : isFieldList_persistent.law (GF := GF) :=
  fun _ _ => pers_box
theorem isPE_persistent_law_holds : isPE_persistent.law (GF := GF) := fun _ _ => pers_box
theorem isPath_persistent_law_holds : isPath_persistent.law (GF := GF) := fun _ _ => pers_box
theorem isPaths_persistent_law_holds : isPaths_persistent.law (GF := GF) := fun _ _ => pers_box
theorem isSet_persistent_law_holds : isSet_persistent.law (GF := GF) := fun _ _ => pers_box
theorem isVSet_persistent_law_holds : isVSet_persistent.law (GF := GF) := fun _ _ => pers_box
theorem isMF_persistent_law_holds : isMF_persistent.law (GF := GF) := fun _ _ => pers_box
theorem isSchema_persistent_law_holds : isSchema_persistent.law (GF := GF) := fun _ _ => pers_box
theorem isTypeRef_persistent_law_holds : isTypeRef_persistent.law (GF := GF) := fun _ _ => pers_box
theorem isTV_persistent_law_holds : isTV_persistent.law (GF := GF) :=
  fun _ _ _ _ _ => pers_box
theorem isConflicts_persistent_law_holds : isConflicts_persistent.law (GF := GF) :=
  fun _ _ => pers_box
theorem isIdentityConverter_persistent_law_holds : isIdentityConverter_persistent.law (GF := GF) :=
  fun _ => pers_box
theorem isUpdater_persistent_law_holds : isUpdater_persistent.law (GF := GF) :=
  fun _ _ _ _ _ => pers_box

end laws
end smd
end EtcdGrove
end Perennial
