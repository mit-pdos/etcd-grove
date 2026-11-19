/-
**`value`'s laws, proved** (structured-merge-diff v7.0.0): the laws stated in `value/Objects.lean`
(`<X>.law`, proved as `<X>_law_holds`) and the lemmas on `value`'s sealed representation that the
package's own proofs use (persistence instances, the shape of an interface). A defs-tier module:
it unfolds the sealed predicates (`import all` of the package's own modules).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## Persistence -/

mutual
theorem isIface_pers : ∀ (i : GoInterface) (x : UVal), Persistent (isIface (GF := GF) i x)
  | i, .null => by unfold isIface; infer_instance
  | i, .bool _ => by unfold isIface; infer_instance
  | i, .int _ => by unfold isIface; infer_instance
  | i, .str _ => by unfold isIface; infer_instance
  | i, .list vs => by
    have := fun xs => isIfaceL_pers xs vs
    unfold isIface; infer_instance
  | i, .map kvs => by
    have := fun M => isIfaceM_pers M kvs
    unfold isIface; infer_instance
theorem isIfaceL_pers : ∀ (xs : List GoInterface) (vs : List UVal),
    Persistent (isIfaceL (GF := GF) xs vs)
  | [], [] => by unfold isIfaceL; infer_instance
  | x :: xs, v :: vs => by
    have := isIface_pers x v
    have := isIfaceL_pers xs vs
    unfold isIfaceL; infer_instance
  | [], _ :: _ => by unfold isIfaceL; infer_instance
  | _ :: _, [] => by unfold isIfaceL; infer_instance
theorem isIfaceM_pers : ∀ (M : GMap GoString GoInterface) (kvs : List (GoString × UVal)),
    Persistent (isIfaceM (GF := GF) M kvs)
  | M, [] => by unfold isIfaceM; infer_instance
  | M, (k, v) :: kvs => by
    have := fun x => isIface_pers x v
    have := isIfaceM_pers M kvs
    unfold isIfaceM; infer_instance
end

attribute [instance] isIface_pers isIfaceL_pers isIfaceM_pers

/-! ## Wrappers -/

/-- The wrapper type. -/
abbrev vuPtrTy : go.GoType := go.GoType.PointerType value.valueUnstructured.ty

theorem isValF_intro (p : Loc) (dq : DFrac) (i : GoInterface) (x : UVal) :
    p ↦{dq} value.valueUnstructured.mk i ∗ isIface (GF := GF) i x ⊢
      isValF (interface.mkOk vuPtrTy #p) dq x := by
  iintro ⟨Hp, Hi⟩
  iunfold isValF
  iexists p, i
  iframe
  ipureintro
  rfl

theorem isValF_elim (p : Loc) (dq : DFrac) (x : UVal) :
    isValF (GF := GF) (interface.mkOk vuPtrTy #p) dq x ⊢
      ∃ i, p ↦{dq} value.valueUnstructured.mk i ∗ isIface (GF := GF) i x := by
  iintro Hv
  iunfold isValF at Hv
  icases Hv with ⟨%p', %i, %Heq, Hp, Hi⟩
  obtain rfl : p = p' := by simpa [intoVal_eq_iff] using Heq
  iexists i
  iframe

end lemmas

end smd
end EtcdGrove
end Perennial
