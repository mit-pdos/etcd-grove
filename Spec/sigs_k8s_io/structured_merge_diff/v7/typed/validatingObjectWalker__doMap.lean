/-
`validatingObjectWalker.doMap(t)` (internal; the `atomHandler` method for a map type): an
error for a value of another kind, none for `null`, else the entries (`visitMapItems`): no
error exactly when the value conforms.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG": the `typed` rows).

D10 (c) (2026-11-19, the Draft's integration): specified on conforming values only (the premise `conforms`, no error after): rejection is outside the scope, so the error paths (`errorf`, `fmt`) are not reached and no `fmt` spec is needed.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

/-- See the file header. -/
abbrev typed.validatingObjectWalker.doMap.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : VWSt) (dq : DFrac) (x : UVal) (tp : Loc) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ vwOwn w sc S st ∗ isValF st.value dq x ∗ isMapRep tp fs e rel ∗ ⌜S.find st.t.name = some (.map fs e rel)⌝ ∗ ⌜conforms S st.t x⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker.ty @!! go!"doMap")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValF st.value dq x ∗
      vwOwn w sc S st }}

end spec

end smd
end EtcdGrove
end Perennial
