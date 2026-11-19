/-
`validatingObjectWalker.visitListItems(t, list)` (internal): validates each item against the
element type (in a child walker); for an associative list, each item must have a key (else an
error, and the loop stops) and no key twice (duplicates not allowed): no error exactly when the
list conforms.

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
abbrev typed.validatingObjectWalker.visitListItems.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : VWSt) (tp : Loc) (e : TypeRef) (rel : ElemRel)
    (ks : List GoString) (ll : value.List') (vs : List UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ vwOwn w sc S st ∗ isListRep tp e rel ks ∗ isListV ll vs ∗
      ⌜S.find st.t.name = some (.list e rel ks) ∧ conforms S st.t (.list vs)⌝ }}
    (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker.ty @!! go!"visitListItems")) (Val #tp)) (Val #ll))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ vwOwn w sc S st }}

end spec

end smd
end EtcdGrove
end Perennial
