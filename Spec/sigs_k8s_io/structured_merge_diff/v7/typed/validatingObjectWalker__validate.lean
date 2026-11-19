/-
`validatingObjectWalker.validate(prefixFn)` (internal; recursive through `resolveSchema` and the
walker's `doScalar`/`doList`/`doMap`): no error exactly when the walker's value conforms to its
type (`conforms`); the errors are prefixed by `prefixFn()` (`prefixOk`). The value is lent (any
share).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG": the `typed` rows).
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
abbrev typed.validatingObjectWalker.validate.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : VWSt) (dq : DFrac) (x : UVal) (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ vwOwn w sc S st ∗ isValF st.value dq x ∗ prefixOk f ∗ ⌜(S.find st.t.name).isSome⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker.ty @!! go!"validate")) (Val #f))
  {{ (errs : GoSlice), RET #errs; errsIff errs (conforms S st.t x) ∗ isValF st.value dq x ∗
      vwOwn w sc S st }}

end spec

end smd
end EtcdGrove
end Perennial
