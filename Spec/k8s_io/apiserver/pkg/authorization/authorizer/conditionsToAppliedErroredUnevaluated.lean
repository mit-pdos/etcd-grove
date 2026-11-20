/-
`conditionsToAppliedErroredUnevaluated(conditions, evalCond, effect, desc)` (`evaluate.go`): a
reason, new slices of the errors and of the unevaluated conditions (some of `cs`). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI k8s_io.apiserver.pkg.authorization.authorizer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

/-- See the file header. -/
abbrev conditionsToAppliedErroredUnevaluated.spec : Prop :=
  ∀ (it : GoFunc) (cs : List GoInterface) (ev : GoFunc) (effect desc : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗ seqOk it cs ∗ ([∗list] c ∈ cs, isCondition c) ∗ evalCondOk ev }}
    (App (App (App (App (Val (@! conditionsToAppliedErroredUnevaluated)) (Val #it)) (Val #ev))
      (Val #effect)) (Val #desc))
  {{ (r : GoString) (es us : GoSlice), RET (PairV (PairV #r #es) #us);
      (∃ errs : List GoInterface, es ↦* errs) ∗
      (∃ uc : List GoInterface, us ↦* uc ∗ [∗list] c ∈ uc, isCondition c) }}

end spec

end authorizer
end EtcdGrove
end Perennial
