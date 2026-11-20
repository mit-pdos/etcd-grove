/-
`ConditionsAwareDecisionDeny(reason, err)` (`conditions.go`): an unconditional Deny. Lean-first
(no Rocq counterpart).
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
abbrev ConditionsAwareDecisionDeny.spec : Prop :=
  ∀ (r : GoString) (e : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗
      utilerrors.errTreeOrNil e }}
    (App (App (Val (@! ConditionsAwareDecisionDeny)) (Val #r)) (Val #e))
  {{ (d : ConditionsAwareDecision), RET #d; isDecision d .deny }}

end spec

end authorizer
end EtcdGrove
end Perennial
