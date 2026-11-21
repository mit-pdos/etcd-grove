/-
`c.Evaluate(ctx, data, fn)` (`evaluate.go`): some decision word, reason and error, for any
evaluation function that can be called. Lean-first (no Rocq counterpart).
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
abbrev ConditionsMap.Evaluate.spec : Prop :=
  ∀ (c : ConditionsMap) (dn no al : List GoInterface) (ctx data : GoInterface) (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗ isConditionsMap c dn no al ∗ evalFnOk f }}
    (App (App (App (Val (c @!! ConditionsMap.ty @!! go!"Evaluate")) (Val #ctx)) (Val #data)) (Val #f))
  {{ (dec : w64) (r : GoString) (e : GoInterface), RET (PairV (PairV #dec #r) #e); True }}

end spec

end authorizer
end EtcdGrove
end Perennial
