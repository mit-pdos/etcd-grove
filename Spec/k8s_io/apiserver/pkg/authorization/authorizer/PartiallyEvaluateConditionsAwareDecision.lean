/-
`PartiallyEvaluateConditionsAwareDecision(ctx, d, data, fn)` (`evaluate.go`): a well-formed
decision no deeper and no larger (`Dec.size`) than `d`, its names `d`'s, for a well-formed `d` and a partial
evaluation function that can be called (recursively through `d`'s unions). `d` fits `strings.Join`
(`Dec.foldFits`): its unions are rebuilt with `ToDecision` (fmt stage 1). Lean-first (no Rocq
counterpart).
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
abbrev PartiallyEvaluateConditionsAwareDecision.spec : Prop :=
  ∀ (ctx : GoInterface) (d : ConditionsAwareDecision) (m : Dec) (data : GoInterface) (f : GoFunc)
    (N : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗ isDecision d m ∗ ⌜m.WF⌝ ∗
      decNames N d m ∗ ⌜Dec.foldFits N m⌝ ∗ maybeEvalFnOk f }}
    (App (App (App (App (Val (@! PartiallyEvaluateConditionsAwareDecision)) (Val #ctx)) (Val #d))
      (Val #data)) (Val #f))
  {{ (d' : ConditionsAwareDecision), RET #d'; isWFDecisionBnd m.depth m.size N d' }}

end spec

end authorizer
end EtcdGrove
end Perennial
