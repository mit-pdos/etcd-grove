/-
`ResourceEventHandlerFuncs.OnAdd` (`controller.go`): calls `AddFunc` if it is not `nil`.
Lean-first; the DaemonSet run's track A (the controller's handlers are such structs).
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerApi

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI apimodel cache informer k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]
/-- **An optional handler function's contract**: from `P` to `Q`; the call `e` of the function `f`
when it is set, nothing when it is `nil`. -/
def optFnOk (f : GoFunc) (e : Expr) (P Q : IProp GF) : IProp GF :=
  if f = func.nil then iprop(P -∗ Q) else iprop(P -∗ WP e {{ fun _ => Q }})

/-- **`fs.OnAdd(…)`**: `fs.AddFunc(…)` if set, else nothing. -/
abbrev ResourceEventHandlerFuncs.OnAdd.spec : Prop :=
  ∀ (fs : ResourceEventHandlerFuncs) (o : GoInterface) (b : Bool) (P Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ P ∗ optFnOk fs.AddFunc' (App (Val #fs.AddFunc') (Val #o)) P Q }}
    (App (App (Val #(methods ResourceEventHandlerFuncs.ty go!"OnAdd" #fs)) (Val #o)) (Val #b))
  {{ RET #(); Q }}

end spec

end cache
end EtcdGrove
end Perennial
