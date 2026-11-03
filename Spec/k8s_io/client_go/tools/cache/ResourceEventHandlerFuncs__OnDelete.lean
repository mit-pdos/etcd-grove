/-
`ResourceEventHandlerFuncs.OnDelete` (`controller.go`): calls `DeleteFunc` if it is not `nil`.
Lean-first; the DaemonSet run's track A (the controller's handlers are such structs).
-/
module

public import Spec.k8s_io.client_go.tools.cache.ResourceEventHandlerFuncs__OnAdd

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

/-- **`fs.OnDelete(…)`**: `fs.DeleteFunc(…)` if set, else nothing. -/
abbrev ResourceEventHandlerFuncs.OnDelete.spec : Prop :=
  ∀ (fs : ResourceEventHandlerFuncs) (o : GoInterface) (P Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ P ∗ optFnOk fs.DeleteFunc' (App (Val #fs.DeleteFunc') (Val #o)) P Q }}
    (App (Val #(methods ResourceEventHandlerFuncs.ty go!"OnDelete" #fs)) (Val #o))
  {{ RET #(); Q }}

end spec

end cache
end EtcdGrove
end Perennial
