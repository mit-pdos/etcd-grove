/-
`(*Reflector).startResync(ctx, resyncerrc)` (`reflector.go:514`): resync the store every resync
period until the context is done. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md`, fifth round.
Stated for resync period `0` (`Main`'s informers): the resync channel is `nil`, so the loop waits for
the context and returns; it never sends on `resyncerrc` (which `errChOk` relies on) nor calls the
store.
-/
module

public import Spec.k8s_io.client_go.tools.cache.Reflector__resyncChan

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache apimodel informer

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`r.startResync(ctx, resyncerrc)`** with resync period `0`: returns once `ctx` is done. -/
abbrev Reflector.startResync.spec : Prop :=
  ∀ (r f : Loc) (lw : GoInterfaceOk) (et : reflect.Type') (dh : GoFunc) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (errCh : GoChan),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ reflFixed r f lw et dh ∗
      context.isContext ctx cs }}
    (App (App (Val (r @!! go.GoType.PointerType Reflector.ty @!! go!"startResync"))
      (Val #(GoInterface.ok ctx))) (Val #errCh))
  {{ RET #(); True }}

end spec

end cache
end EtcdGrove
end Perennial
