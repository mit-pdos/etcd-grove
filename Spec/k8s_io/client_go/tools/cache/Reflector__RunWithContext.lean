/-
`(*Reflector).RunWithContext(ctx)` (`reflector.go`): `r.delayHandler.Until(ctx, true, true, …)`:
`ListAndWatchWithContext(ctx)` again and again (an error to the watch error handler), until `ctx`
is done. From the reflector's state at any last version. Returns (partial correctness).
Lean-first; the DaemonSet run's track A. 
-/
module

public import Spec.k8s_io.client_go.tools.cache.Reflector__ListAndWatchWithContext

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

/-- **`r.RunWithContext(ctx)`**: see the file header. -/
abbrev Reflector.RunWithContext.spec : Prop :=
  ∀ (r f : Loc) (lw : GoInterfaceOk) (et : reflect.Type') (dh : GoFunc) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (dch : GoChan) (γd : ChanNames) (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (res : Res)
    (γf : FifoNames) (γt : TsNames) (γi : InfNames) (n : Option Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ ⌜rvuTyOk ∧ bmTyOk⌝ ∗ reflFixed r f lw et dh ∗
      reflEnv γa cfg res γf γt γi f lw et ∗ context.isContext ctx cs ∗ stableCtx ctx dch γd ∗
      errIsOk ∗ reflSt r γa γi n }}
    (App (Val (r @!! go.GoType.PointerType Reflector.ty @!! go!"RunWithContext"))
      (Val #(GoInterface.ok ctx)))
  {{ RET #(); True }}

end spec

end cache
end EtcdGrove
end Perennial
