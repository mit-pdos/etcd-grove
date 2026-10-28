/-
`(*Reflector).watchWithResync(ctx, w)` (`reflector.go:539`): `watch` with the resync goroutine
(`startResync` under a child context, cancelled and waited for on return). Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md`, fifth round. Stated as `watch` (`w` nil, after a list); the resync
error channel is fresh and, with resync period `0`, never sent on (`errChOk`); the context is the
reflector's (`isContext` for `context.WithCancel`, `stableCtx` for `watch`). Named hypothesis:
`wait.Group.Start` (names-only).
-/
module

public import Spec.k8s_io.client_go.tools.cache.Reflector__watch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache apimodel informer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`r.watchWithResync(ctx, nil)`**: as `watch`. -/
abbrev Reflector.watchWithResync.spec : Prop :=
  ∀ (r f : Loc) (lw : GoInterfaceOk) (et : reflect.Type') (dh : GoFunc) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (dch : GoChan) (γd : ChanNames) (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (res : Res)
    (γf : FifoNames) (γt : TsNames) (γi : InfNames) (k : Nat),
  rvuTyOk → bmTyOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ reflFixed r f lw et dh ∗
      reflEnv γa cfg res γf γt γi f lw et ∗ context.isContext ctx cs ∗ stableCtx ctx dch γd ∗
      errIsOk ∗ (reflSt r γa γi (some k) ∨ ctxSeen dch γd) }}
    (App (App (Val (r @!! go.GoType.PointerType Reflector.ty @!! go!"watchWithResync"))
      (Val #(GoInterface.ok ctx))) (Val #(interface.nil : GoInterface)))
  {{ (err : GoInterface), RET #err; (∃ k', reflSt r γa γi (some k')) ∨ ctxSeen dch γd }}

end spec

end cache
end EtcdGrove
end Perennial
