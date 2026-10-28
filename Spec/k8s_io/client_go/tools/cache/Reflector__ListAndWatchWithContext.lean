/-
`(*Reflector).ListAndWatchWithContext(ctx)` (`reflector.go:470`): with watch-list off, `list`, then
`watchWithResync` from the list's version; a list's error returned. Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md`, fifth round. From the reflector's state at any last version `n`: it
returns with the reflector's state at some version (a list's or a later event's: `some k`, or `n`
again after a failed list), or the context seen done.
-/
module

public import Spec.k8s_io.client_go.tools.cache.Reflector__watch
public import Spec.k8s_io.client_go.tools.cache.Reflector__list

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

/-- **The reflector's state after a `ListAndWatch`**: at some version, or at its last `n` (a failed
list), or the context seen done. -/
def lwPost (r : Loc) (γa : ApiNames) (γi : InfNames) (n : Option Nat) (dch : GoChan)
    (γd : ChanNames) : IProp GF :=
  iprop((∃ k, reflSt r γa γi (some k)) ∨ reflSt r γa γi n ∨ ctxSeen dch γd)

/-- **`r.ListAndWatchWithContext(ctx)`**: see the file header. -/
abbrev Reflector.ListAndWatchWithContext.spec : Prop :=
  ∀ (r f : Loc) (lw : GoInterfaceOk) (et : reflect.Type') (dh : GoFunc) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (dch : GoChan) (γd : ChanNames) (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (res : Res)
    (γf : FifoNames) (γt : TsNames) (γi : InfNames) (n : Option Nat),
  rvuTyOk → bmTyOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ reflFixed r f lw et dh ∗
      reflEnv γa cfg res γf γt γi f lw et ∗ context.isContext ctx cs ∗ stableCtx ctx dch γd ∗
      errIsOk ∗ reflSt r γa γi n }}
    (App (Val (r @!! go.GoType.PointerType Reflector.ty @!! go!"ListAndWatchWithContext"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; lwPost r γa γi n dch γd }}

end spec

end cache
end EtcdGrove
end Perennial
