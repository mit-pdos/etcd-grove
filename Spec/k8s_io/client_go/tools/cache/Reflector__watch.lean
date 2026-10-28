/-
`(*Reflector).watch(ctx, w, resyncerrc)` (`reflector.go:561`): the reflector's watch loop: until the
context is done, watch from the last synced version (`LastSyncResourceVersion`) and hand the watch
to `handleWatch`, re-watching after a watch closes, backing off after a retriable error, returning
after any other (the caller relists). Lean-first; phase 4 of `notes/k8s-daemonset-plan.md`, fifth
round.

Stated for the reflector of an informer of the model API server's resource `res`, called as
`ListAndWatchWithContext` calls it with watch-list off (`w` nil, after a successful `list`): from the
reflector's state at a positive last version `k` (a list's), every event the model's watch delivers
goes to the FIFO through the informer invariant (`watch_evStepOk`: each change the log's next after
the reflector's last version, each bookmark quiet), and the reflector's last version follows. Or
from a context seen done (`list` returned on `ctx.Done()` and its listing goroutine kept the
reflector's fields): `watch` returns at once. It returns either way with the reflector's state at
some positive version, or the context seen done.

Premises besides the reflector's: `rvuTyOk` (`*RealFIFO` is not a `ResourceVersionUpdater`),
`errIsOk` (`errors.Is` returns), Go's `int64(f)` (`Float64ToInt64Semantics`, the watch timeout).
-/
module

public import Proof.k8s_io.client_go.tools.cache.RefInf
public import Spec.k8s_io.client_go.tools.cache.controller__processLoop

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

/-- **The reflector's environment** (persistent): the informer invariant, the FIFO with the
informer's object contract, the list-watch over the model's resource `res`, the expected type its
objects', every state's keys good. -/
def reflEnv (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (res : Res) (γf : FifoNames) (γt : TsNames) (γi : InfNames) (f : Loc) (lw : GoInterfaceOk)
    (et : reflect.Type') : IProp GF :=
  iprop(infInv γa res γf γt γi ∗ isFIFO f γf (infObj γi res) ∗ lwOk lw γa cfg res ∗
    typeOfOk et res ∗ keysOk γa)

instance reflEnv_persistent (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (res : Res)
    (γf : FifoNames) (γt : TsNames) (γi : InfNames) (f : Loc) (lw : GoInterfaceOk)
    (et : reflect.Type') : Persistent (reflEnv (GF := GF) γa cfg res γf γt γi f lw et) := by
  unfold reflEnv; infer_instance

/-- **`r.watch(ctx, nil, resyncerrc)`**: see the file header. -/
abbrev Reflector.watch.spec : Prop :=
  ∀ (r f : Loc) (lw : GoInterfaceOk) (et : reflect.Type') (dh : GoFunc) (ctx : GoInterfaceOk)
    (dch : GoChan) (γd : ChanNames) (errCh : GoChan) (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (res : Res)
    (γf : FifoNames) (γt : TsNames) (γi : InfNames) (k : Nat),
  rvuTyOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ reflFixed r f lw et dh ∗
      reflEnv γa cfg res γf γt γi f lw et ∗ stableCtx ctx dch γd ∗ errChOk errCh ∗ errIsOk ∗
      (reflSt r γi (some k) ∨ ctxSeen dch γd) }}
    (App (App (App (Val (r @!! go.GoType.PointerType Reflector.ty @!! go!"watch"))
      (Val #(GoInterface.ok ctx))) (Val #(interface.nil : GoInterface))) (Val #errCh))
  {{ (err : GoInterface), RET #err; (∃ k', reflSt r γi (some k')) ∨ ctxSeen dch γd }}

end spec

end cache
end EtcdGrove
end Perennial
