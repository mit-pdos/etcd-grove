/-
`conditionalProgressRequestor.run(ctx)` (`cache/progress_requestor.go`). Lean-first (no Rocq
counterpart); see `InvCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `p.run(ctx)`, the progress requestor's loop, with its clock (`isClock`) and notifier (the
client's `RequestProgress`, `isEtcdProgressNotifier`): it starts a goroutine that, once `ctx` is
done, sets `stopped` and signals `cond`; then, until stopped or `ctx` is done, it waits on `cond`
while there are no waiters and, at each tick of its timer, asks etcd for a progress notification
if there are waiters. It returns `()` (once stopped, or `ctx` done); everything it uses is
persistent. -/
abbrev conditionalProgressRequestor.run.spec : Prop :=
  ∀ (p : Loc) (n clk : GoInterfaceOk) (ri : time.Duration) (ctx : GoInterfaceOk)
    (s : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isProgressRequestor p ∗
      isPrRun p (GoInterface.ok n) (GoInterface.ok clk) ri ∗ isClock clk ∗
      isEtcdProgressNotifier n ∗ context.isContext ctx s }}
    (App (Val (p @!! go.GoType.PointerType conditionalProgressRequestor.ty @!! go!"run"))
      (Val #(GoInterface.ok ctx)))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
