/-
`demux.resyncLoop(ctx)` (`cache/demux.go`). Lean-first (no Rocq counterpart); see `InvDemux.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvDemux

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `d.resyncLoop(ctx)`, with a demux token and a handle on its notifier: on each tick of its timer
(`time.NewTimer(d.resyncInterval)`, Perennial's trust boundary), it resyncs the lagging watchers
(`resyncLaggingWatchers`, which keeps the delivery invariant) and notifies `d.resynced`; it returns
`()` once `ctx` is done, with both tokens. -/
abbrev demux.resyncLoop.spec : Prop :=
  ∀ (d : Loc) (γd : DemuxNames) (cap : Nat) (C : DemuxCert GF) (γn : NotifierNames)
    (ctx : GoInterfaceOk) (s : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isDemux d γd cap C ∗
      demuxHandle d γd cap C ∗ demuxResyncHandle d γn ∗ context.isContext ctx s }}
    (App (Val (d @!! go.GoType.PointerType demux.ty @!! go!"resyncLoop"))
      (Val #(GoInterface.ok ctx)))
  {{ RET #(); demuxHandle d γd cap C ∗ demuxResyncHandle d γn }}

end spec

end EtcdGrove
end Perennial
