/-
`Cache.Watch(ctx, key, opts...)` (`cache/cache.go`): the end-to-end `Watch` theorem. Lean-first
(no Rocq counterpart); see `InvCache.lean` (`cacheWatchLog`, `cacheWatch_delivery`) and
`InvEtcd.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `c.Watch(ctx, key, opts...)`, with options whose closures have the model transformers `gs`
(`optsAt`; `OpWatch` must not panic), a demux token and a goroutine slot (`cacheWatchSlot`,
kept by the watch's goroutine), and a fraction `q` of the "open" token (`cacheOpen`, given back:
no `Close` runs meanwhile): returns a channel `rc` (`isCacheWatchChan`) with its consumer,
nothing received yet. For the request's `Op` `o := opWatchModel key gs`, every response received
on `rc` is, with those before it, a `cacheWatchLog` for the key filter
`keyPredForRange key o.rangeEnd` and the start revision `o.rev`: the `i`-th response of a log the
demux delivered to the watch's watcher (with its delivery facts and the certificates of etcd's
steps: `cacheWatch_delivery`), or the compaction's cancel response after all of it, or the single
cancel response of a rejected request (`validateWatch`); if `WaitReady` fails, `rc` is closed
with nothing in it. -/
abbrev Cache.Watch.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (ctx : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ context.isContext ctx s ∗ optsAt sl gs ∗
      ⌜¬ opWatchPanics key gs⌝ ∗ cacheWatchSlot cf γd cap ∗ cacheOpen cf q ∗ threadTok }}
    (App (App (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"Watch"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #sl))
  {{ (rc : Loc), RET #rc; cacheOpen cf q ∗ threadTok ∗ ∃ γ : CacheWatchNames,
      isCacheWatchChan rc γ (etcdStepCert cf.pfx)
        (some (keyPredForRange key (opWatchModel key gs).base.rangeEnd))
        (opWatchModel key gs).base.rev ∗
      cacheWatchConsumer γ (etcdStepCert cf.pfx)
        (some (keyPredForRange key (opWatchModel key gs).base.rangeEnd))
        (opWatchModel key gs).base.rev [] }}

end spec

end EtcdGrove
end Perennial
