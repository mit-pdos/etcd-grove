/-
`Cache.applyStorage(storeW)` (`cache/cache.go`): the store's side of the watch loop. Lean-first
(no Rocq counterpart); see `InvCache.lean`, `InvEtcd.lean`.
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
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `c.applyStorage(storeW)`, by any goroutine (the store has any number of writers:
`isStoreWriter`, in `isCacheFields`), for the store watcher `storeW` (no key filter) the demux
delivers to from `s` on (`demuxPub`, start `0 < s`), of which it is the consumer, when the store's
newest snapshot is at least `s - 1`: it applies every response it receives (`store.Apply`) until
the internal context is done or the channel is closed (`nil`), or `Apply` fails (its error, whose
`Error()` returns some string: `errStrOk`).

Each `Apply` is certified against whatever state the store is in (`storeApplyCert`): the batches
the demux delivers come with the certificates of etcd's steps (`demuxPub`), chained from the
watcher's previous batch (from a revision below `s` for the first), which the store's newest
snapshot has reached (this goroutine's lower bound, `storeSnapLb`: it applied that batch, or it
is below `s`); `isEtcdKvs_step` turns the newest snapshot's map, etcd's state at its revision, and
the step into etcd's state at the batch's revision, and `isEtcdKvs_applyBatch_ok` shows the
batch applies. A response at or below the store's latest revision (one buffered before a later
`Restore`, or replayed to a later iteration's watcher) is rejected by `validateRevisions` and
changes nothing: this is why another goroutine, still draining a stopped watcher, does no harm. -/
abbrev Cache.applyStorage.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (w : Loc) (γw : WatcherNames) (s : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗
      isWatcher w γw none (demuxPub (cacheCert cf) none s) ∗
      watcherConsumer γw [] ∗ storeSnapLb cf.γs (s - W64 1) ∗ ⌜0 < sint.Z s⌝ }}
    (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"applyStorage")) (Val #w))
  {{ (err : GoInterface), RET #err; errStrOk err }}

end spec

end EtcdGrove
end Perennial
