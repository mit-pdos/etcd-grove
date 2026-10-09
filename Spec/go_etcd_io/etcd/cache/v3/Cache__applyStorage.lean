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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `c.applyStorage(storeW)`, by the store's writer (state `st`, synced, its latest map etcd's
state at `R`), for the store watcher `storeW` (no key filter) the demux delivers to from `R + 1`
on (`demuxPub`, start `R + 1`), of which it is the consumer: it applies every response it receives
(`store.Apply`) until the internal context is done or the channel is closed (`nil`), or `Apply`
fails (its error). Every snapshot `Apply` appends is certified (`snapCerts (etcdCert pfx)`): the
batches the demux delivers come with the certificates of etcd's steps (`demuxPub`), chained from
the store's map's revision, and `isEtcdKvs_step` turns the map and a step into etcd's state at the
batch's revision. -/
abbrev Cache.applyStorage.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (w : Loc) (γw : WatcherNames) (R : w64) (st : StoreState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗
      isWatcher w γw none (demuxPub (etcdStepCert cf.pfx) none (R + W64 1)) ∗
      watcherConsumer γw [] ∗
      storeWriter cf.store cf.γs cf.scap (etcdCert cf.pfx) st ∗ isEtcdKvs R cf.pfx st.latest ∗
      ⌜st.Synced ∧ 0 ≤ sint.Z R ∧ sint.Z R < 2 ^ 63 - 1⌝ }}
    (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"applyStorage")) (Val #w))
  {{ (err : GoInterface), RET #err;
      ∃ st' : StoreState, storeWriter cf.store cf.γs cf.scap (etcdCert cf.pfx) st' }}

end spec

end EtcdGrove
end Perennial
