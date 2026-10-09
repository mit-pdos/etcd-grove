/-
`Cache.watch(rev)` (`cache/cache.go`): the watch loop proper, between two `get`s. Lean-first (no
Rocq counterpart); see `InvCache.lean` and `InvEtcd.lean`.
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

/-- `c.watch(rev)`, by the demux's writer (`cacheWriter`, any state) and the store's writer (a
synced state `st` whose latest map is etcd's state at `R`, at most its latest revision, with
`0 < rev ≤ R + 1`): it initializes the demux at `rev` (`Init`), then loops: it registers a fresh
store watcher from `rev` (`newWatcher`, `Register`), starts `applyStorage` on it with the store's
writer, runs `watchEvents` with the demux's writer, unregisters the store watcher (which stops
it), and waits for `applyStorage` by receiving from `applyErr`; it returns the first non-nil error
of `watchEvents` or `applyStorage`.

The store's writer is the goroutine's from its start to the send or close on `applyErr`
(`isHandoff`), and comes back to the loop at the first receive from `applyErr`, in
`watchEvents`'s `select` or in the wait: no two writers of the store at once. On a `nil` from both,
the store's latest map is again etcd's state at a revision `R' ≥ R` (at most the latest revision),
which is what the next iteration's `applyStorage` needs (the demux replays from `rev ≤ R' + 1`).

It returns a non-nil error, and both writers, in some states. -/
abbrev Cache.watch.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (rev R : w64) (c0 : DemuxCore) (st : StoreState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ cacheWriter cf γd cap c0 ∗
      storeWriter cf.store cf.γs cf.scap (etcdCert cf.pfx) etcdReached st ∗ isEtcdKvs R cf.pfx st.latest ∗
      ⌜st.Synced ∧ 0 < sint.Z rev ∧ sint.Z rev ≤ sint.Z R + 1 ∧
        sint.Z R ≤ sint.Z st.latestRev⌝ }}
    (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"watch")) (Val #rev))
  {{ (err : GoInterface), RET #err; ⌜err ≠ GoInterface.nil⌝ ∗
      ∃ (c1 : DemuxCore) (st' : StoreState), cacheWriter cf γd cap c1 ∗
        storeWriter cf.store cf.γs cf.scap (etcdCert cf.pfx) etcdReached st' }}

end spec

end EtcdGrove
end Perennial
