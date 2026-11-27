/- Lean-first (no Rocq counterpart). `awaitProgress(wch, evs)` (`examples/etcd/dist/client/watch.go`):
copy of the cache example's `awaitProgress` (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/cache/awaitProgress.lean`),
at the dist package's copy in `watch.go`: the same triple (over `cacheCollect`'s `collectOk`), the
function and package initializer the dist package's.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.cacheCollect

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

/-- See the file header. -/
abbrev awaitProgress.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (γk : client.KMNames) (P : List (GoString × GoString)) (wch : Loc)
    (γ : CacheWatchNames) (rangeEnd : GoString) (upTo : w64) (sl : GoSlice) (evs : List etcd_cache.cev)
    (rs : List RespModel),
  γk.W = etcd_watch.wkW P → (∀ kv ∈ P, etcd_cache.ckPfx <+: kv.1) →
  (∀ kv ∈ P, keyPredForRange etcd_cache.ckPfx rangeEnd kv.1 = true) →
  (∀ r ∈ rs, r.canceled = false) → evs.length = (eventsOf rs).length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      isCacheWatchChan wch γ (etcdStepCert (EM := client.etcdModelOfKV γk) etcd_cache.ckPfx)
        (some (keyPredForRange etcd_cache.ckPfx rangeEnd)) (W64 2) ∗
      cacheWatchConsumer γ (etcdStepCert (EM := client.etcdModelOfKV γk) etcd_cache.ckPfx)
        (some (keyPredForRange etcd_cache.ckPfx rangeEnd)) (W64 2) rs ∗
      client.kmInv γk ∗ sl ↦* evs ∗ ownSliceCap etcd_cache.cev sl (DFrac.own 1) ∗
      collectOk γk P upTo evs }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.awaitProgress)) (Val #wch))
      (Val #sl))
  {{ (p : w64) (sl' : GoSlice) (ok : Bool), RET (PairV (PairV #p #sl') #ok);
      ⌜ok = true⌝ -∗ ∃ evs' : List etcd_cache.cev, sl' ↦* evs' ∗ collectOk γk P upTo evs' ∗
        ⌜sint.Z p ≤ 1 + evs'.length⌝ }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
