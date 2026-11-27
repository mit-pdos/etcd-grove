/- Lean-first (no Rocq counterpart). `cacheCollect(wch, upTo)` (`examples/etcd/dist/client/watch.go`):
copy of the cache example's `collect` (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/cache/collect.lean`),
at the dist package's copy in `watch.go`: the same triple, the function and package initializer the
dist package's. `collectOk` is the cache example's (`etcd_cache.collectOk`), redeclared here with the
same body so that this spec imports no other spec.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.cache.CacheFacts

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

/-- What `cacheCollect` returns with `true` (the cache example's `etcd_cache.collectOk`): the shared
`etcdstart.collectOk` at the adapter's `kmRevAt`. -/
abbrev collectOk (γk : client.KMNames)
    (P : List (GoString × GoString)) (upTo : w64) (evs : List etcd_cache.cev) : IProp GF :=
  etcdstart.collectOk (etcdstart.kmRevAt γk) P upTo evs

/-- See the file header. -/
abbrev cacheCollect.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (γk : client.KMNames) (P : List (GoString × GoString)) (wch : Loc)
    (γ : CacheWatchNames) (rangeEnd : GoString) (upTo : w64),
  γk.W = etcd_watch.wkW P → (∀ kv ∈ P, etcd_cache.ckPfx <+: kv.1) →
  (∀ kv ∈ P, keyPredForRange etcd_cache.ckPfx rangeEnd kv.1 = true) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      isCacheWatchChan wch γ (etcdStepCert (EM := client.etcdModelOfKV γk) etcd_cache.ckPfx)
        (some (keyPredForRange etcd_cache.ckPfx rangeEnd)) (W64 2) ∗
      cacheWatchConsumer γ (etcdStepCert (EM := client.etcdModelOfKV γk) etcd_cache.ckPfx)
        (some (keyPredForRange etcd_cache.ckPfx rangeEnd)) (W64 2) [] ∗
      client.kmInv γk }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.cacheCollect)) (Val #wch))
      (Val #upTo))
  {{ (sl : GoSlice) (ok : Bool), RET (PairV #sl #ok);
      ⌜ok = true⌝ -∗ ∃ (evs : List etcd_cache.cev) (rs : List RespModel),
        ⌜(∀ r ∈ rs, r.canceled = false) ∧ evs.length = (eventsOf rs).length⌝ ∗
        sl ↦* evs ∗ ownSliceCap etcd_cache.cev sl (DFrac.own 1) ∗
        cacheWatchConsumer γ (etcdStepCert (EM := client.etcdModelOfKV γk) etcd_cache.ckPfx)
          (some (keyPredForRange etcd_cache.ckPfx rangeEnd)) (W64 2) rs ∗
        collectOk γk P upTo evs }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
