/- Lean-first (no Rocq counterpart).

`collect(wch, upTo)` (etcd_cache.go): reads the channel of a cache watch of the prefix from revision
`2` (`isCacheWatchChan` for etcd's certificates at the clients' model of etcd over its KV state,
`client.etcdModelOfKV γk`, the key filter of `[ckPfx, rangeEnd)`, nothing received yet), the
adapter's invariant `client.kmInv γk` holding the plan's fact (`γk.W = etcd_watch.wkW P`: every
change of the KV is a put of the plan, whose keys are under the prefix and in the filter), until an
event at `upTo` or above; with `true` the events read are the puts at revisions `2, 3, ...`, each
of a key and value of the plan (`P`) and the put at its revision of a state the client saw
(`etcdstart.kmRevAt γk`), at least up to `upTo` (watchkv's `collect`, through the cache); and
(2026-11-03, for `awaitProgress`) the slice's capacity and the channel's consumer, with the
responses `rs` received, none a cancel, as many events in `rs` as returned. (Until
2026-10-26, D48, at the server's model, of a server of watchkv's workload.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.cache.CacheFacts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_cache

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver github_com.mit_pdos.etcd_grove.examples.etcd.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.cache.Assumptions]

/-- What `collect` returns with `true`: the events, as the file header says (the shared
`etcdstart.collectOk` at the adapter's `kmRevAt`). -/
abbrev collectOk (γk : client.KMNames)
    (P : List (GoString × GoString)) (upTo : w64) (evs : List cev) : IProp GF :=
  etcdstart.collectOk (etcdstart.kmRevAt γk) P upTo evs

/-- See the file header. -/
abbrev collect.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (γk : client.KMNames) (P : List (GoString × GoString)) (wch : Loc)
    (γ : CacheWatchNames) (rangeEnd : GoString) (upTo : w64),
  γk.W = etcd_watch.wkW P → (∀ kv ∈ P, ckPfx <+: kv.1) →
  (∀ kv ∈ P, keyPredForRange ckPfx rangeEnd kv.1 = true) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.cache ∗
      isCacheWatchChan wch γ (etcdStepCert (EM := client.etcdModelOfKV γk) ckPfx)
        (some (keyPredForRange ckPfx rangeEnd)) (W64 2) ∗
      cacheWatchConsumer γ (etcdStepCert (EM := client.etcdModelOfKV γk) ckPfx)
        (some (keyPredForRange ckPfx rangeEnd)) (W64 2) [] ∗
      client.kmInv γk }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.cache.collect)) (Val #wch))
      (Val #upTo))
  {{ (sl : GoSlice) (ok : Bool), RET (PairV #sl #ok);
      ⌜ok = true⌝ -∗ ∃ (evs : List cev) (rs : List RespModel),
        ⌜(∀ r ∈ rs, r.canceled = false) ∧ evs.length = (eventsOf rs).length⌝ ∗
        sl ↦* evs ∗ ownSliceCap cev sl (DFrac.own 1) ∗
        cacheWatchConsumer γ (etcdStepCert (EM := client.etcdModelOfKV γk) ckPfx)
          (some (keyPredForRange ckPfx rangeEnd)) (W64 2) rs ∗
        collectOk γk P upTo evs }}

end spec

end etcd_cache
end EtcdGrove
end Perennial
