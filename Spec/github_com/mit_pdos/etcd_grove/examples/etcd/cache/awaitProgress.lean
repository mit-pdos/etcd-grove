/- Lean-first (no Rocq counterpart).

`awaitProgress(wch, evs)` (etcd_cache.go): reads the channel of `collect`'s cache watch (the
consumer `collect` gives back, its received responses `rs`, none a cancel) until a progress
notification, appending the events of the responses before it to `evs`; with `true`, the
notification's revision `p` and the events, still `collect`'s (`collectOk`: the puts at
revisions `2, 3, ...`), and `p` at most `1` plus their number, the last one's revision: the
cache's quiet fact at the watchkv server (`log_ck_progress`: every revision from `2` on a put
under the prefix, so a quiet one is not past the events sent).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.cache.collect

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

/-- See the file header. -/
abbrev awaitProgress.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (γk : client.KMNames) (P : List (GoString × GoString)) (wch : Loc)
    (γ : CacheWatchNames) (rangeEnd : GoString) (upTo : w64) (sl : GoSlice) (evs : List cev)
    (rs : List RespModel),
  γk.W = etcd_watch.wkW P → (∀ kv ∈ P, ckPfx <+: kv.1) →
  (∀ kv ∈ P, keyPredForRange ckPfx rangeEnd kv.1 = true) →
  (∀ r ∈ rs, r.canceled = false) → evs.length = (eventsOf rs).length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.cache ∗
      isCacheWatchChan wch γ (etcdStepCert (EM := client.etcdModelOfKV γk) ckPfx)
        (some (keyPredForRange ckPfx rangeEnd)) (W64 2) ∗
      cacheWatchConsumer γ (etcdStepCert (EM := client.etcdModelOfKV γk) ckPfx)
        (some (keyPredForRange ckPfx rangeEnd)) (W64 2) rs ∗
      client.kmInv γk ∗ sl ↦* evs ∗ ownSliceCap cev sl (DFrac.own 1) ∗ collectOk γk P upTo evs }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.cache.awaitProgress)) (Val #wch))
      (Val #sl))
  {{ (p : w64) (sl' : GoSlice) (ok : Bool), RET (PairV (PairV #p #sl') #ok);
      ⌜ok = true⌝ -∗ ∃ evs' : List cev, sl' ↦* evs' ∗ collectOk γk P upTo evs' ∗
        ⌜sint.Z p ≤ 1 + evs'.length⌝ }}

end spec

end etcd_cache
end EtcdGrove
end Perennial
