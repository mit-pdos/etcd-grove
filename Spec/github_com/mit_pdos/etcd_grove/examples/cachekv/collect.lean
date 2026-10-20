/- Lean-first (no Rocq counterpart).

`collect(wch, upTo)` (cachekv.go): reads the channel of a cache watch of the prefix from revision
`2` (`isCacheWatchChan` for etcd's certificates at the server's model, the key filter of
`[ckPfx, rangeEnd)`, nothing received yet) of a server of watchkv's workload
(`γr.kv.wl = watchkv.workload P`, the plan's keys under the prefix and in the filter) until an
event at `upTo` or above; with `true` the events read are the puts at revisions `2, 3, ...`, each
of a key and value of the plan (`P`) and the store's put at its revision (`watchkv.revAt`), at
least up to `upTo` (watchkv's `collect`, through the cache).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.cachekv.CacheFacts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver github_com.mit_pdos.etcd_grove.examples.cachekv

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.cachekv.Assumptions]

/-- What `collect` returns with `true`: the events, as the file header says. -/
def collectOk [go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions] (E : apply.AEnv GF)
    (P : List (GoString × GoString)) (upTo : w64) (evs : List cev) : IProp GF :=
  iprop(⌜(upTo = W64 0 ∨ sint.Z upTo ≤ 1 + evs.length) ∧ evs.length + 1 < 2 ^ 63 ∧
      ∀ (i : Nat) (e : cev), evs[i]? = some e →
        e.put' = true ∧ sint.Z e.rev' = 2 + i ∧ (e.key', e.val') ∈ P⌝ ∗
    □ ∀ (i : Nat) (e : cev), ⌜evs[i]? = some e⌝ -∗ watchkv.revAt E (2 + i) e.key' e.val')

/-- See the file header. -/
abbrev collect.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (E : apply.AEnv GF) (γr : ReadNames) (P : List (GoString × GoString)) (wch : Loc)
    (γ : CacheWatchNames) (rangeEnd : GoString) (upTo : w64),
  γr.kv.wl = watchkv.workload P → γr.kv.log0 = [[], []] → (∀ kv ∈ P, ckPfx <+: kv.1) →
  (∀ kv ∈ P, keyPredForRange ckPfx rangeEnd kv.1 = true) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.cachekv ∗
      isCacheWatchChan wch γ (etcdStepCert (EM := v3rpc.etcdModelOfServer E) ckPfx)
        (some (keyPredForRange ckPfx rangeEnd)) (W64 2) ∗
      cacheWatchConsumer γ (etcdStepCert (EM := v3rpc.etcdModelOfServer E) ckPfx)
        (some (keyPredForRange ckPfx rangeEnd)) (W64 2) [] ∗
      srvKVInvs E γr ∗ mvcc.idxCert E.γ.idx [[], []] }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.cachekv.collect)) (Val #wch))
      (Val #upTo))
  {{ (sl : GoSlice) (ok : Bool), RET (PairV #sl #ok);
      ⌜ok = true⌝ -∗ ∃ evs : List cev, sl ↦* evs ∗ collectOk E P upTo evs }}

end spec

end cachekv
end EtcdGrove
end Perennial
