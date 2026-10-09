/-
`Cache.getWatch()` (`cache/cache.go`): one round of the watch loop, a `get` then a `watch`.
Lean-first (no Rocq counterpart); see `InvCache.lean` and `InvEtcd.lean`.
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

/-- `c.getWatch()`, by the demux's writer and the store's writer (any states): the client's
prefix get, restored into the store (`get`), then `watch` from the revision after the get's. It
returns a non-nil error (the get's, or the watch's) and both writers, in some states.

`get` needs etcd's linearizability for the store's latest revision (`isEtcdKVFrom`, see
`Cache.get`'s spec). -/
abbrev Cache.getWatch.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (c0 : DemuxCore) (st : StoreState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ cacheWriter cf γd cap c0 ∗
      storeWriter cf.store cf.γs cf.scap (etcdCert cf.pfx) st ∗
      isEtcdKVFrom cf.kv cf.pfx st.latestRev }}
    (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"getWatch")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err ≠ GoInterface.nil⌝ ∗
      ∃ (c1 : DemuxCore) (st' : StoreState), cacheWriter cf γd cap c1 ∗
        storeWriter cf.store cf.γs cf.scap (etcdCert cf.pfx) st' }}

end spec

end EtcdGrove
end Perennial
