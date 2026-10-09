/-
`Cache.get(ctx)` (`cache/cache.go`): the bootstrap `Get` of the watch loop. Lean-first (no Rocq
counterpart); see `InvCache.lean` and `InvEtcd.lean`.
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

/-- `c.get(ctx)`, by the store's writer, whose state is `st`: the client's prefix get, then
`store.Restore(resp.Kvs, resp.Header.Revision)`. Either the client's error and `nil` (the store
unchanged), or the response and `nil`: the header revision `R` is one at which etcd's state under
the prefix is the map `m` the store now holds (`restoreState R m`, synced).

`Restore` needs `R` at least the store's latest revision (finding 4: it does not check it): the
writer knows etcd has reached the latest revision (`storeWriter`'s certificate, `etcdReached`),
and the client's get is linearizable (`isEtcdKV`: a non-serializable get returns at least any
revision etcd is known to have reached), and also bounds `R` below `2 ^ 63 - 1`. -/
abbrev Cache.get.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (ctx : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) (st : StoreState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ context.isContext ctx s ∗
      storeWriter cf.store cf.γs cf.scap (etcdCert cf.pfx) etcdReached st }}
    (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"get")) (Val #(GoInterface.ok ctx)))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ storeWriter cf.store cf.γs cf.scap (etcdCert cf.pfx) etcdReached st) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ (R : w64) (m : KvMap), getRespRev resp R ∗
        storeWriter cf.store cf.γs cf.scap (etcdCert cf.pfx) etcdReached (restoreState R m) ∗
        isEtcdKvs R cf.pfx (restoreState R m).latest ∗ storeRevLb cf.γs R ∗
        ⌜sint.Z st.latestRev ≤ sint.Z R ∧ sint.Z R < 2 ^ 63 - 1⌝) }}

end spec

end EtcdGrove
end Perennial
