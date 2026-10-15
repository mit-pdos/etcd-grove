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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `c.get(ctx)`, by the holder of the cache's revision bound (`cacheBound`, at `B`): the client's
prefix get, then `store.Restore(resp.Kvs, resp.Header.Revision)`. Either the client's error and
`nil` (nothing changed; the error's `Error()` returns some string, `errStrOk`), or the response and `nil`: the header revision `R` is at least `B` and
below `2 ^ 63 - 1`, the bound is now `R`, and the store's latest revision and newest snapshot are
at least `R` (the newest snapshot, its latest map, etcd's state at it: the store's certificate).

`Restore` needs `R` at least every revision the store can be at, now or after another writer's
pending `Apply` (finding 4: `Restore` does not check it): all of them are at most the bound
(`cacheRev`, the store's revision certificate), etcd has reached the bound (`cacheBound`), and the
client's get is linearizable (`isEtcdKV`: a non-serializable get returns at least any revision
etcd is known to have reached). -/
abbrev Cache.get.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (ctx : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) (B : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ context.isContext ctx s ∗ cacheBound cf B }}
    (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"get")) (Val #(GoInterface.ok ctx)))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ cacheBound cf B ∗ errStrOk err) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ R : w64, getRespRev resp R ∗ cacheBound cf R ∗
        storeRevLb cf.γs R ∗ storeSnapLb cf.γs R ∗
        ⌜sint.Z B ≤ sint.Z R ∧ sint.Z R < 2 ^ 63 - 1⌝) }}

end spec

end EtcdGrove
end Perennial
