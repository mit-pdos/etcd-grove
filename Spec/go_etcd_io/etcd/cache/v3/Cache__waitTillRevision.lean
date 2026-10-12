/-
`Cache.waitTillRevision(ctx, rev)` (`cache/cache.go`). Lean-first (no Rocq counterpart); see
`InvCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `c.waitTillRevision(ctx, rev)`, by a reader of the store (`cacheReader`, given back): `nil`
only once the store's latest revision is at least `rev` (`storeRevLb`), else the value of
`ErrCacheTimeout` or the context's error once it is done (`waitResult`). It waits on the
store's `revCond` under a read lock, with a goroutine that broadcasts on it at the timeout or
when the context is done. -/
abbrev Cache.waitTillRevision.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (ctx : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ context.isContext ctx s ∗ cacheReader cf }}
    (App (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"waitTillRevision"))
      (Val #(GoInterface.ok ctx))) (Val #rev))
  {{ (err : GoInterface), RET #err; cacheReader cf ∗ waitResult cf s rev err }}

end spec

end EtcdGrove
end Perennial
