/-
`Cache.WaitForRevision(ctx, rev)` (`cache/cache.go`). Lean-first (no Rocq counterpart); see
`InvCache.lean`.
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

/-- `c.WaitForRevision(ctx, rev)`, by a reader of the store (`cacheReader`, given back): `nil`
once the store's latest revision is at least `rev` (`storeRevLb`), or the context's (non-nil)
error once it is done. It polls the store every 10 ms (`time.After`). -/
abbrev Cache.WaitForRevision.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (ctx : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ context.isContext ctx s ∗ cacheReader cf }}
    (App (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"WaitForRevision"))
      (Val #(GoInterface.ok ctx))) (Val #rev))
  {{ (err : GoInterface), RET #err; cacheReader cf ∗
      ((⌜err = GoInterface.nil⌝ ∗ storeRevLb cf.γs rev) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ □ s.PDone ∗ context.ContextClosed s.Done_gn)) }}

end spec

end EtcdGrove
end Perennial
