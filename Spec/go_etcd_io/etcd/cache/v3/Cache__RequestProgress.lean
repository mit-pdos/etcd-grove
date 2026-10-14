/-
`Cache.RequestProgress(ctx)` (`cache/cache.go`). Lean-first (no Rocq counterpart); see `InvCache.lean`.
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
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `c.RequestProgress(ctx)`: `c.demux.BroadcastProgress()` (the context is ignored), then
`nil`. -/
abbrev Cache.RequestProgress.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ demuxHandle cf.demux γd cap (cacheCert cf) }}
    (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"RequestProgress")) (Val #ctx))
  {{ RET #GoInterface.nil; demuxHandle cf.demux γd cap (cacheCert cf) }}

end spec

end EtcdGrove
end Perennial
