/-
`Cache.WaitReady(ctx)` (`cache/cache.go`). Lean-first (no Rocq counterpart); see `InvCache.lean`.
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

/-- `c.WaitReady(ctx)`: `c.ready.WaitReady(ctx)`, `nil` once ready (in an epoch at least
`e0`) or a non-nil error once the context is done. -/
abbrev Cache.WaitReady.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap e0 : Nat)
    (ctx : GoInterfaceOk) (s : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ readyEpochLb γr e0 ∗ context.isContext ctx s }}
    (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"WaitReady")) (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; readyWaitResult γr e0 s id err }}

end spec

end EtcdGrove
end Perennial
