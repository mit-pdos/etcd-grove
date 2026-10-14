/-
`Cache.WaitForNextResync(ctx)` (`cache/cache.go`). Lean-first (no Rocq counterpart); see `InvCache.lean`.
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

/-- `c.WaitForNextResync(ctx)` (`c.demux.WaitForNextResync(ctx)`), with a handle on the demux's
notifier (`New` hands them out) and a lower bound `k0` on its notifications: `nil` once a resync
loop iteration completed after the `k0`-th, or a non-nil error once the context is done. -/
abbrev Cache.WaitForNextResync.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (γn : NotifierNames) (k0 : Nat) (ctx : GoInterfaceOk) (s : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ demuxResyncHandle cf.demux γn ∗ notifierLb γn k0 ∗
      context.isContext ctx s }}
    (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"WaitForNextResync"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err;
      demuxResyncHandle cf.demux γn ∗ notifierWaitResult γn k0 s err }}

end spec

end EtcdGrove
end Perennial
