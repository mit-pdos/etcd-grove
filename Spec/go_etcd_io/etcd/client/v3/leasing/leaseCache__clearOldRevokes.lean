/-
`leaseCache.clearOldRevokes(ctx)` (`client/v3/leasing/cache.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`lc.clearOldRevokes(ctx)`** (a goroutine): until the context is done, every second (write
lock) deletes some revocation times (those older than the backoff, by the clock). The client's
part of the invariant must allow it. -/
abbrev leaseCache.clearOldRevokes.spec : Prop :=
  ∀ (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString) (X : LeaseCacheSt → Qp → IProp GF)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeaseCache lc γ pfx X ∗ context.isContext ctx cs ∗
      □ (∀ (st : LeaseCacheSt) (rv : GMap GoString time.Time), ⌜RevokesSub rv st.revokes⌝ -∗
          X st 1 ={⊤}=∗ X { st with revokes := rv } 1) }}
    (App (Val (lc @!! go.GoType.PointerType leaseCache.ty @!! go!"clearOldRevokes")) (Val #(GoInterface.ok ctx)))
  {{ RET #(); True }}

end spec

end leasing
end EtcdGrove
end Perennial
