/-
`leaseCache.NotifyOps(ops)` (`client/v3/leasing/cache.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
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

/-- **`lc.NotifyOps(ops)`**: for each get, the waiter channel of its key's entry, if any (`notify`):
channels one may receive from. -/
abbrev leaseCache.NotifyOps.spec : Prop :=
  ∀ (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString) (X : LeaseCacheSt → Qp → IProp GF)
    (sl : GoSlice) (os : List OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeaseCache lc γ pfx X ∗ leaseCacheReader lc γ pfx X ∗ opsAt sl os }}
    (App (Val (lc @!! go.GoType.PointerType leaseCache.ty @!! go!"NotifyOps")) (Val #sl))
  {{ (sl' : GoSlice), RET #sl'; leaseCacheReader lc γ pfx X ∗
      ∃ cs : List GoChan, sl' ↦* cs ∗ ownSliceCap GoChan sl' (DFrac.own 1) ∗
        ([∗list] c ∈ cs, waitcOk c) }}

end spec

end leasing
end EtcdGrove
end Perennial
