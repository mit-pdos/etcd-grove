/-
`lkv.deleteRangeRPC(ctx, maxLeaseRev, key, end)` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- The `Op` of `deleteRangeRPC`'s delete, `OpDelete(key, WithRange(end))`. -/
def rangeDeleteOp (key e : GoString) : OpFull := opDeleteModel key [withRangeM e]

/-- **`lkv.deleteRangeRPC(ctx, maxLeaseRev, key, end)`**: deletes the range `[key, end)` in a
transaction guarded by every lease key of `[pfx ++ key, pfx ++ end)` created at or before
`maxLeaseRev`, then deletes the deleted keys' entries from the cache. Returns `(nil, err)` on an
error (the range is evicted: `EvictRange`, which evicts `key` alone, a finding), `(nil, nil)` if
the guard failed, or the delete (`deleteCommitted`). -/
abbrev leasingKV.deleteRangeRPC.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (maxLeaseRev : w64) (key e : GoString) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ context.isContext ctx cs ∗ etcdReached lo }}
    (App (App (App (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"deleteRangeRPC")) (Val #(GoInterface.ok ctx))) (Val #maxLeaseRev)) (Val #key)) (Val #e))
  {{ (dr : Loc) (err : GoInterface), RET (PairV #dr #err);
      ⌜dr = null⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ deleteCommitted lo (rangeDeleteOp key e) dr) }}

end spec

end leasing
end EtcdGrove
end Perennial
