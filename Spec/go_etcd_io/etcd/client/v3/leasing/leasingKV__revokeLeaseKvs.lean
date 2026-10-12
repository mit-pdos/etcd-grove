/-
`lkv.revokeLeaseKvs(ctx, kvs)` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- The largest create revision of the key-values `kvs` (signed), `0` if none: `revokeLeaseKvs`'s
`maxLeaseRev`. -/
def maxCreateRev (kvs : List EtcdKv) : w64 :=
  kvs.foldl (fun m v => if sint.Z m < sint.Z v.createRev then v.createRev else m) (W64 0)

/-- **`lkv.revokeLeaseKvs(ctx, kvs)`** for lease keys `kvs` (read-only `*KeyValue`s): revokes each
lease key not of this client's session (`revoke` of a get of its data key), and returns the largest
create revision (`maxCreateRev`), or an error. -/
abbrev leasingKV.revokeLeaseKvs.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (sl : GoSlice) (ps : List Loc) (kvs : List EtcdKv),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx ∗ sessionReady γ ∗ context.isContext ctx cs ∗
      context.isCancelCtxCtx ctx cs ∗ sl ↦*□ ps ∗ kvPtrsAt ps kvs }}
    (App (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"revokeLeaseKvs")) (Val #(GoInterface.ok ctx))) (Val #sl))
  {{ (maxRev : w64) (err : GoInterface), RET (PairV #maxRev #err); lkvReader lkv γ pfx ∗
      ⌜err ≠ GoInterface.nil ∨ (err = GoInterface.nil ∧ maxRev = maxCreateRev kvs)⌝ }}

end spec

end leasing
end EtcdGrove
end Perennial
