/-
`txn.revokeFallback(fbResps)` (`client/v3/leasing/txn.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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

/-- A `*pb.ResponseOp` `p` of a get (read-only): its range response's key-values `kvs`. -/
def rangeKvsRO (p : Loc) (kvs : List EtcdKv) : IProp GF :=
  iprop(∃ (w rr : Loc) (sl : GoSlice) (ps : List Loc), ⌜p ≠ null ∧ rr ≠ null⌝ ∗
    structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
      interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseRange.ty) #w ∗
    structFieldRef etcdserverpb.ResponseOp_ResponseRange go!"ResponseRange" w ↦□ rr ∗
    structFieldRef etcdserverpb.RangeResponse go!"Kvs" rr ↦□ sl ∗ sl ↦*□ ps ∗ kvPtrsAt ps kvs)

/-- **`txn.revokeFallback(fbResps)`** for the responses of the fallback gets (read-only): revokes
the lease keys each lists (`revokeLeaseKvs`): an error, or `nil`. The context must be
cancelable. -/
abbrev txnLeasing.revokeFallback.spec : Prop :=
  ∀ (txn lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (dq : DFrac) (sl : GoSlice) (ps : List Loc)
    (kvss : List (List EtcdKv)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ structFieldRef txnLeasing go!"lkv" txn ↦{dq} lkv ∗
      structFieldRef txnLeasing go!"ctx" txn ↦{dq} GoInterface.ok ctx ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx ∗
      sessionReady γ ∗ context.isContext ctx cs ∗ context.isCancelCtxCtx ctx cs ∗
      sl ↦*□ ps ∗ ⌜ps.length = kvss.length⌝ ∗
      [∗list] i ↦ p ∈ ps, ∃ kvs, ⌜kvss[i]? = some kvs⌝ ∗ rangeKvsRO p kvs }}
    (App (Val (txn @!! go.GoType.PointerType txnLeasing.ty @!! go!"revokeFallback")) (Val #sl))
  {{ (err : GoInterface), RET #err; structFieldRef txnLeasing go!"lkv" txn ↦{dq} lkv ∗
      structFieldRef txnLeasing go!"ctx" txn ↦{dq} GoInterface.ok ctx ∗ lkvReader lkv γ pfx }}

end spec

end leasing
end EtcdGrove
end Perennial
