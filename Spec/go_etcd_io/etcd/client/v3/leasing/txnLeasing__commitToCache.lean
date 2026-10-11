/-
`txn.commitToCache(txnResp, userTxn)` (`client/v3/leasing/txn.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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

/-- **`txn.commitToCache(txnResp, userTxn)`** for the response of a transaction whose single
then-operation was `userTxn` (the user's transaction, nested, as the tree `t`): under the write
lock, applies the user's chosen operations to the cache (`delete` of each deleted key or cached
key in a deleted range, `Update` of each put key), at the response's header. -/
abbrev txnLeasing.commitToCache.spec : Prop :=
  ∀ (txn lkv : Loc) (γ : LeasingNames) (pfx : GoString) (dq : DFrac) (resp : Loc) (hdr : Loc)
    (hm : HdrM) (rsl : GoSlice) (p0 : Loc) (top : TxnOp) (res : TxnOpResult)
    (uv : go_etcd_io.etcd.client.v3.Op) (t : OpT),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ structFieldRef txnLeasing go!"lkv" txn ↦{dq} lkv ∗ isLeasingKV lkv γ pfx ∗
      structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ hdr ∗ hdrFull hdr hm ∗
      structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦□ rsl ∗ rsl ↦*□ [p0] ∗
      txnOpRespN p0 top res ∗ opTAtC false uv t ∗ ⌜t.txnOp = some top⌝ }}
    (App (App (Val (txn @!! go.GoType.PointerType txnLeasing.ty @!! go!"commitToCache")) (Val #resp)) (Val #uv))
  {{ RET #(); structFieldRef txnLeasing go!"lkv" txn ↦{dq} lkv }}

end spec

end leasing
end EtcdGrove
end Perennial
