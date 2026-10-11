/-
`lkv.revoke(ctx, key, op)` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKV
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__tryModifyOp

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

/-- **`lkv.revoke(ctx, key, op)`**: commits `op` (`top`) guarded by the lease key `pfx ++ key`
created at or before this client's entry revision `rev` (or absent), else puts `"REVOKE"` into
the lease key (keeping its lease) and waits for the holder to give it up (`waitRescind`, no
promise). Returns an error, or (`nil` error) the committed `op` (`opCommitted`), or a response
that did not succeed (`notCommitted`). The context must be cancelable. -/
abbrev leasingKV.revoke.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (key : GoString) (opv : go_etcd_io.etcd.client.v3.Op)
    (o : OpFull) (top : TxnOp) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx ∗ context.isContext ctx cs ∗ context.isCancelCtxCtx ctx cs ∗
      opFullAt opv o ∗ etcdReached lo ∗ ⌜txnOpOf o = some top⌝ }}
    (App (App (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"revoke")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #opv))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); lkvReader lkv γ pfx ∗
      (⌜err ≠ GoInterface.nil⌝ ∨
       (⌜err = GoInterface.nil⌝ ∗ (opCommitted lo top resp ∨ notCommitted resp))) }}

end spec

end leasing
end EtcdGrove
end Perennial
