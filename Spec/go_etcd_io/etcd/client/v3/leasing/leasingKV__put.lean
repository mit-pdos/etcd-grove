/-
`lkv.put(ctx, op)` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`lkv.put(ctx, op)`** for a put `op` (`o`, the transaction operation `top`): after
`waitSession`, commits it by `tryModifyOp` or `revoke` (both, if the key is not cached: a finding)
until one succeeds or the context is done; on success updates the key's cache entry under the
lock (`Update`). Returns an error, or the put (`putCommitted`: its revision, the state before it,
and the cache's step). The context must be cancelable. -/
abbrev leasingKV.put.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull)
    (top : TxnOp) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx ∗ context.isContext ctx cs ∗ context.isCancelCtxCtx ctx cs ∗
      opFullAt opv o ∗ etcdReached lo ∗ ⌜o.t = W64 2 ∧ txnOpOf o = some top⌝ }}
    (App (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"put")) (Val #(GoInterface.ok ctx))) (Val #opv))
  {{ (pr : Loc) (err : GoInterface), RET (PairV #pr #err); lkvReader lkv γ pfx ∗
      (⌜err ≠ GoInterface.nil ∧ pr = null⌝ ∨
       (⌜err = GoInterface.nil⌝ ∗ putCommitted γ lo o top pr)) }}

end spec

end leasing
end EtcdGrove
end Perennial
