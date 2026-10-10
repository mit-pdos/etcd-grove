/-
`txn.serverTxn()` (`client/v3/leasing/txn.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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

/-- **`txn.serverTxn()`**: after `waitSession`, locks the written keys' entries, and until it
succeeds commits "if the guards hold (no other client's lease on a written key or range), the
user's transaction nested, else get the written keys' lease keys", revoking the leases found;
on success applies the user's operations to the cache (`commitToCache`) and returns the nested
transaction's response with the outer header: what the client's `Commit` returns for the user's
transaction (`txnCommitResult`). The context must be cancelable. -/
abbrev txnLeasing.serverTxn.spec : Prop :=
  ∀ (txn lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (b : LTxnBuild) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ ownTxnLeasing txn lkv γ pfx ctx cs b ∗ lkvReader lkv γ pfx ∗ context.isCancelCtxCtx ctx cs ∗ etcdReached lo }}
    (App (Val (txn @!! go.GoType.PointerType txnLeasing.ty @!! go!"serverTxn")) (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); lkvReader lkv γ pfx ∗
      ∃ tops eops : List TxnOp, ⌜b.thenOps = some tops ∧ b.elseOps = some eops⌝ ∗
        txnCommitResult [] lo (b.model tops eops) resp err }}

end spec

end leasing
end EtcdGrove
end Perennial
