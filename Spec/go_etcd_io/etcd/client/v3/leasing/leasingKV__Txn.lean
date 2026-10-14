/-
`lkv.Txn(ctx)` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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

/-- **`lkv.Txn(ctx)`**: a fresh `*txnLeasing` (as a `v3.Txn`), with the client's builder of
`lkv.kv.Txn(ctx)` inside, given nothing yet. -/
abbrev leasingKV.Txn.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ context.isContext ctx cs }}
    (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"Txn")) (Val #(GoInterface.ok ctx)))
  {{ (txn : Loc), RET #(GoInterface.ok (txnIface txn));
      ownTxnLeasing txn lkv γ pfx ctx cs LTxnBuild.empty }}

end spec

end leasing
end EtcdGrove
end Perennial
