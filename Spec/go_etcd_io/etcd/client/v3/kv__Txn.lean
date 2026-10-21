/-
`(*clientv3.kv).Txn(ctx)` (`client/v3/kv.go`, translated for the vertical slice's unit V2). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvTxnBuilder

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `kv.Txn(ctx)` on a `*kv` over a connection to the server at `addr`, at a context whose errors are client errors
(`ctxErrClient`, for `Commit`'s `ContextError`): a new `*txn` as a `Txn`, a builder in its empty
state (`txnObjAt`), made from `api` (`txnKvIs`; 2026-10-20, linkv-txn stage A). -/
abbrev kv.Txn.spec : Prop :=
  ∀ (api : Loc) (addr : List GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
      ctxOk ci cd ∗ ctxErrClient ci cd }}
    (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!! go!"Txn"))
      (Val #(GoInterface.ok ci)))
  {{ (t : GoInterface), RET #t; ∃ tp : Loc,
      ⌜t = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp⌝ ∗
      txnObjAt tp addr ci cd TxnBuild.empty ∗ txnKvIs tp api }}

end spec

end EtcdGrove
end Perennial
