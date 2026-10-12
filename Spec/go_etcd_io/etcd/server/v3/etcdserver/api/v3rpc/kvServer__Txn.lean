/-
`v3rpc.kvServer.Txn` (`key.go`). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvKV.lean` and `Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvKV

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`kvServer.Txn(ctx, r)`** of the transaction (comparisons `cs`, branches `ts`, `es`): `checkTxnRequest`'s error
at the server's budget `n`, or `ErrGRPCDuplicateKey` from `checkIntervals` of a branch
(`txnAllCheck`), or the server's `Txn` answer with the header filled (`kvOut`). -/
abbrev v3rpc.kvServer.Txn.spec : Prop :=
  ∀ (p s : Loc) (A : v3rpc.KVAns GF) (cid mid n : w64) (ctx : GoInterface) (r : Loc) (cs : List CmpModel) (ts es : List v3rpc.ReqOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ v3rpc.kvServerIs p s A cid mid n ∗ A.call ctx ∗ v3rpc.txnReqIs r cs ts es ∗
      v3rpc.txnReqWire r ts es ∗ ⌜A.pre (.txn cs ts es)⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType v3rpc.kvServer.ty @!! go!"Txn")) (Val #ctx))
      (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      match v3rpc.txnAllCheck (sint.Z n) cs ts es with
      | some e => v3rpc.checkOut e resp err ∗ A.call ctx
      | none => v3rpc.kvOut A cid mid (.txn cs ts es)
          (structFieldRef etcdserverpb.TxnResponse go!"Header" resp) resp err }}

end spec

end EtcdGrove
end Perennial
