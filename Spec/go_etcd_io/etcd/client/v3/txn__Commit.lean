/-
`(*clientv3.txn).Commit()` (`client/v3/kv.go`, translated for the vertical slice's unit V2). Lean-first (no Rocq counterpart).
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

/-- `t.Commit()` on a builder at `b`: the request `&pb.TxnRequest{Compare: cmps, Success: sus,
Failure: fas}` (the transaction `txnWireOf b.model` on the wire) through the `*kv`'s retry
client's `Txn`, for a spec `Spec` registered for `Txn` and the caller's `Q`, with the client's call options: the call's answer (`txnCallOut`; the error through
`ContextError`, a client error). The builder is spent (its slices are now the request's). -/
abbrev txn.Commit.spec : Prop :=
  ∀ (tp : Loc) (addr : GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (b : TxnBuild) (Spec : GrpcSpec (GF := GF) pbTxnRequest pbTxnResponse) (Q : TxnRespM → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ txnObjAt tp addr ci cd b ∗
      isGrpcRpc addr go!"/etcdserverpb.KV/Txn" Spec ∗
      -- (2026-10-20, linkv-txn stage A) ordinary on a builder over a one-attempt connection
      txnReqPre tp addr (Spec (txnWireOf b.model) Q) }}
    (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
      (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); txnCallOut Q resp err }}

end spec

end EtcdGrove
end Perennial
