/-
`(*clientv3.kv).Do(ctx, op)` (`client/v3/kv.go`, translated for unit C1, the client meets the server). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

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

/-- **What `kv.Do` needs of its `Op`** `o`, for the run premise of the request it sends: a range
without a sort option or a put, the method registered with a spec (`Sr`, `Sp`) of which the
caller gives the request the server reads (`rangeWireOf o`, `putWireOf o`) and its `Φ`;
the other operation types are not specified (a delete, a transaction: `kv.Do`'s other cases). -/
def doRunOk (addr : GoString) (o : OpFull) (Sp : GrpcSpec (GF := GF) pbPutRequest pbPutResponse)
    (Qp : PutRespM → IProp GF) (Sr : GrpcSpec (GF := GF) pbRangeRequest pbRangeResponse) (Qr : RangeRespM → IProp GF) :
    IProp GF :=
  iprop((⌜o.t = W64 1 ∧ o.base.sortSet = false⌝ ∗ isGrpcRpc addr go!"/etcdserverpb.KV/Range" Sr ∗
      □ ▷ Sr (rangeWireOf o) Qr) ∨
    (⌜o.t = W64 2⌝ ∗ isGrpcRpc addr go!"/etcdserverpb.KV/Put" Sp ∗ □ ▷ Sp (putWireOf o) Qp))

/-- **What `kv.Do` returns** for the `Op` `o`: a range's answer in the `get` field, a put's in the
`put` field (`rangeCallOut`, `putCallOut`, after `ContextError`: a client error). -/
def doOut (o : OpFull) (Qp : PutRespM → IProp GF) (Qr : RangeRespM → IProp GF)
    (r : go_etcd_io.etcd.client.v3.OpResponse) (err : GoInterface) : IProp GF :=
  if o.t = W64 1 then rangeCallOut Qr r.get' err else putCallOut Qp r.put' err

/-- `kv.Do(ctx, op)` on a `*kv` over a connection to `addr` (`kvObjAt`), for an `Op` `op` modelled
by `o` that is a range (without a sort option) or a put: the request `op.toRangeRequest()` or
`&pb.PutRequest{...}` through the retry client's `Range` or `Put`, with the client's call options;
`doOut`. -/
abbrev kv.Do.spec : Prop :=
  ∀ (api : Loc) (addr : GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull) (Sp : GrpcSpec (GF := GF) pbPutRequest pbPutResponse)
    (Qp : PutRespM → IProp GF) (Sr : GrpcSpec (GF := GF) pbRangeRequest pbRangeResponse) (Qr : RangeRespM → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
      context.isContext ci cd ∗ ctxErrClient ci cd ∗ opFullAt opv o ∗ doRunOk addr o Sp Qp Sr Qr }}
    (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!! go!"Do"))
      (Val #(GoInterface.ok ci))) (Val #opv))
  {{ (r : go_etcd_io.etcd.client.v3.OpResponse) (err : GoInterface), RET (PairV #r #err);
      doOut o Qp Qr r err }}

end spec

end EtcdGrove
end Perennial
