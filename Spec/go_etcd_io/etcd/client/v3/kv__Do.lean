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

/-- **What `kv.Do` needs of its `Op`** `o`, for the request it sends: a range (any sort option,
checked against `etcdserverpb`'s enumerations, `sortNamesOk` if there is one: the vertical slice's unit V2; C1
required none), a put or a delete (unit V2), the method registered with a spec (`Sr`, `Sp`, `Sd`)
of which the caller gives the request the server reads (`rangeWireOf o`, `putWireOf o`,
`deleteWireOf o`) and its `Φ`; a transaction (`OpTxn`, `Op.toTxnRequest`) is not specified here
(`kv.Txn`'s builder sends one: `txn.Commit`). -/
def doRunOk (addr : GoString) (o : OpFull) (Sp : GrpcSpec (GF := GF) pbPutRequest pbPutResponse)
    (Qp : PutRespM → IProp GF) (Sr : GrpcSpec (GF := GF) pbRangeRequest pbRangeResponse)
    (Qr : RangeRespM → IProp GF)
    (Sd : GrpcSpec (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse)
    (Qd : DelRespM → IProp GF) : IProp GF :=
  iprop((⌜o.t = W64 1⌝ ∗ sortNamesIf o.base.sortSet ∗ isGrpcRpc addr go!"/etcdserverpb.KV/Range" Sr ∗
      □ ▷ Sr (rangeWireOf o) Qr) ∨
    (⌜o.t = W64 2⌝ ∗ isGrpcRpc addr go!"/etcdserverpb.KV/Put" Sp ∗ □ ▷ Sp (putWireOf o) Qp) ∨
    (⌜o.t = W64 3⌝ ∗ isGrpcRpc addr go!"/etcdserverpb.KV/DeleteRange" Sd ∗
      □ ▷ Sd (deleteWireOf o) Qd))

/-- **What `kv.Do` returns** for the `Op` `o`: a range's answer in the `get` field (an invalid
sort option is a client error, `rpctypes.ErrInvalidSortOption`), a put's in the `put` field, a
delete's in the `del` field (`rangeCallOut`, `putCallOut`, `deleteCallOut`, after
`ContextError`: a client error). -/
def doOut (o : OpFull) (Qp : PutRespM → IProp GF) (Qr : RangeRespM → IProp GF)
    (Qd : DelRespM → IProp GF) (r : go_etcd_io.etcd.client.v3.OpResponse) (err : GoInterface) :
    IProp GF :=
  if o.t = W64 1 then rangeCallOut Qr r.get' err
  else if o.t = W64 2 then putCallOut Qp r.put' err
  else deleteCallOut Qd r.del' err

/-- `kv.Do(ctx, op)` on a `*kv` over a connection to `addr` (`kvObjAt`), for an `Op` `op` modelled
by `o` that is a range, a put or a delete: the request `op.toRangeRequest()`,
`&pb.PutRequest{...}` or `&pb.DeleteRangeRequest{...}` through the retry client's `Range`, `Put`
or `DeleteRange`, with the client's call options; `doOut`. -/
abbrev kv.Do.spec : Prop :=
  ∀ (api : Loc) (addr : GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull)
    (Sp : GrpcSpec (GF := GF) pbPutRequest pbPutResponse) (Qp : PutRespM → IProp GF)
    (Sr : GrpcSpec (GF := GF) pbRangeRequest pbRangeResponse) (Qr : RangeRespM → IProp GF)
    (Sd : GrpcSpec (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse)
    (Qd : DelRespM → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ opFullAt opv o ∗ doRunOk addr o Sp Qp Sr Qr Sd Qd }}
    (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!! go!"Do"))
      (Val #(GoInterface.ok ci))) (Val #opv))
  {{ (r : go_etcd_io.etcd.client.v3.OpResponse) (err : GoInterface), RET (PairV #r #err);
      doOut o Qp Qr Qd r err }}

end spec

end EtcdGrove
end Perennial
