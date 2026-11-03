/-
**The `*kv`'s calls at the members** (D44, 2026-10-25): the statements of the members' lemmas of
`kv.Do`, `kv.Put`, `kv.Get`, `kv.Delete` and `txn.Commit` (`*.specM`; proved in the functions'
`Proof` files as `*.wp_members`, linked in `LinkMembers.lean`): over a `*kv` of the members `ms`
(`isKV`: each member's etcd KV specs registered at its address), the caller's side at each
member (its floor, committed index and update: `floorsAt`, `knownAt`, `putUpd`, ...), the reply
some member's (`putAns`, ...: `putReplied`, ... at that member). The functions' specs (`kv.Put.spec`,
...: one KV, `isKv`) are proved from these; the results about the server's own model use them
(`ServerKV*.lean`: a member's reply's certificates and tokens). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.KVService

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 client

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **What `kv.Do` needs of its `Op`** `o` on a `*kv` of the members `ms` (D44): a range (any
sort option, checked against `etcdserverpb`'s enumerations, `sortNamesOk` if there is one: the
vertical slice's unit V2) by a reader that knows the members' committed indices at least `c` and
the floor `F` (`knownAt`), with its read update at the members (`rangeUpd`, persistent); a put
with no lease or a delete whose range end is not `[0]` (unit V2; what etcd's specs cover), with
the floor `F` and the caller's update at the members (`putUpd`, `delUpd`: persistent, or ordinary
over refusal-free members, D29), all of the request the server reads (`rangeWireOf o`,
`putWireOf o`, `deleteWireOf o`); a transaction (`OpTxn`, `Op.toTxnRequest`) is not specified
here (`kv.Txn`'s builder sends one: `txn.Commit`). -/
def doRunM (api : Loc) (ms : List (SrvAt GF)) (o : OpFull) (c : w64) (F : mvcc.Log)
    (Q : KVState → IProp GF) : IProp GF :=
  iprop((⌜o.t = W64 1⌝ ∗ sortNamesIf o.base.sortSet ∗ knownAt ms c F ∗
      □ rangeUpd ms (rangeWireOf o) Q) ∨
    (⌜o.t = W64 2 ∧ (putWireOf o).leaseID = W64 0⌝ ∗ floorsAt ms F ∗
      kvReqPre api (ms.map SrvAt.addr) (putUpd ms (putWireOf o) Q)) ∨
    (⌜o.t = W64 3 ∧ (deleteWireOf o).base.rangeEnd ≠ [W8 0]⌝ ∗ floorsAt ms F ∗
      kvReqPre api (ms.map SrvAt.addr) (delUpd ms (deleteWireOf o) Q)))

/-- `kv.Do(ctx, op)` on a `*kv` of the members `ms` (`isKV`, D44), for an `Op` `op` modelled by
`o` that is a range, a put or a delete (`doRunM`): the request `op.toRangeRequest()`,
`&pb.PutRequest{...}` or `&pb.DeleteRangeRequest{...}` through the retry client's `Range`, `Put`
or `DeleteRange`, with the client's call options; `doOut` with some member's reply (`rangeAns`,
`putAns`, `delAns`). The request fits a gRPC message (`opSizeOk`; 2026-10-30, `grpcInvokerOk`). -/
abbrev kv.Do.specM : Prop :=
  ∀ (api : Loc) (ms : List (SrvAt GF)) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull) (c : w64) (F : mvcc.Log)
    (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isKV api ms ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ opFullAt opv o ∗ doRunM api ms o c F Q ∗
      ⌜opSizeOk o⌝ }}
    (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!! go!"Do"))
      (Val #(GoInterface.ok ci))) (Val #opv))
  {{ (r : go_etcd_io.etcd.client.v3.OpResponse) (err : GoInterface), RET (PairV #r #err);
      doOut o (putAns ms F (putWireOf o) Q) (rangeAns ms c F (rangeWireOf o) Q)
        (delAns ms F (deleteWireOf o) Q) r err }}

/-- `kv.Put(ctx, key, val, opts...)` on a `*kv` of the members `ms` (`isKV`, D44): `kv.Do` of
`OpPut(key, val, opts...)` (options with transformers `gs` that do not make `OpPut` panic nor
change the operation's type), a put with no lease (etcd's `Put` spec covers no other), with the
floor `F` and the caller's update at the members (`putUpd`; persistent, or ordinary over
refusal-free members: a write sent at most once, D29); the error through `ContextError`:
`putCallOut` with some member's `putReplied` for the put the server reads (`putWireOf`). The request
fits a gRPC message (`opSizeOk`; 2026-10-30, `grpcInvokerOk`). -/
abbrev kv.Put.specM : Prop :=
  ∀ (api : Loc) (ms : List (SrvAt GF)) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key val : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)) (Q : KVState → IProp GF)
    (F : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isKV api ms ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl gs ∗
      ⌜¬ (opPutModel key val gs).putPanics ∧ (opPutModel key val gs).t = W64 2 ∧
        (putWireOf (opPutModel key val gs)).leaseID = W64 0⌝ ∗
      floorsAt ms F ∗
      kvReqPre api (ms.map SrvAt.addr) (putUpd ms (putWireOf (opPutModel key val gs)) Q) ∗
      ⌜opSizeOk (opPutModel key val gs)⌝ }}
    (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      putCallOut (putAns ms F (putWireOf (opPutModel key val gs)) Q) resp err }}

/-- `kv.Get(ctx, key, opts...)` on a `*kv` of the members `ms` (`isKV`, D44): `OpGet(key,
opts...)` (options that do not panic, keep the range type, and may need a resource `R`, given
back: `optsAtRes`; any sort option, checked against `etcdserverpb`'s enumerations,
`sortNamesOk`: the vertical slice's unit V2), then `kv.Do`, by a reader that knows the members'
committed indices at least `c` and the floor `F` (`knownAt`), with its read update at the members
(`rangeUpd`, persistent: a read may be answered by any member, and again); the error through
`ContextError`: `rangeCallOut` with some member's `rangeReplyOk` for the range the server reads
(`rangeWireOf`). The request fits a gRPC message (`opSizeOk`; 2026-10-30, `grpcInvokerOk`). -/
abbrev kv.Get.specM : Prop :=
  ∀ (api : Loc) (ms : List (SrvAt GF)) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)) (R : IProp GF) (c : w64)
    (F : mvcc.Log) (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isKV api ms ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAtRes sl gs R ∗ R ∗
      sortNamesIf (opGetModel key gs).base.sortSet ∗
      ⌜¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1⌝ ∗
      knownAt ms c F ∗ □ rangeUpd ms (rangeWireOf (opGetModel key gs)) Q ∗
      ⌜opSizeOk (opGetModel key gs)⌝ }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      R ∗ rangeCallOut (rangeAns ms c F (rangeWireOf (opGetModel key gs)) Q) resp err }}

/-- `kv.Delete(ctx, key, opts...)` on a `*kv` of the members `ms` (`isKV`, D44): `kv.Do` of
`OpDelete(key, opts...)` (options with transformers `gs` that do not make `OpDelete` panic nor
change the operation's type), a delete whose range end is not `[0]` (etcd's `DeleteRange` spec
covers no other: `WithFromKey`'s), with the floor `F` and the caller's update at the members
(`delUpd`; persistent, or ordinary over refusal-free members, D29); the error through
`ContextError`: `deleteCallOut` with some member's `deleteReplied` for the delete the server reads
(`deleteWireOf`). The request fits a gRPC message (`opSizeOk`; 2026-10-30, `grpcInvokerOk`). -/
abbrev kv.Delete.specM : Prop :=
  ∀ (api : Loc) (ms : List (SrvAt GF)) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)) (Q : KVState → IProp GF)
    (F : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isKV api ms ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl gs ∗
      ⌜¬ opDeletePanics key gs ∧ (opDeleteModel key gs).t = W64 3 ∧
        (deleteWireOf (opDeleteModel key gs)).base.rangeEnd ≠ [W8 0]⌝ ∗
      floorsAt ms F ∗
      kvReqPre api (ms.map SrvAt.addr) (delUpd ms (deleteWireOf (opDeleteModel key gs)) Q) ∗
      ⌜opSizeOk (opDeleteModel key gs)⌝ }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Delete")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      deleteCallOut (delAns ms F (deleteWireOf (opDeleteModel key gs)) Q) resp err }}

/-- `t.Commit()` on a builder at `b` over a `*kv` of the members `ms` (its registrations
`kvRegs`, D44): the request `&pb.TxnRequest{Compare: cmps, Success: sus, Failure: fas}` (the
transaction `txnWireOf b.model` on the wire, of plain operations within the txn package's model)
through the `*kv`'s retry client's `Txn`, with the client's call options, by a caller that knows
the members' committed indices at least `c` and the floor `F` (`knownAt`), with its update at
the members (`txnUpd`; persistent, or ordinary over refusal-free members, D29): the call's answer
(`txnCallOut` with some member's `txnReplied`; the error through `ContextError`, a client error).
The builder is spent (its slices are now the request's). The request fits a gRPC message
(`txnSizeOk`; 2026-10-30, `grpcInvokerOk`). -/
abbrev txn.Commit.specM : Prop :=
  ∀ (tp : Loc) (ms : List (SrvAt GF)) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (b : TxnBuild) (c : w64) (F : mvcc.Log) (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      txnObjAt tp (ms.map SrvAt.addr) ci cd b ∗ kvRegs ms ∗
      ⌜TxnModel.plain b.model ∧ txnModelIn (txnWireOf b.model)⌝ ∗ knownAt ms c F ∗
      txnReqPre tp (ms.map SrvAt.addr) (txnUpd ms (txnWireOf b.model) Q) ∗
      ⌜txnSizeOk (txnWireOf b.model)⌝ }}
    (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
      (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      txnCallOut (txnAns ms c F (txnWireOf b.model) Q) resp err }}

/-- **What `kv.Do` needs of its `Op`, for specs `Sp`, `Sr`, `Sd` registered at the connection**
(the transport's terms, as the retry client's specs take them; `kv.Do.wp_proof` instantiates
them with the members' specs, `kvPutSpec`, ...): a range, the method registered with `Sr` and the
caller's `□ ▷ Sr (rangeWireOf o) Qr`; a put or a delete, `Sp`'s or `Sd`'s request precondition
(`kvReqPre`). Since 2026-10-28 (the auth plan's E3zc) the specs are metadata-indexed
(`GrpcSpecMd`; a plain one is `GrpcSpec.md`), each precondition at every metadata an attempt of the
call on the `*kv`'s connection `conn` with the context `ctx` may deliver (`attemptPre`). -/
def doRunGen (api conn : Loc) (addr : List GoString) (ctx : GoInterface) (o : OpFull)
    (Sp : GrpcSpecMd (GF := GF) pbPutRequest pbPutResponse) (Qp : PutRespM → IProp GF)
    (Sr : GrpcSpecMd (GF := GF) pbRangeRequest pbRangeResponse) (Qr : RangeRespM → IProp GF)
    (Sd : GrpcSpecMd (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse)
    (Qd : DelRespM → IProp GF) : IProp GF :=
  iprop((⌜o.t = W64 1⌝ ∗ sortNamesIf o.base.sortSet ∗
      isGrpcRpcsMd addr go!"/etcdserverpb.KV/Range" Sr ∗
      □ ▷ attemptPre conn ctx Sr (rangeWireOf o) Qr) ∨
    (⌜o.t = W64 2⌝ ∗ isGrpcRpcsMd addr go!"/etcdserverpb.KV/Put" Sp ∗
      kvReqPre api addr (attemptPre conn ctx Sp (putWireOf o) Qp)) ∨
    (⌜o.t = W64 3⌝ ∗ isGrpcRpcsMd addr go!"/etcdserverpb.KV/DeleteRange" Sd ∗
      kvReqPre api addr (attemptPre conn ctx Sd (deleteWireOf o) Qd)))

/-- **`kv.Do(ctx, op)` for any specs registered at the connection** (`doRunGen`, the transport's
terms; the auth plan's E3zc: what the members' calls in either auth mode instantiate,
`kv.Do.wp_members` at the plain specs): `doOut`. The request fits a gRPC message (`opSizeOk`;
2026-10-30, `grpcInvokerOk`). -/
abbrev kv.Do.specG : Prop :=
    ∀ (api conn : Loc) (addr : List GoString) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull)
      (Sp : GrpcSpecMd (GF := GF) pbPutRequest pbPutResponse) (Qp : PutRespM → IProp GF)
      (Sr : GrpcSpecMd (GF := GF) pbRangeRequest pbRangeResponse) (Qr : RangeRespM → IProp GF)
      (Sd : GrpcSpecMd (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse)
      (Qd : DelRespM → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAtC api conn addr ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ opFullAt opv o ∗
        doRunGen api conn addr (GoInterface.ok ci) o Sp Qp Sr Qr Sd Qd ∗
      ⌜opSizeOk o⌝ }}
      (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!! go!"Do"))
        (Val #(GoInterface.ok ci))) (Val #opv))
    {{ (r : go_etcd_io.etcd.client.v3.OpResponse) (err : GoInterface), RET (PairV #r #err);
        doOut o Qp Qr Qd r err }}

/-- **`kv.Put(ctx, key, val, opts...)` for any spec registered for `Put` at the connection** (the
auth plan's E3zc; `kv.Put.specM`'s, in the transport's terms: the caller's request precondition at
every attempt's metadata, `attemptPre`, its answer `Qp`): `putCallOut Qp`. The request fits a gRPC
message (`opSizeOk`; 2026-10-30, `grpcInvokerOk`). -/
abbrev kv.Put.specG : Prop :=
  ∀ (api conn : Loc) (addr : List GoString) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key val : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (Sp : GrpcSpecMd (GF := GF) pbPutRequest pbPutResponse)
    (Qp : PutRespM → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAtC api conn addr ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl gs ∗
      ⌜¬ (opPutModel key val gs).putPanics ∧ (opPutModel key val gs).t = W64 2⌝ ∗
      isGrpcRpcsMd addr go!"/etcdserverpb.KV/Put" Sp ∗
      kvReqPre api addr
        (attemptPre conn (GoInterface.ok ci) Sp (putWireOf (opPutModel key val gs)) Qp) ∗
      ⌜opSizeOk (opPutModel key val gs)⌝ }}
    (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); putCallOut Qp resp err }}

/-- **`kv.Get(ctx, key, opts...)` for any spec registered for `Range` at the connection** (the
auth plan's E3zc; `kv.Get.specM`'s, in the transport's terms): `R` back, `rangeCallOut Qr`. The
request fits a gRPC message (`opSizeOk`; 2026-10-30, `grpcInvokerOk`). -/
abbrev kv.Get.specG : Prop :=
  ∀ (api conn : Loc) (addr : List GoString) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (R : IProp GF)
    (Sr : GrpcSpecMd (GF := GF) pbRangeRequest pbRangeResponse) (Qr : RangeRespM → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAtC api conn addr ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAtRes sl gs R ∗ R ∗
      sortNamesIf (opGetModel key gs).base.sortSet ∗
      ⌜¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1⌝ ∗
      isGrpcRpcsMd addr go!"/etcdserverpb.KV/Range" Sr ∗
      □ ▷ attemptPre conn (GoInterface.ok ci) Sr (rangeWireOf (opGetModel key gs)) Qr ∗
      ⌜opSizeOk (opGetModel key gs)⌝ }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); R ∗ rangeCallOut Qr resp err }}

/-- **`kv.Delete(ctx, key, opts...)` for any spec registered for `DeleteRange` at the connection**
(the auth plan's E3zc; `kv.Delete.specM`'s, in the transport's terms): `deleteCallOut Qd`. The
request fits a gRPC message (`opSizeOk`; 2026-10-30, `grpcInvokerOk`). -/
abbrev kv.Delete.specG : Prop :=
  ∀ (api conn : Loc) (addr : List GoString) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull))
    (Sd : GrpcSpecMd (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse)
    (Qd : DelRespM → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAtC api conn addr ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl gs ∗
      ⌜¬ opDeletePanics key gs ∧ (opDeleteModel key gs).t = W64 3⌝ ∗
      isGrpcRpcsMd addr go!"/etcdserverpb.KV/DeleteRange" Sd ∗
      kvReqPre api addr
        (attemptPre conn (GoInterface.ok ci) Sd (deleteWireOf (opDeleteModel key gs)) Qd) ∗
      ⌜opSizeOk (opDeleteModel key gs)⌝ }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Delete")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); deleteCallOut Qd resp err }}

/-- **`t.Commit()` for any spec registered for `Txn` at the connection** (the auth plan's E3zc;
`txn.Commit.specM`'s, in the transport's terms: the builder's `*kv` `api` over `conn`, the caller's
request precondition at every attempt's metadata): `txnCallOut Q`. The request fits a gRPC message
(`txnSizeOk`; 2026-10-30, `grpcInvokerOk`). -/
abbrev txn.Commit.specG : Prop :=
    ∀ (tp api conn : Loc) (addr : List GoString) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF))
      (b : TxnBuild) (Spec : GrpcSpecMd (GF := GF) pbTxnRequest pbTxnResponse)
      (Q : TxnRespM → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ txnObjAt tp addr ci cd b ∗
        txnKvIs tp api ∗ kvObjAtC api conn addr ∗
        isGrpcRpcsMd addr go!"/etcdserverpb.KV/Txn" Spec ∗
        txnReqPre tp addr (attemptPre conn (GoInterface.ok ci) Spec (txnWireOf b.model) Q) ∗
      ⌜txnSizeOk (txnWireOf b.model)⌝ }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
        (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); txnCallOut Q resp err }}

end spec

end EtcdGrove
end Perennial
