/-
**The client meets the server** (unit C1, 2026-10-14): the vocabulary of the client's KV path
over gRPC (`client/v3/kv.go`, `retry.go`, the generated stub `api/etcdserverpb/rpc_grpc.pb.go`)
and of its trust boundary, grpc's `ClientConn.Invoke` (`Spec/google_golang_org/grpc/
ClientConn__Invoke.lean`, generic since 2026-10-14). Lean-first (no Rocq counterpart); the design
is in `notes/decisions.md`, "The client meets the server (unit C1)" and "A generic gRPC
specification".

**The connection** (`isEtcdConn conn addr`, unit P3a; it was grpc's opaque `isGrpcConn conn
addr`): the client's connection `conn` reaches the gRPC server at `addr` (grpc's `grpcConn`,
`google_golang_org/grpc/InvGrpc.lean`), whose methods are registered with their specs
(`isGrpcRpc addr name Spec`), with one unary interceptor that meets the retry interceptor's
contract (`etcdInterceptorOk`: what `Client.unaryClientInterceptor` returns,
`Client__unaryClientInterceptor.lean`) and no default call options: what `clientv3.New`'s
`dialSetupOpts` dials with, given no `Config.DialOptions` that add interceptors or call options
(an assumption about the unverified constructor and its configuration). The client's
calls are specified for any spec of the KV service's `Put` and `Range` (predicate transformers
over the messages' models, `GrpcSpec pbPutRequest pbPutResponse`, ...), and for any caller's
postcondition `Φ`; etcd's server's specs and handler proofs are in `client/v3/Results.lean`.

**Messages** (`ProtoMsg` instances: `pbPutRequest`, `pbRangeRequest`, `pbPutResponse`,
`pbRangeResponse`; `pbDeleteRangeRequest`, `pbDeleteRangeResponse` for the server's side): a request's model is the server's model of it (`putReqOp`, `rangeReqOp`:
`OpFull`), the sender's message the owned struct with its slices' contents, the decoded copy the
server's own predicate (`txn.putRequestIs`, `txn.rangeRequestIs`); a response's model is every
field the wire carries (`PutRespM`, `RangeRespM`: its header (`hdrFull`, the five fields), a put's
previous key-value (`txn.kvIs`, the six fields), a range's key-values (`txn.kvsIs`), `More`,
`Count`), held read-only (`putRespMsg`, `rangeRespMsg`) by the server's response and by the
client's decoded reply alike (a slice's contents, not whether it is `nil`).

**Call options** (`callOptOk`, `callOptsOk`): what the client passes in a call's `opts`: grpc's own
option values that hold only scalars (`StaticMethodCallOption`, `FailFastCallOption`,
`MaxSendMsgSizeCallOption`, `MaxRecvMsgSizeCallOption`: the stub's and `client.go`'s
`defaultCallOpts`), or a `retryOption` whose closure writes only the interceptor's own `options`'
`retryPolicy` (`retryApplyOk`: `withRepeatablePolicy`'s). None writes the caller's memory, which
`Invoke`'s frame needs (grpc's `Header`/`Trailer`/`Peer` options would).

**Context errors** (`ctxErrClient ci cd`): the context's `Err()` returns client errors
(`clientErr`, nil included), and keeps returning one once it has: Go's documented contract of
`Context.Err` (nil, then `Canceled` or `DeadlineExceeded` for good) and the method sets of those
errors (leaf errors, not `EtcdError`s), which the model does not have; a premise of
`ContextError` (whose result `kv.Put` passes to `errors.As` on a second `ContextError`).

**The objects**: `kvStubAt kc conn` (the generated `*kVClient` on `conn`), `retryKVAt rkv conn`
(a `*retryKVClient` over one), `kvObjAt api addr` (a `*kv` over one, with its call options),
`clientKVAt cl addr` (what `NewKV` reads of a `*Client`: its connection and call options, fixed
since `clientv3.New`, an assumption about the unverified constructor). The call options' slice is
full (`len = cap`, as `client.go` builds it): `retryKVClient.Range` appends to it, which, with
spare capacity, would write the slice's shared backing array from concurrent calls.

**The wire models** (`putWireOf o`, `rangeWireOf o`): the server's model of the request
`kv.Do` sends for the `Op` `o` (`txn.putOpOf`, `txn.rangeOpOf` of its fields; a range end is what
the wire carries, its contents: the server reads an empty one as `nil`, as the absent field it is).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxnOwn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Requests
public import Proof.go_etcd_io.etcd.client.v3.ClientErr
public import Perennial.Proof.context
public import Proof.google_golang_org.grpc.InvGrpc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil)

/-! ## Messages -/

section model
variable [ext : FfiSyntax]

/-- A `*pb.PutResponse` as the wire carries it: its header, its previous key-value. -/
structure PutRespM where
  hdr : HdrM
  prev : Option EtcdKv

/-- A `*pb.RangeResponse` as the wire carries it. -/
structure RangeRespM where
  hdr : HdrM
  kvs : List EtcdKv
  more : Bool
  count : w64

/-- A `*pb.DeleteRangeResponse` as the wire carries it: its header, `Deleted`, `PrevKvs`. -/
structure DelRespM where
  hdr : HdrM
  deleted : w64
  prevs : List EtcdKv

/-- **The server's model of the delete request `req`** (whose `Key` holds `k`, `RangeEnd` `e`):
the copy the gRPC server decodes (`txn.deleteRangeRequestIs`) denotes it, its range end the
contents `e` (as `rangeReqOp`'s). -/
def deleteReqOp (req : etcdserverpb.DeleteRangeRequest) (k e : GoString) : OpFull :=
  txn.deleteOpOf k e req.PrevKv'

/-- **The server's model of the put request `kv.Do` sends for the `Op` `o`** (`txn.putOpOf` of
the request's fields). -/
def putWireOf (o : OpFull) : OpFull :=
  txn.putOpOf o.key o.val o.leaseID o.base.prevKV o.ignoreValue o.ignoreLease

/-- **The server's model of the range request `kv.Do` sends for the `Op` `o`** without a sort
option (`txn.rangeOpOf` of the request's fields, the sort's order and target `0`). -/
def rangeWireOf (o : OpFull) : OpFull :=
  txn.rangeOpOf o.key o.base.rangeEnd o.base.rev o.base.limit (W32 0) (W32 0) o.base.serializable
    o.keysOnly o.base.countOnly o.base.minModRev o.base.maxModRev o.base.minCreateRev
    o.base.maxCreateRev

/-- **The server's model of the put request `req`** (whose `Key` holds `k`, `Value` `v`): the copy
the gRPC server decodes (`txn.putRequestIs`) denotes it. -/
def putReqOp (req : etcdserverpb.PutRequest) (k v : GoString) : OpFull :=
  txn.putOpOf k v req.Lease' req.PrevKv' req.IgnoreValue' req.IgnoreLease'

/-- **The server's model of the range request `req`** (whose `Key` holds `k`, `RangeEnd` `e`):
the copy the gRPC server decodes (`txn.rangeRequestIs`) denotes it, its range end the contents
`e` (an empty `RangeEnd` is not on the wire: the server's copy has `nil`, which
`txn.rangeEndOf` reads as `[]`). -/
def rangeReqOp (req : etcdserverpb.RangeRequest) (k e : GoString) : OpFull :=
  txn.rangeOpOf k e req.Revision' req.Limit' req.SortOrder' req.SortTarget' req.Serializable'
    req.KeysOnly' req.CountOnly' req.MinModRevision' req.MaxModRevision' req.MinCreateRevision'
    req.MaxCreateRevision'

end model

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `TypeRepr` of `clientv3.Client` straight from its `TypeAssumptions` (as `cache/v3/InvNew.lean`
does under the cache's assumptions): without it, the `StructFieldRef` step of `c.conn` and
`c.callOpts` (`RetryKVClient`, `NewKV`) finds `TypeRepr` through `Client`'s `IntoValTyped`,
built from the `sorry` instances of its names-only fields' axiomatized types. -/
instance (priority := high) clientC1_typeRepr :
    TypeRepr go_etcd_io.etcd.client.v3.Client.ty go_etcd_io.etcd.client.v3.Client :=
  go.type_repr_underlying (u := go_etcd_io.etcd.client.v3.Client.underlying)

instance (priority := high) clientC1_typeRepr_u :
    TypeRepr go_etcd_io.etcd.client.v3.Client.underlying go_etcd_io.etcd.client.v3.Client :=
  go.type_repr_underlying (u := go_etcd_io.etcd.client.v3.Client.underlying)

/-- **The `*pb.PutResponse` `l` holds the message `m`** (read-only; see the file header). -/
def putRespMsg (l : Loc) (m : PutRespM) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ ∃ h pk : Loc,
    structFieldRef etcdserverpb.PutResponse go!"Header" l ↦□ h ∗ hdrFull h m.hdr ∗
    structFieldRef etcdserverpb.PutResponse go!"PrevKv" l ↦□ pk ∗
    match m.prev with
    | none => iprop(⌜pk = null⌝)
    | some v => iprop(⌜pk ≠ null⌝ ∗ txn.kvIs pk v))

instance putRespMsg_persistent (l : Loc) (m : PutRespM) :
    Persistent (putRespMsg (GF := GF) l m) := by
  unfold putRespMsg; cases m.prev <;> infer_instance

/-- **The `*pb.RangeResponse` `l` holds the message `m`** (read-only). -/
def rangeRespMsg (l : Loc) (m : RangeRespM) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ ∃ (h : Loc) (sl : GoSlice) (ps : List Loc),
    structFieldRef etcdserverpb.RangeResponse go!"Header" l ↦□ h ∗ hdrFull h m.hdr ∗
    structFieldRef etcdserverpb.RangeResponse go!"Kvs" l ↦□ sl ∗ sl ↦*□ ps ∗ txn.kvsIs ps m.kvs ∗
    structFieldRef etcdserverpb.RangeResponse go!"More" l ↦□ m.more ∗
    structFieldRef etcdserverpb.RangeResponse go!"Count" l ↦□ m.count)

instance rangeRespMsg_persistent (l : Loc) (m : RangeRespM) :
    Persistent (rangeRespMsg (GF := GF) l m) := by
  unfold rangeRespMsg; infer_instance

/-- **The `*pb.DeleteRangeResponse` `l` holds the message `m`** (read-only). -/
def delRespMsg (l : Loc) (m : DelRespM) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ ∃ (h : Loc) (sl : GoSlice) (ps : List Loc),
    structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" l ↦□ h ∗ hdrFull h m.hdr ∗
    structFieldRef etcdserverpb.DeleteRangeResponse go!"Deleted" l ↦□ m.deleted ∗
    structFieldRef etcdserverpb.DeleteRangeResponse go!"PrevKvs" l ↦□ sl ∗ sl ↦*□ ps ∗
    txn.kvsIs ps m.prevs)

instance delRespMsg_persistent (l : Loc) (m : DelRespM) :
    Persistent (delRespMsg (GF := GF) l m) := by
  unfold delRespMsg; infer_instance

/-- **What a unary `Put` call returns** to the client (every layer's postcondition: the stub's,
the retry client's, `kv.Do`'s at its `put` field): `nil` and a response holding a message `m`
(`putRespMsg`) with the run's knowledge `Q m`; or a client error that grpc's `status` accepts
(`statusErrOk`, unit P3a: `ContextError` passes it to `rpctypes.Error`) and no response. -/
def putCallOut (Q : PutRespM → IProp GF) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗ Q m) ∨
    (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗ statusErrOk err))

/-- **What a unary `Range` call returns** to the client (as `putCallOut`). -/
def rangeCallOut (Q : RangeRespM → IProp GF) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗ Q m) ∨
    (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗ statusErrOk err))

/-! ## The KV service's messages -/

/-- **A `*pb.PutRequest`** on the wire (see the file header). -/
def pbPutRequest : ProtoMsg GF where
  ty := etcdserverpb.PutRequest.ty
  M := OpFull
  send inp o := iprop(∃ (req : etcdserverpb.PutRequest) (k v : GoString), inp ↦ req ∗
    req.Key' ↦*□ k ∗ req.Value' ↦*□ v ∗ ⌜o = putReqOp req k v⌝)
  recv r o := txn.putRequestIs r o
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.PutRequest))
  own l := iprop(∃ v : etcdserverpb.PutRequest, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.RangeRequest`** on the wire (see the file header). -/
def pbRangeRequest : ProtoMsg GF where
  ty := etcdserverpb.RangeRequest.ty
  M := OpFull
  send inp o := iprop(∃ (req : etcdserverpb.RangeRequest) (k e : GoString), inp ↦ req ∗
    req.Key' ↦*□ k ∗ req.RangeEnd' ↦*□ e ∗ ⌜o = rangeReqOp req k e⌝)
  recv r o := txn.rangeRequestIs r o
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.RangeRequest))
  own l := iprop(∃ v : etcdserverpb.RangeRequest, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.PutResponse`** on the wire (see the file header). -/
def pbPutResponse : ProtoMsg GF where
  ty := etcdserverpb.PutResponse.ty
  M := PutRespM
  send := putRespMsg
  recv := putRespMsg
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.PutResponse))
  own l := iprop(∃ v : etcdserverpb.PutResponse, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.RangeResponse`** on the wire (see the file header). -/
def pbRangeResponse : ProtoMsg GF where
  ty := etcdserverpb.RangeResponse.ty
  M := RangeRespM
  send := rangeRespMsg
  recv := rangeRespMsg
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.RangeResponse))
  own l := iprop(∃ v : etcdserverpb.RangeResponse, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.DeleteRangeRequest`** on the wire (see the file header; the server's side only: the
client's `kv.Do` does not send one in this development). -/
def pbDeleteRangeRequest : ProtoMsg GF where
  ty := etcdserverpb.DeleteRangeRequest.ty
  M := OpFull
  send inp o := iprop(∃ (req : etcdserverpb.DeleteRangeRequest) (k e : GoString), inp ↦ req ∗
    req.Key' ↦*□ k ∗ req.RangeEnd' ↦*□ e ∗ ⌜o = deleteReqOp req k e⌝)
  recv r o := txn.deleteRangeRequestIs r o
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.DeleteRangeRequest))
  own l := iprop(∃ v : etcdserverpb.DeleteRangeRequest, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.DeleteRangeResponse`** on the wire. -/
def pbDeleteRangeResponse : ProtoMsg GF where
  ty := etcdserverpb.DeleteRangeResponse.ty
  M := DelRespM
  send := delRespMsg
  recv := delRespMsg
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.DeleteRangeResponse))
  own l := iprop(∃ v : etcdserverpb.DeleteRangeResponse, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-! ## Call options -/

/-- **A `retryOption`'s closure** `f` writes only the interceptor's `options`' `retryPolicy`
(`withRepeatablePolicy`'s). -/
def retryApplyOk (f : GoFunc) : IProp GF :=
  iprop(∀ (o : Loc) (p : go_etcd_io.etcd.client.v3.retryPolicy),
    {{ structFieldRef go_etcd_io.etcd.client.v3.options go!"retryPolicy" o ↦ p }}
      (App (Val #f) (Val #o))
    {{ RET #(); ∃ p' : go_etcd_io.etcd.client.v3.retryPolicy,
        structFieldRef go_etcd_io.etcd.client.v3.options go!"retryPolicy" o ↦ p' }})

instance retryApplyOk_persistent (f : GoFunc) : Persistent (retryApplyOk (GF := GF) f) := by
  unfold retryApplyOk; infer_instance

/-- **A call option the client passes** (persistent; see the file header). -/
def callOptOk (v : GoInterface) : IProp GF :=
  iprop(⌜∃ (t : go.GoType) (x : val), v = interface.mkOk t x ∧ t ∈ grpcScalarOptTys⌝ ∨
    ∃ ro : go_etcd_io.etcd.client.v3.retryOption,
      ⌜v = interface.mkOk go_etcd_io.etcd.client.v3.retryOption.ty #ro⌝ ∗
      retryApplyOk ro.applyFunc')

instance callOptOk_persistent (v : GoInterface) : Persistent (callOptOk (GF := GF) v) := by
  unfold callOptOk; infer_instance

/-- Every call option of `vs` is one the client passes. -/
def callOptsOk (vs : List GoInterface) : IProp GF := iprop([∗list] v ∈ vs, callOptOk v)

instance callOptsOk_persistent (vs : List GoInterface) : Persistent (callOptsOk (GF := GF) vs) := by
  unfold callOptsOk; infer_instance

theorem callOptsOk_app (vs ws : List GoInterface) :
    callOptsOk (GF := GF) vs ∗ callOptsOk ws ⊢ callOptsOk (vs ++ ws) := by
  unfold callOptsOk
  iintro ⟨H1, H2⟩
  iapply BigSepL.bigSepL_append.2
  isplitl [H1]
  · iexact H1
  · iexact H2

theorem callOptsOk_nil : ⊢ callOptsOk (GF := GF) [] := by
  unfold callOptsOk
  iapply BigSepL.bigSepL_nil.2
  itrivial

theorem callOptsOk_singleton (v : GoInterface) : callOptOk (GF := GF) v ⊢ callOptsOk [v] := by
  unfold callOptsOk
  iintro H
  iapply BigSepL.bigSepL_singleton.2
  iexact H

/-! ## The connection -/

/-- **The client's retry interceptor's contract** (persistent; unit P3a: what
`Client.unaryClientInterceptor` returns, `Client__unaryClientInterceptor.lean`): called on a
connection to `addr` (`grpcConn`, any interceptors) with an invoker making one attempt
(`grpcInvokerOk`), for a method registered at `addr` with `Spec`, the request `inp`
(`Req.send`, given back), a zero reply `out` (`Rep.blank`), the client's call options
(`callOptsOk`) and the caller's `□ ▷ Spec m Φ` (persistent: the request may be delivered several
times, the attempts), it returns
* `nil`: an attempt succeeded, the last one (the loop returns at the first `nil`), and `out` holds
  its reply's copy of a response (`Rep.recv out m'`) with its run's `Φ m'`; other attempts may
  have run the handler: an attempt that failed with a gRPC `Canceled` or `DeadlineExceeded` while
  `ctx` is not done is retried whatever the method (`issues/etcd-client-retry-put-ctx-error.md`);
* an error: a client error (`clientErr`) that grpc's `status` accepts (`statusErrOk`); nothing
  about whether, or how often, the handler ran, nor about `out`. -/
def etcdInterceptorOk (ic : GoFunc) : IProp GF :=
  iprop(□ ∀ (conn : Loc) (addr : GoString) (ics : List GoFunc) (dopts : List GoInterface)
      (inv : GoFunc) (method : GoString) (Req Rep : ProtoMsg GF) (Spec : GrpcSpec Req Rep)
      (m : Req.M) (Φ : Rep.M → IProp GF) (ctx : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (inp out : Loc) (opts : GoSlice)
      (vs : List GoInterface),
    {{ grpcConn conn addr ics dopts ∗ grpcInvokerOk conn addr inv ∗ isGrpcRpc addr method Spec ∗
        □ ▷ Spec m Φ ∗ context.isContext ctx cd ∗ Req.send inp m ∗ Rep.blank out ∗
        opts ↦*□ vs ∗ callOptsOk vs }}
      (interceptorCall ic #(GoInterface.ok ctx) #method
        #(interface.mkOk (go.GoType.PointerType Req.ty) #inp : GoInterface)
        #(interface.mkOk (go.GoType.PointerType Rep.ty) #out : GoInterface) #conn inv #opts)
    {{ (err : GoInterface), RET #err; Req.send inp m ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ m' : Rep.M, Rep.recv out m' ∗ Φ m') ∨
          (⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗ statusErrOk err)) }})

instance etcdInterceptorOk_persistent (ic : GoFunc) : Persistent (etcdInterceptorOk (GF := GF) ic) := by
  unfold etcdInterceptorOk; infer_instance

/-- **An etcd client's connection `conn` to the server at `addr`** (persistent; unit P3a; see the
file header): grpc's connection with one unary interceptor, the client's retry interceptor
(`etcdInterceptorOk`), and no default call options. -/
def isEtcdConn (conn : Loc) (addr : GoString) : IProp GF :=
  iprop(∃ ic : GoFunc, grpcConn conn addr [ic] [] ∗ etcdInterceptorOk ic)

instance isEtcdConn_persistent (conn : Loc) (addr : GoString) :
    Persistent (isEtcdConn (GF := GF) conn addr) := by
  unfold isEtcdConn; infer_instance

/-! ## Context errors -/

/-- **The context `ci` (descriptor `cd`)'s `Err()` returns client errors** (persistent; see the
file header): `isContext`'s triple of `Err()` (`"#HErr"`: a non-nil error makes the context done,
`ContextClosed`, after which `Err()` is non-nil: Go's "successive calls to Err return the same
error"), with `clientErr` of the error returned, which grpc's `status` accepts (`statusErrOk`,
unit P3a: `kv.Put` passes `ContextError`'s result, possibly the context's error, to a second
`ContextError`, which passes it to `rpctypes.Error`; `context.Canceled` is an `errors.New` error,
`DeadlineExceeded` a `deadlineExceededError`, neither with a `GRPCStatus` or `Is` method). -/
def ctxErrClient (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(□ ∀ (cl : Broadcast) (Φ : val → IProp GF),
    (match cl with
     | .Done => context.ContextClosed cd.Done_gn
     | _ => iprop(True)) -∗
    ▷ (∀ err : GoInterface,
        (match cl with
         | .Done => iprop(⌜err ≠ interface.nil⌝)
         | _ => if err = interface.nil then iprop(True)
                else context.ContextClosed cd.Done_gn) -∗
        ⌜clientErr err⌝ -∗ statusErrOk err -∗ Φ #err) -∗
    WP (App (Val #(methods ci.ty go!"Err" ci.v)) (Val #())) {{ Φ }})

instance ctxErrClient_persistent (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    Persistent (ctxErrClient ci cd) := by
  unfold ctxErrClient; infer_instance

/-! ## The objects -/

/-- **The generated stub `kc`** (`*etcdserverpb.kVClient`) on the connection `conn`. -/
def kvStubAt (kc conn : Loc) : IProp GF :=
  iprop(structFieldRef etcdserverpb.kVClient go!"cc" kc ↦□
    (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #conn :
      GoInterface))

instance kvStubAt_persistent (kc conn : Loc) : Persistent (kvStubAt (GF := GF) kc conn) := by
  unfold kvStubAt; infer_instance

/-- **The `*retryKVClient` `rkv`** over a stub on `conn`. -/
def retryKVAt (rkv conn : Loc) : IProp GF :=
  iprop(∃ kc : Loc, structFieldRef go_etcd_io.etcd.client.v3.retryKVClient go!"kc" rkv ↦□
      (interface.mkOk (go.GoType.PointerType etcdserverpb.kVClient.ty) #kc : GoInterface) ∗
    kvStubAt kc conn)

instance retryKVAt_persistent (rkv conn : Loc) : Persistent (retryKVAt (GF := GF) rkv conn) := by
  unfold retryKVAt; infer_instance

/-- **The call options' slice `sl`** (read-only, full: `len = cap`), each one the client passes. -/
def callOptsAt (sl : GoSlice) : IProp GF :=
  iprop(∃ vs : List GoInterface, sl ↦*□ vs ∗ ⌜sl.len = sl.cap⌝ ∗ callOptsOk vs)

instance callOptsAt_persistent (sl : GoSlice) : Persistent (callOptsAt (GF := GF) sl) := by
  unfold callOptsAt; infer_instance

/-- **The `*kv` `api`** (what `NewKV` returns) over a `*retryKVClient` on a connection to the
server at `addr`. -/
def kvObjAt (api : Loc) (addr : GoString) : IProp GF :=
  iprop(∃ (rkv conn : Loc) (sl : GoSlice),
    structFieldRef go_etcd_io.etcd.client.v3.kv go!"remote" api ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryKVClient.ty) #rkv :
        GoInterface) ∗
    retryKVAt rkv conn ∗ isEtcdConn conn addr ∗
    structFieldRef go_etcd_io.etcd.client.v3.kv go!"callOpts" api ↦□ sl ∗ callOptsAt sl)

instance kvObjAt_persistent (api : Loc) (addr : GoString) : Persistent (kvObjAt (GF := GF) api addr) := by
  unfold kvObjAt; infer_instance

/-- **What `NewKV` reads of the `*Client` `cl`**: its connection (to the server at `addr`) and call
options, fixed since `clientv3.New` (an assumption about the unverified constructor). -/
def clientKVAt (cl : Loc) (addr : GoString) : IProp GF :=
  iprop(⌜cl ≠ null⌝ ∗ ∃ (conn : Loc) (sl : GoSlice),
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"conn" cl ↦□ conn ∗ isEtcdConn conn addr ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"callOpts" cl ↦□ sl ∗ callOptsAt sl)

instance clientKVAt_persistent (cl : Loc) (addr : GoString) :
    Persistent (clientKVAt (GF := GF) cl addr) := by
  unfold clientKVAt; infer_instance

end defs

end EtcdGrove
end Perennial
