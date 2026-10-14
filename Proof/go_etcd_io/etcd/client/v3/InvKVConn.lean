/-
**The client meets the server** (unit C1, 2026-10-14): the vocabulary of the client's KV path
over gRPC (`client/v3/kv.go`, `retry.go`, the generated stub `api/etcdserverpb/rpc_grpc.pb.go`)
and of its trust boundary, grpc's `ClientConn.Invoke` (`Spec/google_golang_org/grpc/
ClientConn__Invoke.lean`). Lean-first (no Rocq counterpart); the design is in
`notes/decisions.md`, "The client meets the server (unit C1)".

**The connection** (`isKVConn conn K`, persistent, an axiomatized predicate: a fact about grpc's
`*ClientConn` and the process at its other end, which nothing here models): the client's
connection `conn` reaches a gRPC server whose KV service answers a `Put` (a `Range`) with a run
of the handler `K.put` (`K.range`) on a copy of the request, each run given by the server's
runtime the resources `K.R ctx'` (for its context `ctx'`). For etcd's server, `K.put` is
`kvServer.Put` at the server's `*kvServer`, `K.R` the server-side call resources `srvCall`,
`srvRdCall` (the client's end-to-end results, `client/v3/Results.lean`).

**What a run gives** (`putRunOk K o Q`, `rangeRunOk K o Q`; persistent: a run may happen several
times, the retry interceptor's attempts): the handler's triple for the request `o` (the server's
model of the copy the gRPC server decodes, `txn.putRequestIs`/`txn.rangeRequestIs`), with the
runtime's resources, whose success is a response message `m` (`putRespMsg`, `rangeRespMsg`: every
field of the message, as the reply's copy holds it) with the caller's persistent knowledge `Q m`.

**Messages** (`PutRespM`, `RangeRespM`; `putRespMsg l m`, `rangeRespMsg l m`, read-only): a
response's every field the wire carries: its header (`hdrFull`, the five fields), a put's previous
key-value (`txn.kvIs`, the six fields), a range's key-values (`txn.kvsIs`), `More`, `Count`. The
gRPC reply is a copy of the server's response (a protobuf round trip), so the same predicate holds
of both (a slice's contents, not whether it is `nil`).

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
(a `*retryKVClient` over one), `kvObjAt api K` (a `*kv` over one, with its call options),
`clientKVAt cl K` (what `NewKV` reads of a `*Client`: its connection and call options, fixed
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

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

/-! ## The connection -/

/-- **A KV service at the other end of a connection**: the handlers the gRPC server runs for a
`Put` and a `Range` (function values: called with the call's context and the request), and the
resources the server's runtime gives each run, for its context. -/
structure KVConn [FfiSyntax] (GF : BundledGFunctors) where
  put : val
  range : val
  R : GoInterface → IProp GF

/-- **The client's connection `conn` reaches the KV service `K`** (persistent; an axiomatized
predicate, see the file header): grpc's `*ClientConn`, dialed by the client with its
interceptors, to a server whose registered KV service answers with runs of `K`'s handlers. -/
axiom isKVConn {GF : BundledGFunctors} [FfiSyntax] (conn : Loc) (K : KVConn GF) : IProp GF

axiom isKVConn_persistent {GF : BundledGFunctors} [FfiSyntax] (conn : Loc) (K : KVConn GF) :
  Persistent (isKVConn conn K)

attribute [instance] isKVConn_persistent

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

/-! ## What a run of a handler gives -/

/-- **A run of the `Put` handler of `K` on the put `o`** (persistent; see the file header): with
the runtime's resources and the decoded request, it answers `(resp, err)`, and if `err` is `nil`,
`resp` holds a message `m` with the caller's knowledge `Q m`. -/
def putRunOk (K : KVConn GF) (o : OpFull) (Q : PutRespM → IProp GF) : IProp GF :=
  iprop(∀ (ctx : GoInterface) (r : Loc),
    {{ K.R ctx ∗ txn.putRequestIs r o }}
      (App (App (Val K.put) (Val #ctx)) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        ⌜err = GoInterface.nil⌝ -∗ ∃ m : PutRespM, putRespMsg resp m ∗ □ Q m }})

instance putRunOk_persistent (K : KVConn GF) (o : OpFull) (Q : PutRespM → IProp GF) :
    Persistent (putRunOk K o Q) := by
  unfold putRunOk; infer_instance

/-- **A run of the `Range` handler of `K` on the get `o`** (as `putRunOk`). -/
def rangeRunOk (K : KVConn GF) (o : OpFull) (Q : RangeRespM → IProp GF) : IProp GF :=
  iprop(∀ (ctx : GoInterface) (r : Loc),
    {{ K.R ctx ∗ txn.rangeRequestIs r o }}
      (App (App (Val K.range) (Val #ctx)) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        ⌜err = GoInterface.nil⌝ -∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗ □ Q m }})

instance rangeRunOk_persistent (K : KVConn GF) (o : OpFull) (Q : RangeRespM → IProp GF) :
    Persistent (rangeRunOk K o Q) := by
  unfold rangeRunOk; infer_instance

/-- **What a unary `Put` call returns** to the client (every layer's postcondition: the stub's,
the retry client's, `kv.Do`'s at its `put` field): `nil` and a response holding a message `m`
(`putRespMsg`) with the run's knowledge `Q m`; or a client error and no response. -/
def putCallOut (Q : PutRespM → IProp GF) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗ □ Q m) ∨
    ⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝)

/-- **What a unary `Range` call returns** to the client (as `putCallOut`). -/
def rangeCallOut (Q : RangeRespM → IProp GF) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗ □ Q m) ∨
    ⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝)

instance putCallOut_persistent (Q : PutRespM → IProp GF) (resp : Loc) (err : GoInterface) :
    Persistent (putCallOut Q resp err) := by
  unfold putCallOut; infer_instance

instance rangeCallOut_persistent (Q : RangeRespM → IProp GF) (resp : Loc) (err : GoInterface) :
    Persistent (rangeCallOut Q resp err) := by
  unfold rangeCallOut; infer_instance

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

/-- grpc's call options that hold only scalars (see the file header). -/
def grpcScalarOptTys : List go.GoType :=
  [google_golang_org.grpc.StaticMethodCallOption.ty, google_golang_org.grpc.FailFastCallOption.ty,
    google_golang_org.grpc.MaxSendMsgSizeCallOption.ty,
    google_golang_org.grpc.MaxRecvMsgSizeCallOption.ty]

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

/-! ## Context errors -/

/-- **The context `ci` (descriptor `cd`)'s `Err()` returns client errors** (persistent; see the
file header): `isContext`'s triple of `Err()` (`"#HErr"`: a non-nil error makes the context done,
`ContextClosed`, after which `Err()` is non-nil: Go's "successive calls to Err return the same
error"), with `clientErr` of the error returned. -/
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
        ⌜clientErr err⌝ -∗ Φ #err) -∗
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

/-- **The `*kv` `api`** (what `NewKV` returns) over a `*retryKVClient` on a connection to `K`. -/
def kvObjAt (api : Loc) (K : KVConn GF) : IProp GF :=
  iprop(∃ (rkv conn : Loc) (sl : GoSlice),
    structFieldRef go_etcd_io.etcd.client.v3.kv go!"remote" api ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryKVClient.ty) #rkv :
        GoInterface) ∗
    retryKVAt rkv conn ∗ isKVConn conn K ∗
    structFieldRef go_etcd_io.etcd.client.v3.kv go!"callOpts" api ↦□ sl ∗ callOptsAt sl)

instance kvObjAt_persistent (api : Loc) (K : KVConn GF) : Persistent (kvObjAt api K) := by
  unfold kvObjAt; infer_instance

/-- **What `NewKV` reads of the `*Client` `cl`**: its connection (to `K`) and call options, fixed
since `clientv3.New` (an assumption about the unverified constructor). -/
def clientKVAt (cl : Loc) (K : KVConn GF) : IProp GF :=
  iprop(⌜cl ≠ null⌝ ∗ ∃ (conn : Loc) (sl : GoSlice),
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"conn" cl ↦□ conn ∗ isKVConn conn K ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"callOpts" cl ↦□ sl ∗ callOptsAt sl)

instance clientKVAt_persistent (cl : Loc) (K : KVConn GF) : Persistent (clientKVAt cl K) := by
  unfold clientKVAt; infer_instance

end defs

end EtcdGrove
end Perennial
