/-
**The wire: the gRPC KV stub's contract** (the vertical slice's unit V1, 2026-10-13;
`notes/STATUS.md`, "The vertical slice: client to server"; `notes/decisions.md`, "The client's
model as a class the server instantiates; the wire as the handler's theorem transported").
Lean-first, no Rocq counterpart.

etcd's client talks to the server through the generated gRPC stub
(`api/etcdserverpb/rpc_grpc.pb.go`): `kVClient.Range`/`Put`/`DeleteRange`/`Txn` each call
`c.cc.Invoke(ctx, "/etcdserverpb.KV/<M>", in, out, opts...)`, gRPC carries the marshalled request
to the server, whose generated server stub unmarshals it into a fresh request and calls the
registered `KVServer`'s method (`v3rpc.NewKVServer(s)`'s `*kvServer`, proved:
`range_end_to_end`, ..., `Results.lean`), and carries the marshalled response back. Neither gRPC
nor protobuf is translated (names-only), so the stub's four methods are the trust boundary
(`Spec/go_etcd_io/etcd/api/v3/etcdserverpb/kVClient__<M>.lean`, axioms in
`Proof/.../etcdserverpb/kVClient__<M>.lean`), each stated as the server's end-to-end theorem for
that method **transported to the client**:

* the precondition: the client's context (`isContext`), the connection (`connectedTo cc p s E ρ γr
  cid mid n`: the `grpc.ClientConnInterface` `cc` leads to the gRPC server serving the `*kvServer`
  `p` of the server `s`, `kvServerAt`, with the server's facts `isServerReq s E ρ ∗ isServerRead s
  E γr` and its packages' initialization), and the request (`txn.rangeRequestIs in o`, ...);
* the postcondition: the end-to-end theorem's with **every server-side resource removed**
  (`srvCall`: the server context, the id credit, the `leadTimeMu` reader slot; `srvRdCall`: the
  store's reader slots, the logger's; `kvServerAt`), the response **the client's fresh copy** (the
  same formulas of its fields: `hdrFilled`, the answer's facts `rangeAnsOk`, `putApplied`, ...), at
  committed index `0` for the read path (a fresh server-side handler knows no committed index:
  `committedAtLeast γr 0` is free; `rangeAnsOk E γr 0 o resp rv` is what a linearizable read
  gives), the header's revision field without the store's reader slot (`hdrRevC`), and an error
  only as a non-nil error (gRPC hands the client a status error with the handler's code and
  message, not the server's error value: the check's `rpctypes` variable, `togRPCError`'s status).

**Premises** (of the axioms' soundness, not stated in Lean; `notes/STATUS.md` lists them): the
server's per-call resources come from its pool (one id credit from the id budget `□ |==>
idCred`, a `leadTimeMu` reader slot and the store's reader slots: gRPC's
`MaxConcurrentStreams` bounds the concurrent handlers, Perennial's `RWMutex` its readers); the
transport's integrity (no corruption, a call's request and response delivered as sent, at most
once: a lost response is an error to the client); protobuf round-trips (unmarshal of marshal is
the identity on the fields the model reads; protobuf-go decodes an empty `bytes` field as `nil`,
which `irrWireOf`'s `[0]` range ends already account for on the server's side).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKV

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

/-- **The connection** (opaque, the trust boundary): the `grpc.ClientConnInterface` `cc` delivers
the KV service's calls to the gRPC server whose registered KV service is the `*kvServer` `p`
(`v3rpc.NewKVServer`'s, registered by `v3rpc.Server`: `pb.RegisterKVServer(grpcServer,
NewQuotaKVServer(s))`). An axiom: `grpc.ClientConn` and `grpc.Server` are names-only. -/
axiom grpcConnTo {GF : BundledGFunctors} [FfiSyntax] (cc : GoInterface) (p : Loc) : IProp GF

section wire
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`cc` is connected to the KV service `p` of the server `s`** (persistent): the connection
(`grpcConnTo`, opaque), the server's packages initialized, the server's facts the end-to-end
theorems assume (`isServerReq s E ρ`, `isServerRead s E γr`) and the `*kvServer` `p`
(`kvServerAt`, its ids `cid`, `mid` and transaction budget `n`, at the read path's committed
index `0`). -/
def connectedTo (cc : GoInterface) (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (cid mid n : w64) : IProp GF :=
  iprop(□ grpcConnTo cc p ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
    isServerReq s E ρ ∗ isServerRead s E γr ∗ kvServerAt p s (srvKVAns s E ρ γr (W64 0)) cid mid n)

instance connectedTo_persistent (cc : GoInterface) (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (cid mid n : w64) : Persistent (connectedTo cc p s E ρ γr cid mid n) := by
  unfold connectedTo; infer_instance

/-- The response header `h`'s revision field in the client's copy: `rv'`, which is the server's
answer's revision `rv` unless that was `0` (`hdrRevOut` without the store's reader slots, which
the server's `fill` holds when it reads the KV's revision for a `0`; the server's answers are
never at `0`: their logs have `NewStore`'s two revisions). -/
def hdrRevC (h : Loc) (rv rv' : w64) : IProp GF :=
  iprop(⌜rv ≠ W64 0 → rv' = rv⌝ ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ rv')

/-! ## The client's view of the four answers -/

/-- **What `kVClient.Range` returns** for the range `o` (`range_end_to_end`'s postcondition,
transported; see the file header). -/
def rangeOutC (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) (o : OpFull) (resp : Loc)
    (err : GoInterface) : IProp GF :=
  match rangeCheck o with
  | some _ => iprop(⌜resp = null ∧ err ≠ GoInterface.nil⌝)
  | none =>
    iprop((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
        structFieldRef etcdserverpb.RangeResponse go!"Header" resp ↦□ h ∗ hdrFilled h cid mid ∗
        hdrRevC h rv rv' ∗ rangeAnsOk E γr (W64 0) o resp rv) ∨
      ⌜resp = null ∧ err ≠ GoInterface.nil⌝)

/-- **What `kVClient.Put` returns** for the put `o` (`put_end_to_end`'s, transported). -/
def putOutC (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) (o : OpFull) (resp : Loc)
    (err : GoInterface) : IProp GF :=
  match putCheck o with
  | some _ => iprop(⌜resp = null ∧ err ≠ GoInterface.nil⌝)
  | none =>
    iprop((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
        structFieldRef etcdserverpb.PutResponse go!"Header" resp ↦□ h ∗ hdrFilled h cid mid ∗
        hdrRevC h rv rv' ∗ putApplied E o resp rv) ∨
      (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ e : GoInterface, putErr E ρ o e))

/-- **What `kVClient.DeleteRange` returns** for the delete `o` (`deleteRange_end_to_end`'s,
transported). -/
def deleteOutC (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) (o : OpFull) (resp : Loc)
    (err : GoInterface) : IProp GF :=
  match deleteCheck o with
  | some _ => iprop(⌜resp = null ∧ err ≠ GoInterface.nil⌝)
  | none =>
    iprop((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
        structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" resp ↦□ h ∗
        hdrFilled h cid mid ∗ hdrRevC h rv rv' ∗ deleteApplied E o resp rv) ∨
      (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ e : GoInterface, deleteErr E ρ o e))

/-- **What `kVClient.Txn` returns** for the transaction `cs`, `ts`, `es` under the server's
budget `n` (`txn_end_to_end`'s, transported): a read-only transaction's run at a certified log
(`txnReadAns`, at committed index `0`), a writing one's application (`txnAppliedAns`), or an
error (a writing one's: the apply's or the proposal's, `txnErrOk`). -/
def txnOutC (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cid mid n : w64)
    (cs : List CmpModel) (ts es : List ReqOp) (resp : Loc) (err : GoInterface) : IProp GF :=
  match txnAllCheck (sint.Z n) cs ts es with
  | some _ => iprop(⌜resp = null ∧ err ≠ GoInterface.nil⌝)
  | none =>
    iprop((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
        structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ h ∗ hdrFilled h cid mid ∗
        hdrRevC h rv rv' ∗ ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
          if txn.txnReadonly t then txnReadAns E γr (W64 0) t resp rv
          else txnAppliedAns E t resp rv) ∨
      (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ e : GoInterface, ∃ t,
        ⌜txnModelOf cs ts es = some t⌝ ∗
        if txn.txnReadonly t then iprop(True) else txnErrOk E ρ t e))

/-! ## `pb.KVClient`: the four triples of an interface value -/

/-- **A `pb.KVClient` interface value `rc` talking to the KV service of the server whose apply
thread's environment is `E`** (request names `ρ`, read names `γr`, the `*kvServer`'s ids `cid`,
`mid` and budget `n`; persistent; what `client/v3`'s `kv.remote` holds): the triples of its `Range`, `Put`,
`DeleteRange` and `Txn` (`in`'s request read-only, any call options), each the server's
end-to-end theorem transported (`rangeOutC`, ...). `kvclient_of_conn` (`Results.lean`) proves it
of the generated stub `&kVClient{cc}` from `connectedTo`; the vertical slice's unit V2 proves the
client's `retryKVClient` meets it too. -/
def isKVClient (rc : GoInterfaceOk) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (cid mid n : w64) : IProp GF :=
  iprop(
    (□ ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (inp : Loc) (o : OpFull)
        (opts : GoSlice),
      {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
          context.isContext ctx cd ∗ txn.rangeRequestIs inp o }}
        (App (App (App (Val #(methods rc.ty go!"Range" rc.v)) (Val #(GoInterface.ok ctx)))
          (Val #inp)) (Val #opts))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          rangeOutC E γr cid mid o resp err }}) ∗
    (□ ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (inp : Loc) (o : OpFull)
        (opts : GoSlice),
      {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
          context.isContext ctx cd ∗ txn.putRequestIs inp o }}
        (App (App (App (Val #(methods rc.ty go!"Put" rc.v)) (Val #(GoInterface.ok ctx)))
          (Val #inp)) (Val #opts))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          putOutC E ρ cid mid o resp err }}) ∗
    (□ ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (inp : Loc) (o : OpFull)
        (opts : GoSlice),
      {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
          context.isContext ctx cd ∗ txn.deleteRangeRequestIs inp o }}
        (App (App (App (Val #(methods rc.ty go!"DeleteRange" rc.v)) (Val #(GoInterface.ok ctx)))
          (Val #inp)) (Val #opts))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          deleteOutC E ρ cid mid o resp err }}) ∗
    (□ ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (inp : Loc)
        (cs : List CmpModel) (ts es : List ReqOp) (opts : GoSlice),
      {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
          context.isContext ctx cd ∗ txnReqIs inp cs ts es ∗ txnReqWire inp ts es ∗
          ⌜txnInModel cs ts es⌝ }}
        (App (App (App (Val #(methods rc.ty go!"Txn" rc.v)) (Val #(GoInterface.ok ctx)))
          (Val #inp)) (Val #opts))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          txnOutC E ρ γr cid mid n cs ts es resp err }}))

instance isKVClient_persistent (rc : GoInterfaceOk) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (cid mid n : w64) :
    Persistent (isKVClient rc E ρ γr cid mid n) := by
  unfold isKVClient; infer_instance

end wire

end v3rpc
end EtcdGrove
end Perennial
