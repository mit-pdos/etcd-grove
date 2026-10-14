/-
**The transport contract** (unit C1, 2026-10-14; the trust boundary between etcd's client and
server, an axiom: `Proof/google_golang_org/grpc/ClientConn__Invoke.lean`): grpc's
`(*ClientConn).Invoke` of the KV service's unary methods `Put` and `Range`, on a connection to
a KV service (`isKVConn conn K`, `client/v3/InvKVConn.lean`), with the interceptors the client
installed at dial (`client.go`: `unaryClientInterceptor(withMax(unaryMaxRetries), ...)`, the
retry interceptor of `retry_interceptor.go`) inside the boundary. Lean-first (no Rocq
counterpart); the design and its justification: `notes/decisions.md`, "The client meets the
server (unit C1)".
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

/-- **`conn.Invoke(ctx, "/etcdserverpb.KV/Put", in, out, opts...)`** on a connection to the KV
service `K`: the call marshals the request `in` (the caller's, owned: protobuf's marshaling
writes its size cache), sends it, and, if the reply is a success, unmarshals it into `out` (a
zero `*PutResponse` the caller owns). What it returns:

* `nil`: a run of the server's handler (`K.put`, with the runtime's resources `K.R`) on a copy of
  the request (the server's model of it: `putReqOp`, `txn.putOpOf` of `in`'s fields) answered
  `(resp, nil)`, and `out` holds the same message as `resp` (`putRespMsg`; the run's `Q`, `putRunOk`). Other
  runs may have happened (failed attempts the retry interceptor retried: an attempt that failed
  with a gRPC `Canceled` or `DeadlineExceeded` while `ctx` is not done is retried whatever the
  method, `issues/etcd-client-retry-put-ctx-error.md`); the reply is the last one's.
  The runtime's resources `K.R` are given to every run (the server's runtime holds them: for
  etcd's server, the id budget and reader slots its own results assume, `notes/decisions.md`);
  the run's knowledge `Q` is persistent, so none of them reaches the caller.
* an error (a client error, `clientErr`): nothing about whether, or how often, the handler ran
  (a `Put` may have been applied), nor about `out`.

The request `in` comes back (its visible fields unchanged; only its size cache may differ), and
the options (`callOptsOk`: none writes the caller's memory) stay read-only. -/
abbrev grpc.ClientConn.invokePutSpec : Prop :=
  ∀ (conn : Loc) (K : KVConn GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp out : Loc) (req : etcdserverpb.PutRequest) (k v : GoString) (opts : GoSlice)
    (vs : List GoInterface) (Q : PutRespM → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ isKVConn conn K ∗
      context.isContext ctx cd ∗ inp ↦ req ∗ req.Key' ↦*□ k ∗ req.Value' ↦*□ v ∗
      out ↦ (zero_val etcdserverpb.PutResponse) ∗ opts ↦*□ vs ∗ callOptsOk vs ∗
      putRunOk K (putReqOp req k v) Q }}
    (App (App (App (App (App
      (Val (conn @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty @!! go!"Invoke"))
      (Val #(GoInterface.ok ctx))) (Val #(go!"/etcdserverpb.KV/Put" : GoString)))
      (Val #(interface.mkOk (go.GoType.PointerType etcdserverpb.PutRequest.ty) #inp : GoInterface)))
      (Val #(interface.mkOk (go.GoType.PointerType etcdserverpb.PutResponse.ty) #out : GoInterface)))
      (Val #opts))
  {{ (err : GoInterface), RET #err;
      (∃ req' : etcdserverpb.PutRequest, inp ↦ req' ∗
        ⌜req'.Key' = req.Key' ∧ req'.Value' = req.Value' ∧ req'.Lease' = req.Lease' ∧
          req'.PrevKv' = req.PrevKv' ∧ req'.IgnoreValue' = req.IgnoreValue' ∧
          req'.IgnoreLease' = req.IgnoreLease'⌝) ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg out m ∗ □ Q m) ∨
        ⌜err ≠ GoInterface.nil ∧ clientErr err⌝) }}

/-- **`conn.Invoke(ctx, "/etcdserverpb.KV/Range", in, out, opts...)`**: as `invokePutSpec`, for a
range: the server's model of the request is `rangeReqOp` (`txn.rangeOpOf` of `in`'s fields, its
range end the contents of `RangeEnd`: the wire does not carry an empty field, which the server
decodes as `nil`). A range is repeatable: the retry interceptor retries it on `Unavailable` (with
`withRepeatablePolicy`), so several runs may have read; the reply is the last one's. -/
abbrev grpc.ClientConn.invokeRangeSpec : Prop :=
  ∀ (conn : Loc) (K : KVConn GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp out : Loc) (req : etcdserverpb.RangeRequest) (k e : GoString) (opts : GoSlice)
    (vs : List GoInterface) (Q : RangeRespM → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ isKVConn conn K ∗
      context.isContext ctx cd ∗ inp ↦ req ∗ req.Key' ↦*□ k ∗ req.RangeEnd' ↦*□ e ∗
      out ↦ (zero_val etcdserverpb.RangeResponse) ∗ opts ↦*□ vs ∗ callOptsOk vs ∗
      rangeRunOk K (rangeReqOp req k e) Q }}
    (App (App (App (App (App
      (Val (conn @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty @!! go!"Invoke"))
      (Val #(GoInterface.ok ctx))) (Val #(go!"/etcdserverpb.KV/Range" : GoString)))
      (Val #(interface.mkOk (go.GoType.PointerType etcdserverpb.RangeRequest.ty) #inp :
        GoInterface)))
      (Val #(interface.mkOk (go.GoType.PointerType etcdserverpb.RangeResponse.ty) #out :
        GoInterface)))
      (Val #opts))
  {{ (err : GoInterface), RET #err;
      (∃ req' : etcdserverpb.RangeRequest, inp ↦ req') ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg out m ∗ □ Q m) ∨
        ⌜err ≠ GoInterface.nil ∧ clientErr err⌝) }}

/-- **grpc's `Invoke` of the KV service's `Put` and `Range`** (see each). -/
abbrev grpc.ClientConn.Invoke.spec : Prop :=
  grpc.ClientConn.invokePutSpec (GF := GF) (hG := hG) ∧
    grpc.ClientConn.invokeRangeSpec (GF := GF) (hG := hG)

end spec

end EtcdGrove
end Perennial
