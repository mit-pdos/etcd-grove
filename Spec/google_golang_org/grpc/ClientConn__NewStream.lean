/-
`(*grpc.ClientConn).NewStream(ctx, desc, method, opts...)` (grpc's `stream.go`): a client stream
of a streaming method (the watch slice's unit W-W; the stream analogue of `ClientConn.Invoke`,
`ClientConn__Invoke.lean`). The trust boundary (an axiom, `Proof/google_golang_org/grpc/
ClientConn__NewStream.lean`); the vocabulary is `Proof/google_golang_org/grpc/InvGrpcStream.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcStream
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`conn.NewStream(ctx, desc, method, opts...)`** on a connection with no default call options
(`grpcConn conn addr ics []`, what etcd's client dials with: `isEtcdConn`), for a streaming method
registered at `addr` (`isGrpcStream addr method Up Spec`), a context (`ctxOk`), a stream
descriptor `desc` (read-only) and the client's call options (`callOptsOk`: scalar options or the
client's retry options): a client stream (`cliStreamIs`: a raw client end, both tokens at `[]`,
and the method's stream specification `Spec γ Dn` for the content `Dn` its responses will carry),
or a client error grpc's `status` accepts and a `nil` stream. Inside the boundary, besides the
transport (`InvGrpcStream.lean`'s header): the connection's stream interceptor, etcd's
`streamClientInterceptor(withMax(0), ...)` (`retry_interceptor.go`, as `clientv3.New` dials:
`withVersion`'s metadata, `getToken`, which may fail, `filterCallOptions` dropping the retry
options; with no retry, then grpc's streamer; with retries asked of a bidirectional stream, an
`Unimplemented` error); grpc's own stream (`newClientStream`, its retries of the stream's
creation). The stream's context (`cd'`) is grpc's child of `ctx`: done when `ctx` is (with a
quiet `ctx`, only when the stream ends). -/
abbrev grpc.ClientConn.NewStream.spec : Prop :=
  ∀ (conn : Loc) (addr : GoString) (ics : List GoFunc) (method : GoString) (Req Rep : StreamMsg GF)
    (Up : Nat → Req.M → IProp GF) (Spec : StreamSpec Rep) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (desc : Loc) (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ grpcConn conn addr ics [] ∗
      isGrpcStream addr method Up Spec ∗ ctxOk ctx cd ∗
      (∃ d : google_golang_org.grpc.StreamDesc, desc ↦□ d) ∗ opts ↦*□ vs ∗ callOptsOk vs }}
    (App (App (App (App
      (Val (conn @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty @!! go!"NewStream"))
      (Val #(GoInterface.ok ctx))) (Val #desc)) (Val #method)) (Val #opts))
  {{ (cs err : GoInterface), RET (PairV #cs #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (γ : StreamNames) (Dn : Nat → Rep.M → IProp GF)
          (cd' : context.ContextDesc (IProp GF)),
        cliStreamIs cs γ Req Rep Up Dn cd' ∗ cliSendTok (Req := Req) γ [] ∗
        cliRecvTok (Rep := Rep) γ [] ∗ Spec γ Dn) ∨
      (⌜cs = GoInterface.nil⌝ ∗ cliStreamErr err) }}

end spec

end EtcdGrove
end Perennial
