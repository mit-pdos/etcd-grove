/-
`(*grpc.ClientConn).NewStream(ctx, desc, method, opts...)` (grpc's `stream.go`): a client stream
of a streaming method (the watch slice's unit W-W; the stream analogue of `ClientConn.Invoke`,
`ClientConn__Invoke.lean`). The trust boundary (an axiom, `Proof/google_golang_org/grpc/
ClientConn__NewStream.lean`); the vocabulary is `Proof/google_golang_org/grpc/InvGrpcStream.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcStream
public import Proof.go_etcd_io.etcd.client.v3.InvRetry

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
(`grpcConn conn addrs ics []`, what etcd's client dials with: `isEtcdConn`), for a streaming method
registered at every address of `addrs`, each with its own content and stream specification
(`isGrpcStreams addrs method Up Spec`; 2026-10-21, D30: until then one address, `[addr]`), a
context (`ctxOk`), a stream descriptor `desc` (read-only) of a client stream (`ClientStreams`;
2026-10-18, the axiom audit: for a server-streaming method with retries etcd's interceptor
returns a `serverStreamingRetryingStream`, which on a failed first `RecvMsg` opens a second stream
and replays the sends, so the handler runs twice, which one `γ` cannot describe) and the client's
call options (`streamCallOptsOk`: scalar options, the client's retry policy options, or, since
2026-10-18 (item 1, the client lease: the lessor's `withMax(0)`), any `retryOption` that builds the
interceptor's options): a client stream at some address `a` of `addrs` (`cliStreamIs`: a raw
client end, both tokens at `[]`, `a`'s content `Up a` and stream specification `Spec a γ Dn` for
the content `Dn` its responses will carry), or a client error grpc's `status` accepts and a `nil`
stream. `a` is ghost: the program does not learn it. (D30) True of grpc-go: `newClientStream`
takes one transport from the picker (round-robin over the READY subchannels of the resolver's
addresses), and every message of the stream goes on that one HTTP/2 stream, to one server's
handler run; grpc's transparent retry of a stream's creation moves it only when the first server
did not process it, and etcd's service configuration has no retry policy, so no message is
replayed on a second server. Inside the boundary, besides the transport (`InvGrpcStream.lean`'s
header): the connection's stream interceptor, etcd's `streamClientInterceptor(withMax(0), ...)`
(`retry_interceptor.go`, as `clientv3.New` dials: `withVersion`'s metadata, `getToken`, which may
fail, `filterCallOptions` taking the retry options out and applying them to a copy of the
interceptor's options; with no retry (`max` `0`), then grpc's streamer; with retries asked of a
client stream (`ClientStreams`), an `Unimplemented` error); grpc's own stream (`newClientStream`,
its retries of the stream's creation). The stream's context (`cd'`) is grpc's child of `ctx`: done
when `ctx` is (with a quiet `ctx`, only when the stream ends). -/
abbrev grpc.ClientConn.NewStream.spec : Prop :=
  ∀ (conn : Loc) (addrs : List GoString) (ics : List GoFunc) (method : GoString)
    (Req Rep : StreamMsg GF) (Up : GoString → Nat → Req.M → IProp GF)
    (Spec : GoString → StreamSpec Rep) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (desc : Loc) (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ grpcConn conn addrs ics [] ∗
      isGrpcStreams addrs method Up Spec ∗ ctxOk ctx cd ∗
      (∃ d : google_golang_org.grpc.StreamDesc, desc ↦□ d ∗ ⌜d.ClientStreams' = true⌝) ∗
      opts ↦*□ vs ∗ streamCallOptsOk vs }}
    (App (App (App (App
      (Val (conn @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty @!! go!"NewStream"))
      (Val #(GoInterface.ok ctx))) (Val #desc)) (Val #method)) (Val #opts))
  {{ (cs err : GoInterface), RET (PairV #cs #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (a : GoString) (γ : StreamNames) (Dn : Nat → Rep.M → IProp GF)
          (cd' : context.ContextDesc (IProp GF)),
        ⌜a ∈ addrs⌝ ∗ cliStreamIs cs γ Req Rep (Up a) Dn cd' ∗ cliSendTok (Req := Req) γ [] ∗
        cliRecvTok (Rep := Rep) γ [] ∗ Spec a γ Dn) ∨
      (⌜cs = GoInterface.nil⌝ ∗ cliStreamErr err) }}

end spec

end EtcdGrove
end Perennial
