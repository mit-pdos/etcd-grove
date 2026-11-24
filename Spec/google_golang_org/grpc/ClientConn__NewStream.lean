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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`conn.NewStream(ctx, desc, method, opts...)`** on a connection with no default call options
(`grpcConn conn addrs ics []`, what etcd's client dials with: `isEtcdConn`), for a streaming method
registered at every address of `addrs`, each with its own content and stream specification
(`isGrpcStreams addrs method Up Spec`; 2026-10-21, D32: until then one address, `[addr]`), a
context (`ctxOk`), a stream descriptor `desc` (read-only) of a client stream (`ClientStreams`;
2026-10-18, the axiom audit: for a server-streaming method with retries etcd's interceptor
returns a `serverStreamingRetryingStream`, which on a failed first `RecvMsg` opens a second stream
and replays the sends, so the handler runs twice, which one `γ` cannot describe) and the client's
call options (`streamCallOptsOk`: scalar options, the client's retry policy options, or, since
2026-10-18 (item 1, the client lease: the lessor's `withMax(0)`), any `retryOption` that builds the
interceptor's options): a client stream at some address `a` of `addrs` (`cliStreamIs`: a raw
client end, both tokens at `[]`, `a`'s content `Up a` and stream specification `Spec a γ Dn` for
the content `Dn` its responses will carry), or a client error grpc's `status` accepts and a `nil`
stream. `a` is ghost: the program does not learn it. (D32) True of grpc-go: `newClientStream`
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
when `ctx` is (with a quiet `ctx`, only when the stream ends). Since G2 (2026-10-30): the
registration is metadata-indexed (`isGrpcStreamsMd`; a plain one is the instance at a spec
ignoring it). Since phase 7's switch (SW1, 2026-11-24, `notes/phase7-endstate.md` §2, R2; ledger
2026-11-24): the post fixes neither the metadata nor the address. The client's content `Up` is one for
every address (a transparent retry before the stream is committed re-picks the transport,
`getTransportConn`, the model's `modelChooseAddr`, `model_clientconn.go:322`, and replays the requests
sent, so their content must suit any address; the review of SW1, finding 2), and the address the
stream ran at is learned with each response, as the metadata (`streamDispIs γ a md`). The stream is dispatched with the metadata of the attempt the
server ran, which a transparent retry recomputes (`createHeaderFields` again, the per-RPC credentials
called again: `models/grpc/model_transport.go:239-245`, from `stream.go:482-505`), so it is not known
when `NewStream` returns; the stream specification holds at every metadata an attempt may deliver
(`a ∈ addrs` and `clientAttemptMdI conn om md`: the interceptor's `withVersion(ctx)` (`retry_interceptor.go:120`), the
credentials' data, then the outgoing metadata and `added`, reserved keys skipped:
`internal/transport/http2_client.go:579-655`), at that dispatch's content `Dn a md`. Until then one
`a` and one `md` were fixed when `NewStream` returned ("grpc sends the headers once"), with one `Dn`:
false under a retry with refreshed credentials. (R1) A refused first attempt whose replay's write
fails ends the stream with a bare `io.EOF` and no handler run: `cliStreamIs`' error arm
(`cliStreamErr`), not its `downClosed` one. True of a connection whose stream interceptor is etcd's
(`dialOk`). Since stage A of the per-type models (2026-11-07): the
request's and the reply's models are the ones registered for their Go types (`streamReqModelOf`,
`streamRepModelOf`). (errdesc stage 1, 2026-11-20) The attempt's metadata is over the context's outgoing
metadata `om`, which the precondition relates to `ctx` (`metadata.outMD ctx om`); until then over the
pure `metadata.outgoingOf ctx`. Since 2026-11-23 (#24's S2 signatures, the resource parameter): the
caller gives a resource `R` of the connection's family (`Ok R`, `grpcConn`'s), which comes back with
the result; grpc-go v1.84 lends it to the per-RPC credentials, which `newClientStream` calls on the
caller's goroutine for the stream's first attempt and for each transparent retry of its creation
(`stream.go:495-508`, `clientStream.withRetry`); etcd's stream interceptor (inside the boundary)
reaches them only on that goroutine too, through grpc's streamer and through its `getToken`'s
`Authenticate` call (a unary call on the same connection). The stream's later operations take their
own (`cliStreamIs … Ok`). -/
abbrev grpc.ClientConn.NewStream.spec : Prop :=
  ∀ (conn : Loc) (addrs : List GoString) (ics : List GoFunc) (Ok : IProp GF → Prop)
    (method : GoString) (Req Rep : StreamMsgT GF),
    streamReqModelOf GF Req.ty = some Req → streamRepModelOf GF Rep.ty = some Rep →
  ∀ (Up : Nat → Req.M → IProp GF)
    (Spec : GoString → GrpcMd → StreamSpec Rep.toStreamMsg) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (om : GrpcMd) (desc : Loc) (opts : GoSlice)
    (vs : List GoInterface) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ grpcConn conn addrs ics [] Ok ∗
      ⌜Ok R⌝ ∗ R ∗
      isGrpcStreamsMd addrs method (fun _ => Up) Spec ∗ ctxOk ctx cd ∗ metadata.outMD ctx om ∗
      (∃ d : google_golang_org.grpc.StreamDesc, desc ↦□ d ∗ ⌜d.ClientStreams' = true⌝) ∗
      opts ↦*□ vs ∗ streamCallOptsOk vs }}
    (App (App (App (App
      (Val (conn @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty @!! go!"NewStream"))
      (Val #(GoInterface.ok ctx))) (Val #desc)) (Val #method)) (Val #opts))
  {{ (cs err : GoInterface), RET (PairV #cs #err); R ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (γ : StreamNames) (Dn : GoString → GrpcMd → Nat → Rep.M → IProp GF)
          (cd' : context.ContextDesc (IProp GF)),
        cliStreamIs cs γ Req.toStreamMsg Rep.toStreamMsg Up
          (fun a md => iprop(⌜a ∈ addrs⌝ ∗ clientAttemptMdI conn om md)) Dn cd' Ok ∗
        cliSendTok (Req := Req.toStreamMsg) γ [] ∗ cliRecvTok (Rep := Rep.toStreamMsg) γ [] ∗
        □ (∀ a md, ⌜a ∈ addrs⌝ -∗ clientAttemptMdI conn om md -∗ Spec a md γ (Dn a md))) ∨
      (⌜cs = GoInterface.nil⌝ ∗ cliStreamErr err)) }}

end spec

end EtcdGrove
end Perennial
