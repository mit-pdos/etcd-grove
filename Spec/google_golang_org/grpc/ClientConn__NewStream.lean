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
(`grpcConn conn addrs ics []`) dialed with the options `d` (`grpcConnOpts conn d`, `NewClient`'s), whose
stream interceptor relates a caller's outgoing metadata to its attempts' by `F` (`streamMdOk d F`: none,
the caller's own; one, its `streamIcMdIs`), for a streaming method registered at every address of
`addrs` with one client content `Up` and a stream specification per address
(`isGrpcStreamsMd addrs method (fun _ => Up) Spec`), a context (`ctxOk`, outgoing metadata `om`), a
client-streaming descriptor (`ClientStreams`), or a server-streaming one on a connection with no stream
interceptor (an interceptor may retry a server stream by a second call, etcd's with `max > 0`, which
replays its sends to a second handler run; grpc alone retries only an unprocessed first attempt), and
the client's call options (`streamCallOptsOk`). The caller's resource `R` of the connection's family
(`Ok R`) is lent to the per-RPC credentials and comes back. Post: a client stream (`cliStreamIs`, both
tokens at `[]`) whose responses carry the dispatch `(a, md)` (`a ∈ addrs`, `md` an attempt's metadata,
`streamAttemptMd conn F om md`) with the content `Dn a md`, and the stream specification
`Spec a md γ (Dn a md)` at every such dispatch, its errors of the connection's shape (`streamErrShape
d`: grpc's own, a status or `io.EOF`, with no stream interceptor); or a client error of that shape and a
`nil` stream (`cliStreamErr`, which admits a bare `io.EOF`). True of grpc-go v1.84 (inside the
boundary: the stream interceptor, of `streamIcMdIs`): every attempt takes one transport and runs one
handler; a transparent retry happens only of an unprocessed first attempt, before the stream is
committed, and may re-pick the address and call the per-RPC credentials again
(`stream.go:482-508,800-819`), so the dispatch is known only from the responses; the configurations
`grpcResolverAt` and `dialPassthrough` admit have no retry policy. History: `notes/phase7-endstate.md`
§2. (grpc-trusted-T, T6/T7, 2026-11-24) The metadata, the server-streaming descriptor and the error
shape are stated from the connection's options (`grpcConnOpts`, `streamMdOk`, `streamErrShape`); until
then the connection's stream interceptor had to be etcd's (`NewClient`'s `dialOk`) and the metadata was
`clientAttemptMd conn om md`, etcd's, which is now `streamAttemptMd conn etcdVersionMd om md`. -/
abbrev grpc.ClientConn.NewStream.spec : Prop :=
  ∀ (conn : Loc) (addrs : List GoString) (ics : List GoFunc) (Ok : IProp GF → Prop)
    (d : GrpcConnOpts) (F : GrpcMd → GrpcMd → Prop)
    (method : GoString) (Req Rep : StreamMsgT GF),
    streamReqModelOf GF Req.ty = some Req → streamRepModelOf GF Rep.ty = some Rep →
  ∀ (Up : Nat → Req.M → IProp GF)
    (Spec : GoString → GrpcMd → StreamSpec Rep.toStreamMsg) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (om : GrpcMd) (desc : Loc) (opts : GoSlice)
    (vs : List GoInterface) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ grpcConn conn addrs ics [] Ok ∗
      grpcConnOpts conn d ∗ ⌜streamMdOk d F⌝ ∗ ⌜Ok R⌝ ∗ R ∗
      isGrpcStreamsMd addrs method (fun _ => Up) Spec ∗ ctxOk ctx cd ∗ metadata.outMD ctx om ∗
      (∃ sd : google_golang_org.grpc.StreamDesc, desc ↦□ sd ∗
        ⌜sd.ClientStreams' = true ∨ (sd.ServerStreams' = true ∧ d.streamIc = none)⌝) ∗
      opts ↦*□ vs ∗ streamCallOptsOk vs }}
    (App (App (App (App
      (Val (conn @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty @!! go!"NewStream"))
      (Val #(GoInterface.ok ctx))) (Val #desc)) (Val #method)) (Val #opts))
  {{ (cs err : GoInterface), RET (PairV #cs #err); R ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (γ : StreamNames) (Dn : GoString → GrpcMd → Nat → Rep.M → IProp GF)
          (cd' : context.ContextDesc (IProp GF)),
        cliStreamIs cs γ Req.toStreamMsg Rep.toStreamMsg Up
          (fun a md => iprop(⌜a ∈ addrs⌝ ∗ streamAttemptMd conn F om md)) Dn cd' Ok
          (streamErrShape d) ∗
        cliSendTok (Req := Req.toStreamMsg) γ [] ∗ cliRecvTok (Rep := Rep.toStreamMsg) γ [] ∗
        □ (∀ a md, ⌜a ∈ addrs⌝ -∗ streamAttemptMd conn F om md -∗ Spec a md γ (Dn a md))) ∨
      (⌜cs = GoInterface.nil⌝ ∗ cliStreamErr err (streamErrShape d))) }}

end spec

end EtcdGrove
end Perennial
