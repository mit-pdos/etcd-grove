/-
`(*grpc.ClientConn).NewStream(ctx, desc, method, opts...)` (grpc's `stream.go`): a client stream
of a streaming method (the watch slice's unit W-W; the stream analogue of `ClientConn.Invoke`,
`ClientConn__Invoke.lean`). The trust boundary (an axiom, `Proof/google_golang_org/grpc/
ClientConn__NewStream.lean`); the vocabulary is `Proof/google_golang_org/grpc/InvGrpcStream.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcStreamer
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
(`grpcConn conn addrs ics [] Ok`) dialed with the options `d` (`grpcConnOpts conn d`, `NewClient`'s):
grpc calls the connection's stream interceptor (`d.streamIc`, the last `WithStreamInterceptor`'s)
with grpc's streamer and the caller's arguments, or, with none, the streamer itself, whose contract is
`grpcStreamerOk streamCallOptsOk conn addrs Ok` (`InvGrpcStreamer.lean`: one client stream of a
streaming method registered at `addrs`, the caller's metadata delivered, grpc's errors). Stated as a
weakest precondition, for any postcondition `Ψ`: the call's behavior is the interceptor's, or the
streamer's (as `ClientConn.Invoke`'s, and SpecPlan's `ClientConn.NewStream`). True of grpc-go v1.84
(`stream.go`: `NewStream` combines the connection's default call options, none here, with `opts`,
which `combine` then returns unchanged, and calls `cc.dopts.streamInt(ctx, desc, cc, method,
newClientStream, opts...)` if set, else `newClientStream(ctx, desc, cc, method, opts...)`).
History: until phase7-s3-interceptor (2026-11-26) a Hoare triple stating the stream's post at a
metadata relation `F` the connection's stream interceptor met (`streamMdOk d F`, over the
axiomatized property `streamIcMdIs`), and the stream specification only at the attempts' metadata;
the post at no interceptor is now `grpcStreamerOk`'s, and the form at etcd's interceptor the
theorem `etcdNewStream` (`client/v3/EtcdNewStream.lean`), derived from etcd's proved interceptor.
Before: `notes/phase7-endstate.md` §2; grpc-trusted-T (T5-T7, 2026-11-24). -/
abbrev grpc.ClientConn.NewStream.spec : Prop :=
  ∀ (conn : Loc) (addrs : List GoString) (ics : List GoFunc) (Ok : IProp GF → Prop)
    (d : GrpcConnOpts) (ctx : GoInterface) (desc : Loc) (method : GoString) (opts : GoSlice)
    (Ψ : val → IProp GF),
  isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ grpcConn conn addrs ics [] Ok ∗
      grpcConnOpts conn d ∗
      (∀ str : GoFunc, grpcStreamerOk streamCallOptsOk conn addrs Ok str -∗
        match d.streamIc with
        | none => WP (streamerCall str #ctx #desc #conn #method #opts) {{ Ψ }}
        | some si => WP (streamIcCall si #ctx #desc #conn #method str #opts) {{ Ψ }}) ⊢
    WP (App (App (App (App
      (Val (conn @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty @!! go!"NewStream"))
      (Val #ctx)) (Val #desc)) (Val #method)) (Val #opts)) {{ Ψ }}

end spec

end EtcdGrove
end Perennial
