/-
Trust boundary: `(*grpc.Server).Serve` (an axiom; see `Spec/google_golang_org/grpc/Server__Serve.lean`).
-/
module

public import Spec.google_golang_org.grpc.Server__Serve

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (item 4, the server start): grpc's `Serve` accepts connections on `lis` and
serves each in goroutines of its own (what the calls do: `grpc.serve`, `grpc.serveStream`, from
`grpc.start`'s tokens); it returns only with a non-nil error (the listener failed permanently, or
the server was stopped), closing `lis`. Nothing it does touches the caller's resources.

Since 2026-10-31 (`notes/reply-size.md`): grpc marshals a reply before any size check, and the
codec's `make` panics above `grpcReplyMax`. This axiom's resource (`grpcServerAt`,
`grpcStreamServerAt`, `grpcServeTok`) comes only from `grpc.start`, under `grpcRepliesFit`, so no
reply exceeds it. A reply in `(2 ^ 31 - 1, 2 ^ 48]` fails with `ResourceExhausted`. -/
axiom grpc.Server.Serve.wp_proof : grpc.Server.Serve.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
