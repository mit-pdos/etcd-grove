/-
`(*grpc.ClientConn).Close()` (grpc's `clientconn.go`; grpc-trusted-T, T8, 2026-11-24): the gRPC driver's
`close` section. The trust boundary (an axiom, `Proof/google_golang_org/grpc/ClientConn__Close.lean`;
interim, retired by phase 7's S2d, which proves `Close` over the model). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.google_golang_org.grpc.InvGrpc

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

/-- **`conn.Close()`** on a dialed connection (`grpcConn`) returns, and the connection is closed for
good (`grpcConnClosed conn`, persistent): a call `invoke` makes on it from then on fails at once with
`codes.Canceled` (`grpcInvokerDone`, part of `ClientConn.Invoke`'s attempt contract). Calls and
streams in flight may fail (their specs admit an error at every step). True of grpc-go v1.84 and the
model (`models/grpc/clientconn.go:633-658`): `Close` cancels `cc.ctx`, sets `cc.streams` (grpc-go:
`cc.conns`) to `nil`, closes the resolver wrapper (nil-safe, when idle) and the open streams, and
returns `nil`, or `ErrClientConnClosing` if already closed; nothing sets `cc.streams` again
(`NewClient` alone makes it), so `onCallBegin` fails every later call with `ErrClientConnClosing`,
`status.Error(codes.Canceled, …)`. -/
abbrev grpc.ClientConn.Close.spec : Prop :=
  ∀ (conn : Loc) (addrs : List GoString) (ics : List GoFunc) (dopts : List GoInterface)
    (Ok : IProp GF → Prop),
  {{ grpcConn (GF := GF) conn addrs ics dopts Ok }}
    (App (Val (conn @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty @!!
      go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; grpcConnClosed conn }}

end spec

end EtcdGrove
end Perennial
