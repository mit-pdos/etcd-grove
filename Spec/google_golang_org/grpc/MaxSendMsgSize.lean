/-
`grpc.MaxSendMsgSize` (grpc-go, assumed: `server.go`).

Users: `v3rpc.Server` (`grpc.go:86`: `math.MaxInt32`).

Why true: a reply over the limit fails the call with `ResourceExhausted` after the run (grpc's own error to the client).

Changes: from `specs-ref/.../grpc/MaxSendMsgSize.lean`.

Margin: none.
-/
module

public import Spec.google_golang_org.grpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Grpc

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `grpc.MaxSendMsgSize(...)`: a server option acting as shown. -/
def MaxSendMsgSize.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ True }}
    (App (Val (@! google_golang_org.grpc.MaxSendMsgSize)) (Val #n))
  {{ (v : GoInterface), RET #v; srvOptAt v (id) }}

end spec

end Grpc
end EtcdGrove
end Perennial
