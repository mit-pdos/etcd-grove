/-
`grpc.MaxRecvMsgSize` (grpc-go, assumed: `server.go`).

Users: `v3rpc.Server` (`grpc.go:85`: `MaxRequestBytesWithOverhead`).

Why true: a request over the limit is refused before any handler runs, with `ResourceExhausted` (grpc's own error, the client's contract lost: the run never happens).

Changes: from `specs-ref/.../grpc/MaxRecvMsgSize.lean`.

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

/-- `grpc.MaxRecvMsgSize(...)`: a server option acting as shown. -/
def MaxRecvMsgSize.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ True }}
    (App (Val (@! google_golang_org.grpc.MaxRecvMsgSize)) (Val #n))
  {{ (v : GoInterface), RET #v; srvOptAt v (id) }}

end spec

end Grpc
end EtcdGrove
end Perennial
