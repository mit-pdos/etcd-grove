/-
`grpc.MaxConcurrentStreams` (grpc-go, assumed: `server.go`).

Users: `v3rpc.Server` (`grpc.go:87`).

Why true: a stream over the limit waits for the client's transport (HTTP/2 flow control), not the server's code.

Changes: from `specs-ref/.../grpc/MaxConcurrentStreams.lean`.

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

/-- `grpc.MaxConcurrentStreams(...)`: a server option acting as shown. -/
def MaxConcurrentStreams.spec : Prop :=
  ∀ (n : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ True }}
    (App (Val (@! google_golang_org.grpc.MaxConcurrentStreams)) (Val #n))
  {{ (v : GoInterface), RET #v; srvOptAt v (id) }}

end spec

end Grpc
end EtcdGrove
end Perennial
