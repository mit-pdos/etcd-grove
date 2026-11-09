/-
`status.Code(err)` (grpc-go, assumed: `status/status.go`).

Users: the client's `isContextError` (`retry_interceptor.go:362`, 1c), Kubernetes' store and
watcher (`store.go:956,959`, `watcher.go:316,397`).

Why true: `FromError(err)`'s status's code (`OK` for `nil`, `Unknown` for an error with no status).

Changes: restored (round 1).

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

/-- `status.Code(err)`: the code of the error's status view. -/
def Code.spec : Prop :=
  ∀ (err : GoInterface) (code : w32) (msg : GoString) (ok : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ errView err code msg ok }}
    (App (Val (@! google_golang_org.grpc.status.Code)) (Val #err))
  {{ RET #code; True }}

end spec

end Grpc
end EtcdGrove
end Perennial
