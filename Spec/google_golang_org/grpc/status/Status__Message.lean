/-
`(*status.Status).Message()` (grpc-go, assumed: `internal/status/status.go`).

Users: `rpctypes.ErrorDesc`, `rpctypes.Error` (this batch), `v3rpc.isClientCtxErr`.

Why true: `Message()` reads the stored proto's message (`""` for a `nil` receiver).

Changes: new (it was part of `FromError`'s old post).

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

/-- `s.Message()`: its message. -/
def Status.Message.spec : Prop :=
  ∀ (s : Loc) (code : w32) (msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ statusAt s code msg }}
    (App (Val (s @!! go.GoType.PointerType google_golang_org.grpc.status.Status.ty @!! go!"Message")) (Val #()))
  {{ RET #msg; True }}

end spec

end Grpc
end EtcdGrove
end Perennial
