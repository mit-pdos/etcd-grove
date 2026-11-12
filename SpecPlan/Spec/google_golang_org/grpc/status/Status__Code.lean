/-
`(*status.Status).Code()` (grpc-go, assumed: `internal/status/status.go`).

Users: `rpctypes.Error` (this batch), `v3rpc.isClientCtxErr`, the client's error classifiers (W0,
1b, 1c).

Why true: `Code()` reads the stored proto's code (`OK` for a `nil` receiver).

Changes: from `specs-ref/Spec/google_golang_org/grpc/status/Code.lean`.

Margin: none.
-/
module

public import SpecPlan.Spec.google_golang_org.grpc.Api

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

/-- `s.Code()`: its code. -/
def Status.Code.spec : Prop :=
  ∀ (s : Loc) (code : w32) (msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ statusAt s code msg }}
    (App (Val (s @!! go.GoType.PointerType google_golang_org.grpc.status.Status.ty @!! go!"Code")) (Val #()))
  {{ RET #code; True }}

end spec

end Grpc
end EtcdGrove
end Perennial
