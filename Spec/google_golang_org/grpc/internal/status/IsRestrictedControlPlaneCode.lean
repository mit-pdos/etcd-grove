/-
`istatus.IsRestrictedControlPlaneCode(s)` (grpc's `internal/status/status.go`): whether a status's
code is one gRFC A54 restricts to the control plane (`createHeaderFields` turns a per-RPC
credentials' such status into `Internal`).
-/
module

public import Proof.google_golang_org.grpc.HeaderFields

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- Of a status whose `Code()` returns `c` (as `status.FromError`'s post gives it; until 2026-11-23 a
read-only status, `statusAt`, which `FromError` does not give): whether `c` is one of
`restrictedCodes`. -/
abbrev istatus.IsRestrictedControlPlaneCode.spec : Prop :=
  ∀ (s : Loc) (c : w32),
  {{ □ (∀ Φ : val → IProp GF, ▷ Φ #c -∗
      WP (App (Val (s @!! go.GoType.PointerType google_golang_org.grpc.status.Status.ty @!! go!"Code"))
        (Val #())) {{ Φ }}) }}
    (App (Val (@! google_golang_org.grpc.internal.status.IsRestrictedControlPlaneCode)) (Val #s))
  {{ RET #(decide (c ∈ grpcHdr.restrictedCodes)); True }}

end spec

end EtcdGrove
end Perennial
