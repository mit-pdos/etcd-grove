/-
`div(d, r)` (grpc's `internal/grpcutil/encode_duration.go`): `d / r`, rounded up when the remainder is
positive.
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

/-- `div(d, r)` of a non-zero `r` (Go panics dividing by zero) returns `durDiv d r`. -/
abbrev grpcutil.div.spec : Prop :=
  ∀ (d r : w64), sint.Z r ≠ 0 →
  {{ (True : IProp GF) }}
    (App (App (Val (@! google_golang_org.grpc.internal.grpcutil.div)) (Val #d)) (Val #r))
  {{ RET #(grpcHdr.durDiv d r); True }}

end spec

end EtcdGrove
end Perennial
