/-
`EncodeDuration(t)` (grpc's `internal/grpcutil/encode_duration.go`): the `grpc-timeout` header's value
of a duration.
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

/-- `EncodeDuration(t)` returns `encodeDurationOf t`. -/
abbrev grpcutil.EncodeDuration.spec : Prop :=
  ∀ (t : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.internal.grpcutil }}
    (App (Val (@! google_golang_org.grpc.internal.grpcutil.EncodeDuration)) (Val #t))
  {{ RET #(grpcHdr.encodeDurationOf t); True }}

end spec

end EtcdGrove
end Perennial
