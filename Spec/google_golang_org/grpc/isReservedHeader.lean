/-
`isReservedHeader(hdr)` (the grpc model's `model_http_util.go`, grpc-go's `http_util.go`): whether a
header key is one grpc sets itself, which `createHeaderFields` skips in the outgoing metadata.
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

/-- `isReservedHeader(h)` returns whether `h` is `reservedHdr`: a pseudo-header or one of the keys
grpc sets (`content-type`, `user-agent`, `te`, `grpc-timeout`, ...). -/
abbrev grpc.isReservedHeader.spec : Prop :=
  ∀ (h : GoString),
  {{ (True : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.isReservedHeader)) (Val #h))
  {{ RET #(decide (grpcHdr.reservedHdr h)); True }}

end spec

end EtcdGrove
end Perennial
