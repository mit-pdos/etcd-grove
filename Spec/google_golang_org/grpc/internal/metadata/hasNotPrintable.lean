/-
`hasNotPrintable(msg)` (grpc's `internal/metadata/metadata.go`): whether a value has a byte outside
printable ASCII (`0x20`-`0x7E`).
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

/-- `hasNotPrintable(msg)` returns whether some byte of `msg` is not `printable`. -/
abbrev imetadata.hasNotPrintable.spec : Prop :=
  ∀ (msg : GoString),
  {{ (True : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.internal.metadata.hasNotPrintable)) (Val #msg))
  {{ RET #(decide (¬ ∀ b ∈ msg, grpcHdr.printable b)); True }}

end spec

end EtcdGrove
end Perennial
