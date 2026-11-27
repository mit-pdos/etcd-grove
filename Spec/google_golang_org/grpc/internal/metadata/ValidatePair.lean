/-
`ValidatePair(key, vals...)` (grpc's `internal/metadata/metadata.go`): the key is `ValidateKey`'s, and
unless it ends in `-bin` every value is printable ASCII.
-/
module

public import Proof.google_golang_org.grpc.HeaderFields
public import Spec.fmt.ErrorOk

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

/-- `ValidatePair(key, vals...)` returns `nil` exactly when the pair is `pairOk`; otherwise an error
`fmt` formats by its `Error()` (`fmt.Errorf`'s). The values' slice comes back. -/
abbrev imetadata.ValidatePair.spec : Prop :=
  ∀ (key : GoString) (vals_sl : GoSlice) (vs : List GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.internal.metadata ∗
      vals_sl ↦*{dq} vs }}
    (App (App (Val (@! google_golang_org.grpc.internal.metadata.ValidatePair)) (Val #key))
      (Val #vals_sl))
  {{ (e : GoInterface), RET #e;
      vals_sl ↦*{dq} vs ∗ ⌜e = .nil ↔ grpcHdr.pairOk key vs⌝ ∗ fmtErrorOkOrNil e }}

end spec

end EtcdGrove
end Perennial
