/-
`ValidateKey(key)` (grpc's `internal/metadata/metadata.go`): a metadata key is non-empty and, unless a
pseudo-header, lower-case `[0-9a-z_.-]`.
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

/-- `ValidateKey(key)` returns `nil` exactly when the key is `keyOk`; otherwise an error `fmt`
formats by its `Error()` (`fmt.Errorf`'s). -/
abbrev imetadata.ValidateKey.spec : Prop :=
  ∀ (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.internal.metadata }}
    (App (Val (@! google_golang_org.grpc.internal.metadata.ValidateKey)) (Val #key))
  {{ (e : GoInterface), RET #e; ⌜e = .nil ↔ grpcHdr.keyOk key⌝ ∗ fmtErrorOkOrNil e }}

end spec

end EtcdGrove
end Perennial
