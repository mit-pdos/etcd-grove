/-
**LOCAL, until the integration pin bump (perennial#692; delete then):** a spec of Perennial's
`internal/gomodel.Choose()` (any `bool`), proved from its primitive stub's model
(`Perennial/TrustedCode/internal/gomodel.lean`, `Choose.impl := λ: <>, ArbitraryInt =⟨go.uint64⟩
#(W64 0)`) through the translation's `FuncUnfold`. Perennial's Go-model work adds the package's
specs; this file then goes, and its users take Perennial's. A defs module (no `wp_proof`), so the
proofs of the standard-library models that call `Choose` import it.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.internal.gomodel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [_root_.Perennial.internal.gomodel.Assumptions]

/-- `gomodel.Choose()` returns some `bool` (LOCAL: see the file header). -/
theorem internal.gomodel.Choose.wp_local :
    {{ (True : IProp GF) }}
      (App (Val (@! _root_.Perennial.internal.gomodel.Choose)) (Val #()))
    {{ (b : Bool), RET #b; True }} := by
  wp_start as -
  wp_apply wp_ArbitraryInt as %x -
  try wp_auto
  iapply HΦ
  itrivial

/-- `gomodel.ChooseUint64()` returns some `uint64` (LOCAL: see the file header). -/
theorem internal.gomodel.ChooseUint64.wp_local :
    {{ (True : IProp GF) }}
      (App (Val (@! _root_.Perennial.internal.gomodel.ChooseUint64)) (Val #()))
    {{ (x : w64), RET #x; True }} := by
  wp_start as -
  wp_apply wp_ArbitraryInt as %x -
  try wp_auto
  iapply HΦ
  itrivial

end proof
end EtcdGrove
end Perennial
