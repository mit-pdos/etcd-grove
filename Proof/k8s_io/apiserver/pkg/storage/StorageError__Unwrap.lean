/-
The proof of `(*storage.StorageError).Unwrap`: one field load.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.StorageError__Unwrap

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

theorem storage.StorageError.Unwrap.wp_proof : storage.StorageError.Unwrap.spec (GF := GF) (hG := hG) := by
  intro l dq s
  wp_start as Hl
  icases (typedPointsto_not_null_dup _ _ _) $$ Hl with ⟨Hl, %Hn⟩
  iStructNamed Hl
  wp_auto
  ihave Hl : l ↦{dq} s $$ [Code Key ResourceVersion err]
  · iapply typedPointsto_combine l _ _ Hn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply HΦ
  iexact Hl

end proof

end EtcdGrove
end Perennial
