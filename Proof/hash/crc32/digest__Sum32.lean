/-
The proof of `Spec/hash/crc32/digest__Sum32.lean`.
-/
module

public import Spec.hash.crc32.digest__Sum32

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
variable [hash.crc32.Assumptions]

theorem hash.crc32.digest.Sum32.wp_proof : hash.crc32.digest.Sum32.spec (GF := GF) (hG := hG) := by
  intro d dq x
  wp_start as Hd
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hd
  ihave Hd := typedPointsto_split _ _ _ $$ Hd
  simp only [TypedPointsto.typedPointstoDef]
  icases Hd with ⟨Hc, Ht, -⟩
  wp_auto
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end EtcdGrove
end Perennial
