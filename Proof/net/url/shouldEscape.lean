/-
The proof of `shouldEscape.spec` (`Spec/net/url/shouldEscape.lean`).
-/
module

public import Spec.net.url.shouldEscape

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.url

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : net.url.Assumptions]

theorem shouldEscape.wp_proof : shouldEscape.spec (GF := GF) (hG := hG) := by
  intro c mode
  wp_start
  icases urlInit_table_get c $$ Hpkg with ⟨%t, #Ht, %Htv⟩
  wp_auto
  have hb : 0 ≤ sint.Z (W64 (uint.Z c)) ∧ sint.Z (W64 (uint.Z c)) < 256 := by word
  rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
  have hidx : sint.Z (W64 (uint.Z c)) = (c.toNat : Int) := by word
  rw [hidx]
  ihave Hel := array_acc (globalAddr table) (c.toNat : Int) DfracDiscarded 256 t
    (encTable c) (by omega) (by simpa using Htv) $$ Ht
  icases Hel with ⟨Hel, -⟩
  wp_auto
  iapply HΦ
  itrivial

end proof

end net.url
end Perennial
