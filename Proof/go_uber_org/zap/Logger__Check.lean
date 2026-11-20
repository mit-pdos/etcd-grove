/-
Proof of `Spec/go_uber_org/zap/Logger__Check.lean`: `return log.check(lvl, msg)`, over `check`'s spec
(the trust boundary; until 2026-11-20 `Check` itself was). Lean-first.
-/
module

public import Spec.go_uber_org.zap.Logger__Check
public import Spec.go_uber_org.zap.Logger__check

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_uber_org

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_uber_org.zap.Assumptions]

theorem zap.Logger.Check.wp_proof
    (wp_check : zap.Logger.check.spec (GF := GF) (hG := hG)) :
    zap.Logger.Check.spec (GF := GF) (hG := hG) := by
  intro l lvl msg
  wp_start as ⟨#Hl, %Hlvl⟩
  obtain ⟨w, rfl, hw⟩ := Hlvl
  wp_auto
  wp_apply wp_check as %ce Hce
  · iframe Hl
    ipureintro; exact ⟨w, rfl, hw⟩
  iapply HΦ
  iexact Hce

end proof

end EtcdGrove
end Perennial
