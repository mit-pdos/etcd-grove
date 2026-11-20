/-
Proof of `Spec/go_uber_org/zap/Logger__Debug.lean`: `if ce := log.check(DebugLevel, msg); ce != nil {
ce.Write(fields...) }`, over `check`'s spec (the trust boundary; until 2026-11-20 `Debug` itself was)
and `zapcore.CheckedEntry.Write`'s. Lean-first.
-/
module

public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.Logger__check
public import Spec.go_uber_org.zap.zapcore.CheckedEntry__Write

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

theorem zap.Logger.Debug.wp_proof
    (wp_check : zap.Logger.check.spec (GF := GF) (hG := hG))
    (wp_Write : zapcore.CheckedEntry.Write.spec (GF := GF) (hG := hG)) :
    zap.Logger.Debug.spec (GF := GF) (hG := hG) := by
  intro l msg fields
  wp_start as #Hl
  wp_auto
  wp_apply wp_check as %ce Hce
  · iframe Hl
    ipureintro; exact ⟨_, rfl, by decide⟩
  by_cases hce : ce = null
  · -- not enabled: nothing to write
    subst hce
    wp_auto
    iapply HΦ
    itrivial
  · icases Hce with (%Hnull | Hce)
    · exact absurd Hnull hce
    rw [decide_eq_false hce]
    wp_auto
    wp_apply wp_Write $$ [Hce]
    · iexact Hce
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
