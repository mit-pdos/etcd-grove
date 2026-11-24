/-
Proof of `Spec/go_uber_org/zap/Logger__check.lean` over zap's code (zap-z1, 2026-11-23; until then the
trust-boundary axiom of zap's leveled logging, and before 2026-11-20 the five exported methods over it):
zap v1.28.0 `logger.go:322-343`, `if lvl < zapcore.DPanicLevel && !log.core.Enabled(lvl) { return nil }`.
A `zapLoggerOk` logger's core is zapcore's `nopCore`, whose `Enabled` is `false` (`zapcore/core.go:51`),
and the level is below `DPanicLevel`: `check` returns `nil` there, before the rest of its body (the
clock, the core's `Check`, the terminal hooks, the caller and stack annotation).
-/
module

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

theorem zap.Logger.check.wp_proof : zap.Logger.check.spec (GF := GF) (hG := hG) := by
  intro l lvl msg
  wp_start as ⟨#Hok, %Hlvl⟩
  obtain ⟨w, rfl, hw⟩ := Hlvl
  unfold zapLoggerOk zap.nopLogger
  icases Hok with ⟨%Hnn, #⟨#Hcore, -, -, -, -, -, -⟩⟩
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  have hlt : sint.Z w < sint.Z (W8 3) := by word
  rw [decide_eq_true hlt]
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  iapply HΦ
  ileft
  ipureintro
  rfl

end proof

end EtcdGrove
end Perennial
