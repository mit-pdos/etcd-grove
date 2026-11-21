/-
Proof of `Spec/go_uber_org/zap/Error.lean` (`NamedError("error", err)`: `Skip()` if `err` is nil, else `Field{Key: key, Type: zapcore.ErrorType, Interface: err}`; until 2026-11-20 a trust-boundary axiom).
Lean-first.
-/
module

public import Spec.go_uber_org.zap.Error

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

theorem zap.Error.wp_proof : zap.Error.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start
  wp_auto
  -- `NamedError` (no spec of its own): unfolded, and `Skip()` in it when `err` is nil
  wp_func_call; wp_call
  cases err with
  | nil =>
    wp_auto
    wp_func_call; wp_call
    wp_auto
    iapply HΦ
    itrivial
  | ok i =>
    wp_auto
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
