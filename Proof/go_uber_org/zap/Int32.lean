/-
Proof of `Spec/go_uber_org/zap/Int32.lean` (`Field{Key: key, Type: zapcore.Int32Type, Integer: int64(val)}`; until 2026-11-20 a trust-boundary axiom).
Lean-first.
-/
module

public import Spec.go_uber_org.zap.Int32

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

theorem zap.Int32.wp_proof : zap.Int32.spec (GF := GF) (hG := hG) := by
  intro k v
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
