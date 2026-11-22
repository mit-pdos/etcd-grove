/-
Proof of `Spec/go_uber_org/zap/Float64.lean` (`Field{Key: key, Type: zapcore.Float64Type, Integer:
int64(math.Float64bits(val))}`; over Perennial's `math.Float64bits`). Lean-first.
-/
module

public import Spec.go_uber_org.zap.Float64
public import Perennial.Spec.math.Float64bits

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

theorem zap.Float64.wp_proof
    (wp_Float64bits : _root_.Perennial.math.Float64bits.spec (GF := GF) (hG := hG)) :
    zap.Float64.spec (GF := GF) (hG := hG) := by
  intro k v
  wp_start as #Hzap
  ihave #Hmath : isPkgInit (PROP := IProp GF) pkg_id.math $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Float64bits v $$ [$Hmath]
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
