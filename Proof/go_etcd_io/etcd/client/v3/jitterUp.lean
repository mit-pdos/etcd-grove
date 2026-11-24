/-
Proof of `Spec/go_etcd_io/etcd/client/v3/jitterUp.lean`: `time.Duration(float64(duration) * (1 +
jitter * (rand.Float64()*2 - 1)))`, IEEE 754 steps (`wp_float64_*`) and a float converted to an
integer (any value). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.jitterUp
public import Spec.math.rand.Float64

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem jitterUp.wp_proof (wp_Float64 : rand.Float64.spec (GF := GF) (hG := hG)) :
    jitterUp.spec (GF := GF) (hG := hG) := by
  intro d j
  wp_start
  wp_auto
  wp_apply wp_Float64 as %x -
  (try wp_auto)
  wp_apply wp_float64_mul as %_ -
  (try wp_auto)
  wp_apply wp_float64_sub as %_ -
  (try wp_auto)
  wp_apply wp_float64_mul as %_ -
  (try wp_auto)
  wp_apply wp_float64_add as %_ -
  (try wp_auto)
  wp_apply wp_float64_mul as %_ -
  (try wp_auto)
  wp_apply wp_ArbitraryInt as %r -
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
