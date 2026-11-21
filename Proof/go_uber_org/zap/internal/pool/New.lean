/-
Proof of `Spec/go_uber_org/zap/internal/pool/New.lean` over the real code (prove-misc, 2026-11-20).
-/
module

public import Spec.go_uber_org.zap.internal.pool.New

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_uber_org.zap.internal.pool.Assumptions]

theorem zap.internal.pool.New.wp_proof : zap.internal.pool.New.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ fn
  wp_start
  wp_auto
  rw [recv_eq_func_mk BAnon BAnon]
  wp_auto
  wp_end

end proof

end EtcdGrove
end Perennial
