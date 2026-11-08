/-
`ctx.Value(StartTimeKey{})` under `startTimeOk` (sweep repairs 1, B2, 2026-11-08: the trust-boundary
axiom it replaces claimed it of every `isContext`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.context.ValueStartTime

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

theorem context.ValueStartTime.wp_proof : context.ValueStartTime.spec (GF := GF) (hG := hG) := by
  intro ctx
  iintro %Φ #Hst HΦ
  unfold context.startTimeOk
  iapply Hst
  inext
  iintro %v %hv
  iapply HΦ; ipureintro; exact hv

end proof

end EtcdGrove
end Perennial
