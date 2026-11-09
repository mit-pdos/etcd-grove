/-
`ctx.Value(keepAliveCtxKey{})` under `keepAliveOk` (sweep repairs 1, B2b, 2026-11-08: the
trust-boundary axiom it replaces claimed it of every `isContext`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.context.ValueKeepAlive

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

/-- Unfolds `keepAliveOk` (sweep repairs 1, B2b; until then a trust-boundary axiom). -/
theorem context.ValueKeepAlive.wp_proof : context.ValueKeepAlive.spec (GF := GF) (hG := hG) := by
  intro ctx
  iintro %Φ #Hka HΦ
  unfold context.keepAliveOk
  iapply Hka
  inext
  iintro %v %hv
  iapply HΦ; ipureintro; exact hv

end proof

end EtcdGrove
end Perennial
