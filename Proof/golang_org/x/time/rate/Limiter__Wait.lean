/-
Proof of `Spec/golang_org/x/time/rate/Limiter__Wait.lean` over the real code (x/time/rate v0.16.0,
`rate.go:232-235`: `WaitN(ctx, 1)`; rate-wait, 2026-11-23: until then a trust-boundary axiom, the
token bucket's floats and then `wait`'s `fmt.Errorf`, `select`s and timer closure untranslated).
-/
module

public import Spec.golang_org.x.time.rate.Limiter__WaitN

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode golang_org.x.time

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : golang_org.x.time.rate.Assumptions]

theorem rate.Limiter.Wait.wp_proof
    (wp_WaitN : rate.Limiter.WaitN.spec (GF := GF) (hG := hG)) :
    rate.Limiter.Wait.spec (GF := GF) (hG := hG) := by
  intro rl c cd
  wp_start as ⟨#Hl, #Hc⟩
  wp_auto
  wp_apply wp_WaitN $$ [$Hpkg $Hl $Hc] as %err -
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
