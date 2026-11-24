/-
Proof of `Spec/golang_org/x/time/rate/Limiter__WaitN.lean` over the real code (x/time/rate v0.16.0,
`rate.go:237-249`; rate-wait, 2026-11-23): `wait` with `time.Now()` and the closure over
`time.NewTimer`, which is a timer generator (`rate.newTimerOk`: its channel is the timer's, `isTimer`'s
bag of times; `stop` is the timer's `Stop`; `advance` does nothing).
-/
module

public import Spec.golang_org.x.time.rate.Limiter__WaitN
public import Spec.golang_org.x.time.rate.Limiter__wait
public import Perennial.Spec.time.Now
public import Perennial.Proof.time.Link
public import Perennial.Proof.time.Results

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

theorem rate.Limiter.WaitN.wp_proof
    (wp_Now : _root_.Perennial.time.Now.spec (GF := GF) (hG := hG))
    (wp_wait : rate.Limiter.wait.spec (GF := GF) (hG := hG)) :
    rate.Limiter.WaitN.spec (GF := GF) (hG := hG) := by
  intro rl c cd n
  wp_start as ⟨#Hl, #Hc⟩
  wp_auto
  wp_apply wp_Now as %now -
  wp_apply wp_wait $$ [$Hpkg $Hl $Hc] as %err -
  · iunfold rate.newTimerOk
    iintro %d
    iintro !> %Φ' - HΦ'
    wp_auto
    wp_apply _root_.Perennial.time.wp_NewTimer as %tm %tc %γ #Ht
    ihave #Ht' := Ht
    iunfold _root_.Perennial.time.isTimer at Ht'
    icases Ht' with ⟨#HtC, -, -, #HtB⟩
    wp_auto
    iapply HΦ'
    iframe HtB
    isplit
    · iintro !> %Ψ - HΨ
      wp_apply _root_.Perennial.time.Timer.wp_Stop_timer tm tc γ $$ Ht as %b -
      iapply HΨ
      itrivial
    · iintro !> %Ψ - HΨ
      wp_auto
      iapply HΨ
      itrivial
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
