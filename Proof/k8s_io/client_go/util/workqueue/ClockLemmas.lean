/-
`clock.RealClock{}` is a clock (`isClock`), from the trust-boundary specs of `k8s.io/utils/clock`'s
`RealClock`, `realTimer` and `realTicker` methods (hypotheses). Lean-first.
-/
module

public import Proof.k8s_io.client_go.util.workqueue.DelayingDefs
public import Spec.k8s_io.utils.clock.RealClock__Now
public import Spec.k8s_io.utils.clock.realTimer__C
public import Spec.k8s_io.utils.clock.realTimer__Stop
public import Spec.k8s_io.utils.clock.realTicker__C
public import Spec.k8s_io.utils.clock.realTicker__Stop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

/-- `clock.RealClock{}` (as a `clock.WithTicker` or `clock.Clock`) is a clock. -/
theorem realClock_isClock
    (wp_Now : clock.RealClock.Now.spec (GF := GF) (hG := hG))
    (wp_NewTimer : clock.RealClock.NewTimer.spec (GF := GF) (hG := hG))
    (wp_NewTicker : clock.RealClock.NewTicker.spec (GF := GF) (hG := hG))
    (wp_timerC : clock.realTimer.C.spec (GF := GF) (hG := hG))
    (wp_timerStop : clock.realTimer.Stop.spec (GF := GF) (hG := hG))
    (wp_tickerC : clock.realTicker.C.spec (GF := GF) (hG := hG))
    (wp_tickerStop : clock.realTicker.Stop.spec (GF := GF) (hG := hG)) :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ⊢
      isClock (interface.mkOk k8s_io.utils.clock.RealClock.ty
        #(k8s_io.utils.clock.RealClock.mk : k8s_io.utils.clock.RealClock)) := by
  iintro #Hpkg
  ihave #Hck : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.clock $$ []
  · iPkgInit
  unfold isClock
  iexists _
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %Φ - HΦ
    iapply (wp_Now _) $$ [$Hck] HΦ
  isplitr
  · iintro %d !> %Φ - HΦ
    wp_apply (wp_NewTimer _ d) $$ [$Hck] as %p #Hp
    iapply HΦ
    unfold isTimerI
    iexists _
    isplitr
    · ipureintro; rfl
    isplitr
    · iintro !> %Φ' - HΦ'
      iapply (wp_timerC p) $$ [$Hck $Hp] HΦ'
    · iintro !> %Φ' - HΦ'
      iapply (wp_timerStop p) $$ [$Hck $Hp] HΦ'
  · iintro %d !> %Φ %hd HΦ
    wp_apply (wp_NewTicker _ d hd) $$ [$Hck] as %p #Hp
    iapply HΦ
    unfold isTickerI
    iexists _
    isplitr
    · ipureintro; rfl
    isplitr
    · iintro !> %Φ' - HΦ'
      iapply (wp_tickerC p) $$ [$Hck $Hp] HΦ'
    · iintro !> %Φ' - HΦ'
      iapply (wp_tickerStop p) $$ [$Hck $Hp] HΦ'

end lemmas

end workqueue
end EtcdGrove
end Perennial
