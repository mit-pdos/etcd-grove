/-
Proof of `Spec/github_com/jonboulle/clockwork/NewRealClock.lean`, over clockwork v0.5.0's code: Lean-first
(no Rocq counterpart).

`NewRealClock()` is `&realClock{}` as a `Clock`, whose `Now` and `After` meet `clockOk`'s triples by
their specs (`realClock.Now.spec`, `realClock.After.spec`).
-/
module

public import Spec.github_com.jonboulle.clockwork.NewRealClock
public import Spec.github_com.jonboulle.clockwork.realClock__Now
public import Spec.github_com.jonboulle.clockwork.realClock__After

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
variable [package_sem : github_com.jonboulle.clockwork.Assumptions]

theorem clockwork.NewRealClock.wp_proof
    (wp_Now : clockwork.realClock.Now.spec (GF := GF) (hG := hG))
    (wp_After : clockwork.realClock.After.spec (GF := GF) (hG := hG)) :
    clockwork.NewRealClock.spec (GF := GF) (hG := hG) := by
  wp_start
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_auto
  wp_bind (App (Val (GoInstruction (GoAlloc _))) _)
  iapply (IntoValTyped.wp_alloc (t := github_com.jonboulle.clockwork.realClock.ty) (zero_val github_com.jonboulle.clockwork.realClock))
  · itrivial
  inext
  iintro %l -
  wp_auto
  iapply HΦ
  unfold clockwork.clockOk
  iexists (interface.mk (go.GoType.PointerType github_com.jonboulle.clockwork.realClock.ty) #l)
  isplitr
  · ipureintro; rfl
  isplitr
  · iexists (-2 ^ 63)
    unfold clockwork.clockLb
    iapply time.isPkgInit_clockLb $$ Htime
  isplitr
  · imodintro
    iintro %Φ'
    imodintro
    iintro _ HΦ'
    iapply wp_Now l $$ Hpkg HΦ'
  · imodintro
    iintro %d %P %n #HP #Hn %Φ'
    imodintro
    iintro _ HΦ'
    iapply wp_After l d P n $$ [] HΦ'
    iframe #

end proof

end EtcdGrove
end Perennial
