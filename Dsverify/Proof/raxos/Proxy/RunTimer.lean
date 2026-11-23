/-
Package `proxy`: `common.TimerWithCancel`'s `NewTimerWithCancel`, `SetTimeoutFuntion` and `Start`
(the timer's goroutine calls the function at most once).
-/
module

public import Dsverify.Proof.raxos.Proxy.RunDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]

attribute [local instance] HeapGS.goose_globalGS

theorem wp_NewTimerWithCancel : NewTimerWithCancel_spec (GF := GF) (hG := hG) := by
  intro d
  wp_start
  wp_auto
  wp_apply +noauto (chan.wp_make2 (V := GoInterface) (W64 50)) as %ch %γc ⟨#Hch, %Hcap, Hown⟩
  · ipureintro; constructor <;> word
  imod start_bag (fun _ => iprop(True)) _ ch γc (by simp) $$ Hch Hown with #Hbag
  iapply wp_fupd
  wp_auto
  iStructNamed «$r0»
  ipersist c
  imodintro
  iapply HΦ
  iunfold timerOwn
  iexists _, ch, γc
  iframe
  isplitl [] <;> iassumption

theorem wp_SetTimeoutFuntion : SetTimeoutFuntion_spec (GF := GF) (hG := hG) := by
  intro t d f0 f
  wp_start as Ht
  iunfold timerOwn at Ht
  icases Ht with ⟨%tt, %ch, %γc, Htt, Hd, #Hc, #Hbag, Hf⟩
  wp_auto
  iapply HΦ
  iunfold timerOwn
  iexists tt, ch, γc
  iframe
  isplitl [] <;> iassumption

theorem wp_Start : Start_spec (GF := GF) (hG := hG) := by
  intro t d f
  wp_start as ⟨Ht, Hwp⟩
  iunfold timerOwn at Ht
  icases Ht with ⟨%tt, %ch, %γc, Htt, Hd, #Hc, #Hbag, Hf⟩
  wp_auto
  wp_apply time.wp_NewTimer as %tm %chT %γT #Htimer
  wp_apply wp_fork $$ [t Htt Hf Hwp]
  · iunfold time.isTimer at Htimer
    icases Htimer with ⟨#HC, -, -, #HTbag⟩
    wp_auto_lc 4
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, chT, γT
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ HTbag
      iapply bag_recv_au γT chT _ _ $$ [$Hlc1 $Hlc2] HTbag
      inext
      iintro %v -
      wp_auto
      wp_apply Hwp
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hbag
      iapply bag_recv_au γc ch _ _ $$ [$Hlc3 $Hlc4] Hbag
      inext
      iintro %v -
      wp_auto
      itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  wp_end

end proofs

end Perennial.raxos
