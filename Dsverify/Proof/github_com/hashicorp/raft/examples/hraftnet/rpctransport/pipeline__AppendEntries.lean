/-
The proof of `rpctransport.pipeline.AppendEntries` (ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/examples/inproc, 241f27e).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline__AppendEntries
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Dsverify.Proof.github_com.hashicorp.raft.ReplBase
public import Perennial.Spec.time.Now

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [π : Net.NetProtoGS] [net.rpc.Assumptions] [net.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline.AppendEntries.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline.AppendEntries.spec (GF := GF) (hG := hG) := by
  intro p γ j T args resp rq rp0 snd prev pt ents lci ss
  wp_start as ⟨#Hp, #Hargs, #Hrq, Hrp, %Hrp0⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  icases pipeShutdown_ok $$ Hraft with ⟨%epc, #Hepc, #Hepcok⟩
  iNamed Hp
  wp_auto
  wp_apply wp_Lock $$ [$Hlock] as ⟨Hlocked, HR⟩
  unfold pipLocked
  icases HR with ⟨%b, Hcl, HcR⟩
  wp_auto
  wp_apply wp_Unlock $$ [$Hlock $Hlocked Hcl HcR]
  · inext; iexists b; iframe
  cases b
  case true =>
    wp_auto
    wp_end
    iright; iexact Hepcok
  wp_auto
  wp_apply wp_Now $$ [$Htime] as %ts -
  wp_apply (lc := 2) (chan.wp_make1 (V := Unit)) as %dc %γd ⟨#Hdcc, -, Hdown⟩
  irename «$r0» => Hfl
  iStructNamed Hfl
  ipersist start
  ipersist req
  ipersist resp
  ipersist done
  imod alloc_broadcast_chan (futErrDone «$r0_ptr») γd dc $$ Hdcc Hdown with Hdc
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, q, γq, «$r0_ptr»
    isplitr; · ipureintro; exact ⟨rfl, rfl⟩
    isplitr; · iapply is_bag_is_chan $$ Hqb
    iapply bag_send_au $$ [$Hlc1 $Hlc2] Hqb [-HΦ «$res0» «$res1» f]
    · unfold futQ
      iexists ts, args, resp, dc, γd, rq, rp0, snd, prev, pt, ents, lci, ss
      iframe
      iframe start req resp done Hargs Hrq
      ipureintro; exact Hrp0
    inext
    wp_auto
    wp_end
    ileft; ipureintro; rfl
  iapply BigAndL.bigAndL_singleton.2
  simp only [chan.blockingClausePre]
  iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, cc, γcl
  isplitr; · ipureintro; rfl
  isplitr; · iapply ownBroadcastChan_is_chan $$ Hclose
  iapply broadcast_chan_receive $$ Hclose
  iintro -
  wp_auto
  wp_end
  iright; iexact Hepcok


end proof

end Perennial
