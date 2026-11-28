/-
The proof of `service.waitFuture` (dsverify-lab's hr3 `waitFuture.lean`, 241f27e, with a timeout argument and the answer's spec a hypothesis).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.waitFuture
public import Perennial.Spec.time.After
public import Perennial.Golang.Theory.Chan.Idioms.Bag

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.service.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.service github_com.hashicorp.raft
  github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.hraftnet.service.waitFuture.wp_proof
    (wp_After : time.After.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.service.waitFuture.spec (GF := GF) (hG := hG) := by
  intro x P Q d hErr
  wp_start as HP
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 1)) as %ech %γe ⟨#Hech, %Hcap, Hown⟩
  · ipureintro; decide
  imod start_bag Q _ ech γe (by simp) $$ Hech Hown with #Hbag
  ipersist f
  ipersist errCh
  wp_apply wp_fork $$ [HP]
  · wp_auto
    wp_apply hErr $$ [$Hraft $HP] as %err Hq
    wp_apply wp_bag_send γe ech err _ $$ [$Hbag $Hq]
    itrivial
  wp_apply (lc := 2) (time.After.spec_pkgInit wp_After d) $$ [$Htime] as %tch %γt #Htch
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, ech, γe
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
    inext
    iintro %err Hq
    wp_auto
    wp_end
    iright
    iframe
    ipureintro; rfl
  iapply BigAndL.bigAndL_singleton.2
  simp only [chan.blockingClausePre]
  iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply is_bag_is_chan $$ Htch
  iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
  inext
  iintro %tv -
  wp_auto
  wp_end
  ileft
  ipureintro; rfl

end proof

end Perennial
