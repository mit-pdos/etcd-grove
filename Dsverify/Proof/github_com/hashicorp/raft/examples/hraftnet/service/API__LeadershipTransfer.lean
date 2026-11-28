/-
The proof of `service.API.LeadershipTransfer`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.API__LeadershipTransfer
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.waitFuture
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.API__done
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__LeadershipTransfer
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__LeadershipTransferToServer

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

theorem github_com.hashicorp.raft.examples.hraftnet.service.API.LeadershipTransfer.wp_proof
    (wp_LeadershipTransfer : github_com.hashicorp.raft.Raft.LeadershipTransfer.spec (GF := GF) (hG := hG))
    (wp_LeadershipTransferToServer :
      github_com.hashicorp.raft.Raft.LeadershipTransferToServer.spec (GF := GF) (hG := hG))
    (wp_done : github_com.hashicorp.raft.examples.hraftnet.service.API.done.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.service.API.LeadershipTransfer.spec (GF := GF) (hG := hG) := by
  intro a args reply γ rc i fc alb id addr rep0
  wp_start as ⟨#Hapi, #Hargs, Hok, Hrep⟩
  ihave #Hraft : (isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft) $$ []
  · iPkgInit
  ihave #Hapi' := Hapi
  iunfold isAPI at Hapi'
  icases Hapi' with ⟨%r, %fsm, %enq, %wt, #Hr, #Hfsm, #Henq, #Hwt, #Hisr, %Hresp, #Hst, #Hmu⟩
  iStructNamed Hargs
  wp_auto
  icases Hok with (%hid | ⟨#Hsrv, %haddr⟩)
  · subst hid
    wp_auto
    wp_apply (wp_LeadershipTransfer r γ rc i) $$ [$Hraft $Hisr] as %fi Hfut
    wp_apply wp_done $$ [$Hpkg $Hapi $Hfut] as %b -
    try wp_auto
    iapply HΦ
    iexists _
    iframe
  · subst haddr
    by_cases hid : addr = []
    · subst hid
      wp_auto
      wp_apply (wp_LeadershipTransfer r γ rc i) $$ [$Hraft $Hisr] as %fi Hfut
      wp_apply wp_done $$ [$Hpkg $Hapi $Hfut] as %b -
      try wp_auto
      iapply HΦ
      iexists _
      iframe
    · have hne : decide (addr = go!"") = false := decide_eq_false hid
      simp only [hne]
      wp_auto
      wp_apply (wp_LeadershipTransferToServer r γ rc i addr) $$ [$Hraft $Hisr $Hsrv] as %fi Hfut
      wp_apply wp_done $$ [$Hpkg $Hapi $Hfut] as %b -
      try wp_auto
      iapply HΦ
      iexists _
      iframe

end proof

end Perennial
