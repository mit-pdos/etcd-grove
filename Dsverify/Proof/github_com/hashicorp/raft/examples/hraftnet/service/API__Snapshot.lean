/-
The proof of `service.API.Snapshot`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.API__Snapshot
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.waitFuture
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.API__done
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__Snapshot

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

theorem github_com.hashicorp.raft.examples.hraftnet.service.API.Snapshot.wp_proof
    (wp_Snapshot : github_com.hashicorp.raft.Raft.Snapshot.spec (GF := GF) (hG := hG))
    (wp_done : github_com.hashicorp.raft.examples.hraftnet.service.API.done.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.service.API.Snapshot.spec (GF := GF) (hG := hG) := by
  intro a args reply γ rc i fc alb rep0
  wp_start as ⟨#Hapi, Hrep⟩
  ihave #Hraft : (isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft) $$ []
  · iPkgInit
  ihave #Hapi' := Hapi
  iunfold isAPI at Hapi'
  icases Hapi' with ⟨%r, %fsm, %enq, %wt, #Hr, #Hfsm, #Henq, #Hwt, #Hisr, %Hresp, #Hst, #Hmu⟩
  wp_auto
  wp_apply (wp_Snapshot r γ rc i) $$ [$Hraft $Hisr] as %fi Hfut
  wp_apply wp_done $$ [$Hpkg $Hapi $Hfut] as %b -
  try wp_auto
  iapply HΦ
  iexists _
  iframe

end proof

end Perennial
