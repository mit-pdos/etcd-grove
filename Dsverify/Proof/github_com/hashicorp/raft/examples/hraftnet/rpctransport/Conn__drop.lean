/-
The proof of `rpctransport.Conn.drop`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn__drop
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Net.Spec.net.rpc.Client__Close

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [π : Net.NetProtoGS] [net.rpc.Assumptions] [net.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn.drop.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_Close : net.rpc.Client.Close.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn.drop.spec (GF := GF) (hG := hG) := by
  intro p W a c
  wp_start as ⟨#Hc, #Hcl⟩
  ihave #Henv := dialEnv_of_pkg $$ Hpkg
  iunfold dialEnv at Henv
  icases Henv with ⟨#Hnet, #Hsync, -⟩
  iunfold isConn at Hc
  icases Hc with ⟨#Haddr, #Hmu, -, -⟩
  wp_auto
  wp_apply wp_Lock $$ [$Hmu] as ⟨Hlk, Hinv⟩
  iunfold connInv at Hinv
  icases Hinv with ⟨%c0, Hc0, Hcc⟩
  wp_auto
  wp_if_destruct
  · wp_apply wp_Unlock $$ [$Hmu $Hlk Hc0]
    · inext; unfold connInv; iexists _; iframe Hc0; ileft; ipureintro; rfl
    wp_apply wp_Close $$ [$Hcl] as %err -
    iapply HΦ; itrivial
  · wp_apply wp_Unlock $$ [$Hmu $Hlk Hc0 Hcc]
    · inext; unfold connInv; iexists _; iframe
    wp_apply wp_Close $$ [$Hcl] as %err -
    iapply HΦ; itrivial

end proof

end Perennial
