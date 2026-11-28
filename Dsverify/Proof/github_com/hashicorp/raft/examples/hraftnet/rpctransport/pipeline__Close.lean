/-
The proof of `rpctransport.pipeline.Close` (ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/examples/inproc, 241f27e).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline__Close
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

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

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline.Close.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline.Close.spec (GF := GF) (hG := hG) := by
  intro p γ j T
  wp_start as #Hp
  iNamed Hp
  wp_auto
  wp_apply wp_Lock $$ [$Hlock] as ⟨Hlocked, HR⟩
  unfold pipLocked
  icases HR with ⟨%b, Hcl, HcR⟩
  wp_auto
  cases b
  case true =>
    wp_auto
    wp_apply wp_Unlock $$ [$Hlock $Hlocked Hcl HcR]
    · inext; iexists true; iframe
    wp_end
  icases HcR with (%Hf | HcR)
  · cases Hf
  wp_auto
  wp_apply wp_broadcast_chan_close $$ [$HcR] as -
  · imodintro; itrivial
  wp_apply wp_Unlock $$ [$Hlock $Hlocked Hcl]
  · inext; iexists true; iframe; ileft; ipureintro; rfl
  wp_end


end proof

end Perennial
