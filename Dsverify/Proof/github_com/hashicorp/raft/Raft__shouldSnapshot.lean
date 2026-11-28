/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__shouldSnapshot.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).shouldSnapshot`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__shouldSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__config

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.Raft.shouldSnapshot.wp_proof
    (wp_getLastSnapshot : github_com.hashicorp.raft.raftState.getLastSnapshot.spec (GF := GF) (hG := hG))
    (wp_config : github_com.hashicorp.raft.Raft.config.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.shouldSnapshot.spec (GF := GF) (hG := hG) :=
  fun r γ rc i tid => by
  wp_start as ⟨#Hr, Htok⟩
  ihave #Hls := isRaft_logStore r γ rc i $$ Hr
  icases Hls with ⟨%lsx, #Hlsp, #Hls, -⟩
  iunfold isLogStore at Hls
  icases Hls with ⟨#HLast, -⟩
  wp_auto
  wp_apply wp_getLastSnapshot $$ [$Hr] as %si %st -
  wp_bind
  iapply HLast $$ Htok
  ihave #HlogC := isRaft_durInv r γ rc i $$ Hr
  iunfold logCell at HlogC
  iinv HlogC with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  icases Hi with ⟨%A, %L, %ps, %lo, %c, HL, Hrest⟩
  iexists A
  iframe HL
  iintro HL
  imod Hmask with -
  imod Hclose $$ [HL Hrest] with -
  · inext; iexists A, L, ps, lo, c; iframe
  imodintro
  iintro Htok
  wp_auto
  wp_apply wp_config $$ [$Hr] as %c %Hc
  iapply HΦ $$ Htok

end proof

end Perennial
