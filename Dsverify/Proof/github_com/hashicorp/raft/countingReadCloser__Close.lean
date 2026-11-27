/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/countingReadCloser__Close.lean (241f27e).
-/
/-
The proof of `raft.countingReadCloser__Close` (stage 3, snap).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.countingReadCloser__Close

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

theorem github_com.hashicorp.raft.countingReadCloser.Close.wp_proof :
    github_com.hashicorp.raft.countingReadCloser.Close.spec (GF := GF) (hG := hG) := by
  intro cr src R eof
  wp_start as #Hrc
  unfold readCloserOk
  icases Hrc with ⟨-, #HClose⟩
  wp_auto
  wp_apply HClose
  iapply HΦ; itrivial

end proof

end Perennial
