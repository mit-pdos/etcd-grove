/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/newCountingReadCloser.lean (241f27e).
-/
/-
The proof of `raft.newCountingReadCloser` (stage 3, snap).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.newCountingReadCloser
public import Dsverify.Spec.github_com.hashicorp.raft.newCountingReader

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

theorem github_com.hashicorp.raft.newCountingReadCloser.wp_proof
    (wp_newCountingReader : github_com.hashicorp.raft.newCountingReader.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.newCountingReadCloser.spec (GF := GF) (hG := hG) := by
  intro rc
  wp_start
  iapply wp_fupd
  wp_auto
  wp_apply wp_newCountingReader as %cr #Hcr
  ipersist «$r0»
  imodintro
  iapply HΦ
  iexists cr
  iframe #

end proof

end Perennial
