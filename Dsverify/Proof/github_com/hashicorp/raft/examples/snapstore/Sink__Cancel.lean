/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/examples/snapstore/Sink__Cancel.lean (241f27e).
-/
/-
The proof of `snapstore.Sink.Cancel`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.Sink__Cancel

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.snapstore.Assumptions]

open github_com.hashicorp.raft github_com.hashicorp.raft.examples.snapstore

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.snapstore.Sink.Cancel.wp_proof :
    github_com.hashicorp.raft.examples.snapstore.Sink.Cancel.spec (GF := GF) (hG := hG) :=
  fun k o => by
  wp_start as Hst
  cases o with
  | none =>
    simp only [sinkSt]
    wp_auto
    wp_end
  | some bs =>
    simp only [sinkSt]
    icases Hst with ⟨%dsl, Hdata, Hsl, Hcap, Hclosed, Hsize⟩
    wp_auto
    wp_end

end proof

end Perennial
