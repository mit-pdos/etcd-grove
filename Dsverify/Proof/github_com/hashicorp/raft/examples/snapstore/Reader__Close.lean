/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/examples/inproc/Reader__Close.lean (241f27e),
into snapstore (the `Reader` moved there: examples/snapstore/reader.go).
-/
/-
The proof of `snapstore.Reader.Close`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.Reader__Close

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

theorem github_com.hashicorp.raft.examples.snapstore.Reader.Close.wp_proof :
    github_com.hashicorp.raft.examples.snapstore.Reader.Close.spec (GF := GF) (hG := hG) :=
  fun rd => by
  wp_start
  wp_auto
  wp_end

end proof

end Perennial
