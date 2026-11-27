/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/examples/snapstore/Sink__ID.lean (241f27e).
-/
/-
The proof of `snapstore.Sink.ID`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.Sink__ID

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

theorem github_com.hashicorp.raft.examples.snapstore.Sink.ID.wp_proof :
    github_com.hashicorp.raft.examples.snapstore.Sink.ID.spec (GF := GF) (hG := hG) :=
  fun k st γ eof id ver idx term cfgIdx cfg => by
  wp_start as #Hcore
  iNamed Hcore
  wp_auto
  wp_end

end proof

end Perennial
