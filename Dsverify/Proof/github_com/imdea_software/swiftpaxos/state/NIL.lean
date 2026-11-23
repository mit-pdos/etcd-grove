/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/state/NIL.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.Specs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp

section proof
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
variable [sync.Assumptions] [SwiftNetPkgState GF]

set_option goose.wp.extras true

theorem state.NIL.wp_proof : state.NIL.spec (GF := GF) := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iExactEq Hsl
  rfl

end proof

end Perennial.github_com.imdea_software.swiftpaxos
