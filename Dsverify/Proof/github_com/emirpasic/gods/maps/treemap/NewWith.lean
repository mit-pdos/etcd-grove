/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/treemap/NewWith.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Specs

@[expose] public section

noncomputable section

namespace Perennial.github_com.emirpasic.gods.maps.treemap

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [treemap.Assumptions] [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

set_option goose.wp.extras true

theorem NewWith.wp_proof : NewWith.spec (GF := GF) := fun cmp enc => by
  wp_start as #Hcmp
  wp_auto
  iapply HΦ
  iunfold isTreeMap
  iexists cmp, slice.nil
  iframe «$r0» Hcmp
  simp only [List.map_nil]
  isplitl []
  · iapply ownSlice_nil
  isplitl []
  · iapply ownSliceCap_nil
  ipureintro; exact List.Pairwise.nil

end proof

end Perennial.github_com.emirpasic.gods.maps.treemap
