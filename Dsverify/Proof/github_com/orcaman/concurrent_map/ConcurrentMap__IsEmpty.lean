/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/cmap/ConcurrentMap__IsEmpty.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Proof.github_com.orcaman.concurrent_map.Specs

@[expose] public section

noncomputable section

namespace Perennial.github_com.orcaman.concurrent_map

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

set_option goose.wp.extras true

theorem ConcurrentMap.IsEmptyV.wp_proof (wp_CountV : ConcurrentMap.CountV.spec (GF := GF)) :
    ConcurrentMap.IsEmptyV.spec (GF := GF) := fun m γ R => by
  wp_start as Hr
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply wp_CountV $$ [$Hr] as %c Hr
  iapply HΦ $$ Hr

theorem ConcurrentMap.IsEmpty.wp_proof (wp_IsEmptyV : ConcurrentMap.IsEmptyV.spec (GF := GF)) :
    ConcurrentMap.IsEmpty.spec (GF := GF) := fun m R => by
  wp_start_folded as ⟨-, Hr⟩
  iunfold reader at Hr
  icases Hr with ⟨%γ, Hr, #Hold⟩
  wp_apply wp_IsEmptyV $$ [$Hr] as %b Hr
  iapply HΦ
  iapply reader_intro; iframe Hr Hold

end proof

end Perennial.github_com.orcaman.concurrent_map
