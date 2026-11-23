/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/state/InitState.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
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

/-- `KeyComparator` compares the treemap's keys (`cmpOk`). -/
theorem state.keyComparator_cmpOk (wp_KeyComparator : state.KeyComparator.spec (GF := GF)) :
    ⊢ github_com.emirpasic.gods.maps.treemap.cmpOk (GF := GF) (functions state.KeyComparator []) state.keyEnc := by
  iunfold github_com.emirpasic.gods.maps.treemap.cmpOk
  iintro !> %a %b %Φ HΦ
  wp_apply wp_KeyComparator as %c %Hc
  iapply HΦ $$ %c %Hc

theorem state.InitState.wp_proof (wp_KeyComparator : state.KeyComparator.spec (GF := GF))
    (wp_NewWith : github_com.emirpasic.gods.maps.treemap.NewWith.spec (GF := GF)) : state.InitState.spec (GF := GF) := by
  wp_start
  wp_auto
  ihave #Hcmp := state.keyComparator_cmpOk wp_KeyComparator
  imod sync.init_Mutex iprop(True) ⊤ «$v0_ptr» $$ «$v0» [] with #Hmu
  · inext; itrivial
  wp_apply +noauto wp_NewWith $$ [$Hcmp] as %tm Htm
  wp_auto
  iapply HΦ
  iunfold state.ownState
  iexists «$v0_ptr», tm, []
  iframe «$r0» Hmu Htm
  iunfold state.valsOk
  iintro !> %k
  have : github_com.emirpasic.gods.maps.treemap.lookupE [] k = none := rfl
  rw [this]
  ipureintro; rfl

end proof

end Perennial.github_com.imdea_software.swiftpaxos
