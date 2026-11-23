/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/state/Link.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`state`'s linked results (the functions SwiftPaxos's replicas call).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.KeyComparator
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.NIL
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.InitState
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.Command__Execute

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp

section link
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
variable [sync.Assumptions] [SwiftNetPkgState GF] [SwiftHyps GF] [SwiftBufioDeps GF]

theorem state.wp_KeyComparator : state.KeyComparator.spec (GF := GF) :=
  state.KeyComparator.wp_proof
theorem state.wp_NIL : state.NIL.spec (GF := GF) := state.NIL.wp_proof
theorem state.wp_InitState : state.InitState.spec (GF := GF) :=
  state.InitState.wp_proof state.wp_KeyComparator github_com.emirpasic.gods.maps.treemap.wp_NewWith
theorem state.Command.wp_Execute : state.Command.Execute.spec (GF := GF) :=
  state.Command.Execute.wp_proof state.wp_NIL github_com.emirpasic.gods.maps.treemap.Map.wp_Put
    github_com.emirpasic.gods.maps.treemap.Map.wp_Get sync.Mutex.wp_Lock sync.Mutex.wp_Unlock

end link

end Perennial.github_com.imdea_software.swiftpaxos
