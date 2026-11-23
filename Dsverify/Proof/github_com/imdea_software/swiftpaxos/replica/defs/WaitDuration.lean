/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/defs/WaitDuration.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`(*LatencyTable)(nil).WaitDurationID(id)`: zero (the deployment has no latency table).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Specs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

set_option goose.wp.extras true

theorem replica.defs.LatencyTable.WaitDurationID.wp_proof :
    replica.defs.LatencyTable.WaitDurationID.spec (hG := hG) := by
  intro id
  wp_start
  wp_auto
  iapply HΦ; itrivial

end proof

end Perennial.github_com.imdea_software.swiftpaxos
