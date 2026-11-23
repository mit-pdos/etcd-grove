/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/Results.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The exported results of the project (restated; `etc/tcb-report.py` prints their axioms).
-/
module

public import Goal

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section results
variable [GoGlobalContext] [GooseGlobalGS .hasLC netDistGF]

theorem result_start : StartOk := start_ok
theorem result_orch : OrchOk pkgStates := orch_ok
theorem result_servers : ServersOk := servers_ok_full
theorem result_client_nodes : Nonempty (ClientNodeOk pkgStates) := ⟨client_node_ok_linked⟩

end results

end Perennial.github_com.imdea_software.swiftpaxos
