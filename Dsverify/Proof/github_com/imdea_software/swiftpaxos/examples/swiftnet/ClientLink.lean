/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ClientLink.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Stage 2: the client node's linked spec is `client_node_ok` (Proof/swiftnet/ClientNodeLink.lean,
imported here); stage 1's `ClientOk` link (`client_hyps`, `client_ok_linked`) is gone with
`ClientOk`.

Kept from stage 1 (the initialization is group C's in stage 2): the test package's initialization in the servers' form (`swiftnetInit.spec`,
Proof/swiftnet/Servers.lean), proved (`swiftnetInit_proof`, from `swiftnetInit_of` and the
packages' initializers `adapter.swiftInits`, ClientPkgInits.lean), for ServersLink's `init`
case.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNodeLink
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientPkgInits
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Servers

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

-- The codec of the linked results (decision D6, HUB-REQUEST 2, Proof/swiftnet/KitLike.lean):
-- `kitCodecC`, whose `kitCodecOk` holds (`kitCodecOkC_holds`).
attribute [local instance 2000] examples.swiftnet.kitCodecC

section init
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [examples.swiftnet.Assumptions] [net.FieldAssumptions]

/-- The test package's initialization in the servers' statement (the same statement as
`ClientOk`'s `wp_initialize'`), from the SwiftPaxos packages' initializers. -/
theorem swiftnetInit_of (I : adapter.SwiftInits) : swiftnetInit.spec :=
  adapter.initialize.wp_proof I

end init

section init2
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [examples.swiftnet.Assumptions] [net.FieldAssumptions]

/-- The test package's initialization at `pkgStates` (sorry-free): ServersLink's `init`. -/
theorem swiftnetInit_proof :
    letI := @pkgStates _ netDistGF hG sem
    swiftnetInit.spec :=
  letI := @pkgStates _ netDistGF hG sem
  swiftnetInit_of adapter.swiftInits

end init2

end Perennial.github_com.imdea_software.swiftpaxos
