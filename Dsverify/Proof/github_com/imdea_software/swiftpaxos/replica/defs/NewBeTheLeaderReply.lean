/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/defs/NewBeTheLeaderReply.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`replica/defs.NewBeTheLeaderReply()`'s proof: a fresh reply with both fields -1.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.replica.defs.NewBeTheLeaderReply

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [replica.defs.Assumptions]

set_option goose.wp.extras true

theorem replica.defs.NewBeTheLeaderReply.wp_proof : replica.defs.NewBeTheLeaderReply.spec := by
  wp_start
  wp_auto
  iapply HΦ $$ «$r0»

end proof

end Perennial.github_com.imdea_software.swiftpaxos
