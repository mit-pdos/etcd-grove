/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/defs/Link.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`replica/defs`' linked results (the adapter's and the master's callees).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.defs.NewBeTheLeaderReply

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris

open NetConn Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [replica.defs.Assumptions]

theorem replica.defs.wp_NewBeTheLeaderReply : replica.defs.NewBeTheLeaderReply.spec :=
  replica.defs.NewBeTheLeaderReply.wp_proof

end link

end Perennial.github_com.imdea_software.swiftpaxos
