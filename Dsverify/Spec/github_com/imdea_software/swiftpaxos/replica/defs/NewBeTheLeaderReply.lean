/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/defs/NewBeTheLeaderReply.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`defs.NewBeTheLeaderReply()` (the adapter's leader changes; the master's `BeTheLeader` calls).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [replica.defs.Assumptions]

/-- A new reply with both fields -1. -/
abbrev replica.defs.NewBeTheLeaderReply.spec : Prop :=
  {{ (True : IProp netDistGF) }}
    (App (Val (@! replica.defs.NewBeTheLeaderReply)) (Val #()))
  {{ (p : Loc), RET #p; p ↦ (replica.defs.BeTheLeaderReply.mk (W32 (-1)) (W32 (-1))) }}

end spec

end Perennial.github_com.imdea_software.swiftpaxos
