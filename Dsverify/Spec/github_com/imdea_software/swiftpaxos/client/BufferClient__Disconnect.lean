/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/client/BufferClient__Disconnect.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`b.Disconnect()` (`Client.Disconnect` through the embedding), after a failed `Connect`.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions] -- change log C4 (`failed`)
variable [client.Assumptions]

/-- Closes what a failed `Connect` opened; the client is dropped. -/
abbrev client.BufferClient.Disconnect.spec : Prop :=
  ∀ (b : Loc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.failed b }}
    (App (Val (b @!! go.GoType.PointerType client.BufferClient.ty @!! go!"Disconnect"))
      (Val #()))
  {{ RET #(); True }}

end spec

end Perennial.github_com.imdea_software.swiftpaxos
