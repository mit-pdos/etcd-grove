/-
The definitions, specs and lemmas of `InitMsgSets.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandleAcksDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.SHashesDefs
@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.handler

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [client.Assumptions] [time.Assumptions]
  [dlog.Assumptions] [bytes.Assumptions]

/-- The internal spec of `c.initMsgSets(cmdId)`. -/
abbrev initMsgSets.specI : Prop :=
  ∀ (H : HC) (x : swift.CommandId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      ctxOk H ∗ quorumsOk H ∗ pathsOwn H true (fun _ => True) ∗ pathsOwn H false (fun _ => True) }}
    (App (Val (H.c @!! go.GoType.PointerType swift.Client.ty @!! go!"initMsgSets")) (Val #x))
  {{ RET #(); pathsOwn H true (hasSet x) ∗ pathsOwn H false (hasSet x) }}

end proof

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
