/-
The definitions, specs and lemmas of `DepEqualsV.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FastAckCalleesDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

/-- `dep1.Equals(dep2)` (value receiver) on any lists: some Boolean. -/
abbrev swift.Dep.Equals.specAnyV : Prop :=
  ∀ (d1 d2 : GoSlice) (dq1 dq2 : DFrac) (l1 l2 : List swift.CommandId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      d1 ↦*{dq1} l1 ∗ d2 ↦*{dq2} l2 }}
    (App (Val (d1 @!! swift.Dep.ty @!! go!"Equals")) (Val #d2))
  {{ (bb : Bool), RET #bb; d1 ↦*{dq1} l1 ∗ d2 ↦*{dq2} l2 }}

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
