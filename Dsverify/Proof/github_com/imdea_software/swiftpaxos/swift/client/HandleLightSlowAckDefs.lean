/-
The definitions, specs and lemmas of `HandleLightSlowAck.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandleFastAckDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.FastAckObjDefs

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

/-- A decoded `MLightSlowAck` of the client's command `x` with its witness. -/
def lsArg (H : HC) (x : sp.CmdId) (l : Loc) : IProp netDistGF :=
  iprop(∃ lsv : swift.MLightSlowAck, l ↦□ lsv ∗
    ⌜cmdOf lsv.CmdId' = x ∧ x.cl = H.cid ∧ sp.wireOk lsv.Replica' lsv.Ballot'⌝ ∗
    sp.msgOk H.γ H.γc H.γm (.lightSlowAck ⟨lsv.Replica', lsv.Ballot', x⟩))

instance lsArg_persistent H x l : Persistent (lsArg H x l) := by
  unfold lsArg; haveI := sp.msgOk_persistent (γ := H.γ) (γc := H.γc) (γm := H.γm); infer_instance

abbrev handleLightSlowAck.specI : Prop :=
  ∀ (H : HC) (x : sp.CmdId) (l : Loc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      ctxOk H ∗ quorumsOk H ∗ hst H ∗ lsArg H x l }}
    (App (Val (H.c @!! go.GoType.PointerType swift.Client.ty @!! go!"handleLightSlowAck")) (Val #l))
  {{ RET #(); hst H }}

end proof

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
