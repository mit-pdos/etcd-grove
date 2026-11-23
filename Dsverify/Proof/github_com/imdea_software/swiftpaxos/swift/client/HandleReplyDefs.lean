/-
The definitions, specs and lemmas of `HandleReply.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandleLightSlowAckDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

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

/-- A decoded `MReply` of the client's command `x` with its witness. -/
def replyArg (H : HC) (x : sp.CmdId) (l : Loc) : IProp netDistGF :=
  iprop(∃ (rv : swift.MReply) (hs : List sp.Hash) (v : List w8), l ↦□ rv ∗
    rv.Checksum' ↦*□ hs.map shashOf ∗ rv.Rep' ↦*□ v ∗
    ⌜cmdOf rv.CmdId' = x ∧ x.cl = H.cid ∧ ∀ h ∈ hs, h.length = 32⌝ ∗
    sp.msgOk H.γ H.γc H.γm (.reply rv.Replica' rv.Ballot' x hs v))

instance replyArg_persistent H x l : Persistent (replyArg H x l) := by
  unfold replyArg; haveI := sp.msgOk_persistent (γ := H.γ) (γc := H.γc) (γm := H.γm)
  infer_instance

abbrev handleReply.specI : Prop :=
  ∀ (H : HC) (x : sp.CmdId) (l : Loc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      ctxOk H ∗ quorumsOk H ∗ hst H ∗ replyArg H x l }}
    (App (Val (H.c @!! go.GoType.PointerType swift.Client.ty @!! go!"handleReply")) (Val #l))
  {{ RET #(); hst H }}

end proof

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
