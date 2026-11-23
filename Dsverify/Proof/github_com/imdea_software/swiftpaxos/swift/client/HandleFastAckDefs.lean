/-
The definitions, specs and lemmas of `HandleFastAck.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.InitMsgSetsDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.LeaderDefs

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

/-- What a caller hands `handleFastAck`: a leader entry, or a non-leader ack before N4. -/
def fastArg (H : HC) (x : sp.CmdId) (l : Loc) (fromLeader : Bool) : IProp netDistGF :=
  if fromLeader then leaderP H.γ H.γc H.γm H.γr H.cid true x
      (interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l)
  else iprop(∃ k, entryW H true x k (interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l))

instance fastArg_persistent H x l fromLeader : Persistent (fastArg H x l fromLeader) := by
  unfold fastArg; cases fromLeader <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- The internal spec of `c.handleFastAck(f, fromLeader)`. -/
abbrev handleFastAck.specI : Prop :=
  ∀ (H : HC) (x : sp.CmdId) (l : Loc) (fromLeader : Bool),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      ctxOk H ∗ quorumsOk H ∗ hst H ∗ fastArg H x l fromLeader }}
    (App (App (Val (H.c @!! go.GoType.PointerType swift.Client.ty @!! go!"handleFastAck"))
      (Val #l)) (Val #fromLeader))
  {{ (b : Bool), RET #b; hst H }}

end proof

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
