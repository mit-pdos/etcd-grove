/-
The definitions, specs and lemmas of `HandleMsgs.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.ReadersDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.FastAckObjDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.handler

open swift.rd

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [client.Assumptions] [time.Assumptions]
  [dlog.Assumptions] [bytes.Assumptions]

/-- A channel field of the client's `cs`. -/
abbrev csF (c : Loc) (f : GoString) : Loc :=
  structFieldRef swift.CommunicationSupply f (structFieldRef swift.Client go!"cs" c)

/-- The handler's channels (persistent): the readers' three, and four that never receive. -/
def csOk (H : HC) : IProp netDistGF :=
  iprop(∃ (chR chF chL chA chFA chAk chO : Loc) (gR gF gL gA gFA gAk gO : ChanNames),
    csF H.c go!"replyChan" ↦□ chR ∗ isChanBag gR chR (repP H) ∗
    csF H.c go!"fastAckClientChan" ↦□ chF ∗ isChanBag gF chF (facP H) ∗
    csF H.c go!"lightSlowAckChan" ↦□ chL ∗ isChanBag gL chL (lsP H) ∗
    csF H.c go!"acceptChan" ↦□ chA ∗ isChanBag gA chA (fun _ : GoInterface => iprop(False)) ∗
    csF H.c go!"fastAckChan" ↦□ chFA ∗ isChanBag gFA chFA (fun _ : GoInterface => iprop(False)) ∗
    csF H.c go!"acksChan" ↦□ chAk ∗ isChanBag gAk chAk (fun _ : GoInterface => iprop(False)) ∗
    csF H.c go!"optAcksChan" ↦□ chO ∗ isChanBag gO chO (fun _ : GoInterface => iprop(False)))


/-- `c.handleMsgs()`: runs for good. -/
abbrev handleMsgs.specI : Prop :=
  ∀ (H : HC),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      ctxOk H ∗ quorumsOk H ∗ hst H ∗ csOk H }}
    (App (Val (H.c @!! go.GoType.PointerType swift.Client.ty @!! go!"handleMsgs")) (Val #()))
  {{ RET #(); True }}

end defs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [client.Assumptions] [time.Assumptions]
  [dlog.Assumptions] [bytes.Assumptions]

set_option goose.wp.extras true

/-- A receive clause on a bag channel. -/
theorem bag_clause (γ : ChanNames) (ch : Loc) (P : GoInterface → IProp netDistGF)
    (handler : Expr) (Ψ : val → IProp netDistGF) :
    ⊢ £ 1 -∗ £ 1 -∗ isChanBag γ ch P -∗
      (▷ ∀ v, P v -∗ WP (App handler (Val (PairV #v #true))) {{ Ψ }}) -∗
    chan.blockingClausePre (.CommClause (.RecvCase github_com.imdea_software.swiftpaxos.rpc.Serializable.ty
      (Val #ch)) handler) Ψ := by
  iintro Hlc1 Hlc2 #Hbag HP
  simp only [chan.blockingClausePre]
  iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply is_bag_is_chan $$ Hbag
  iapply bag_recv_au γ ch P _ $$ [$Hlc1 $Hlc2] Hbag
  iexact HP

end proof

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
