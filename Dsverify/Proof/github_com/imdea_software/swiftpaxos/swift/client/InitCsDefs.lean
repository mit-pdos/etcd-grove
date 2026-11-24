/-
The definitions, specs and lemmas of `InitCs.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.rpc.TableC
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandlerState

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.rd

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

/-- A fresh buffered channel of messages. -/
def freshChan (ch : Loc) : IProp netDistGF :=
  iprop(∃ γ : ChanNames, isChan ch γ GoInterface ∗ ownChan γ GoInterface (ChanState.Buffered []))

/-- `initCs(cs, t)`. -/
abbrev initCs.specI : Prop :=
  ∀ (cs t : Loc) (v : swift.CommunicationSupply),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      cs ↦ v ∗ rpc.tblOwn t (W8 9) ∅ }}
    (App (App (Val (@! swift.initCs)) (Val #cs)) (Val #t))
  {{ RET #(); ∃ (v' : swift.CommunicationSupply) (M : GMap w8 rpc.Pair'') (idn : w8),
      cs ↦ v' ∗ rpc.tblOwn t idn M ∗
      freshChan v'.replyChan' ∗ freshChan v'.fastAckClientChan' ∗ freshChan v'.lightSlowAckChan' ∗
      freshChan v'.acceptChan' ∗ freshChan v'.fastAckChan' ∗ freshChan v'.acksChan' ∗
      freshChan v'.optAcksChan' ∗
      ⌜(∃ o1 : Loc, M !! W8 10 = some ⟨interface.mkOk (go.GoType.PointerType swift.MFastAckClient.ty) #o1,
          v'.fastAckClientChan'⟩) ∧
        (∃ o2 : Loc, M !! W8 12 = some ⟨interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #o2,
          v'.lightSlowAckChan'⟩) ∧
        (∃ o3 : Loc, M !! W8 15 = some ⟨interface.mkOk (go.GoType.PointerType swift.MReply.ty) #o3,
          v'.replyChan'⟩)⌝ }}

end spec

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [rpc.Assumptions] [replica.defs.Assumptions] [time.Assumptions]

set_option goose.wp.extras true

set_option hygiene false in
/-- `make(chan fastrpc.Serializable, defs.CHAN_BUFFER_SIZE)`, its fresh channel named `H`. -/
macro "mk_ch" H:ident : tactic => `(tactic| (
  wp_apply chan.wp_make2 (V := GoInterface) (W64 2000000) as %ch %γ ⟨#Hch, %Hcap, Hown⟩
  · ipureintro; decide
  ihave Hnew : freshChan ch $$ [Hown]
  · unfold freshChan; iexists γ; iframe Hch; iExactEq Hown; rfl
  irename Hnew => $H
  try wp_auto
  try isimp only at Hcs))

set_option hygiene false in
/-- `t.Register(new(M), ch)`. -/
macro "reg_one" : tactic => `(tactic| (
  wp_alloc_auto
  try wp_auto
  wp_apply rpc.wp_Register $$ [Ht] as Ht
  · iexact Ht
  try wp_auto
  try isimp only at Hcs))

end proof

end swift.rd

end Perennial.github_com.imdea_software.swiftpaxos
