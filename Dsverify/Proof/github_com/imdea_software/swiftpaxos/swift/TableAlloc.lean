/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/TableAlloc.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The swift replica's table is `sp.tableOk`** (`swift.tableOk_alloc_of`): from the fourteen
fresh channels `initCs` made (`swift.csChans`), the table's entries (`swift.tableIs`) and each
entry's `newOk` (under persistent facts `Ctx`), the run loop allocates the channels' bags
(`swift.csBags`, the representation `swift.msgRep`) and gets `sp.tableOk`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableBase

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.tbl

theorem code_cases : ∀ c : w8, 9 ≤ c.toNat → c.toNat ≤ 22 →
    c = W8 9 ∨ c = W8 10 ∨ c = W8 11 ∨ c = W8 12 ∨ c = W8 13 ∨ c = W8 14 ∨ c = W8 15 ∨
    c = W8 16 ∨ c = W8 17 ∨ c = W8 18 ∨ c = W8 19 ∨ c = W8 20 ∨ c = W8 21 ∨ c = W8 22 := by
  decide

section alloc
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

/-- An entry of `tableIs`: its `entryOk` from its `newOk` and its bag. -/
theorem entryOk_of (γ : sp.Names) (γc γm : GName) (M : GMap w8 rpc.Pair') (c : w8)
    (ty : go.GoType) (ch : GoChan) (p : rpc.Pair') (γch : ChanNames) (Ctx : IProp netDistGF)
    (hM : swift.entryIs M c ty ch) (hp : M !! c = some p)
    (hnew : ∀ o : Loc, Ctx ⊢ sp.newOk c (swift.msgRep c) (interface.mkOk (go.GoType.PointerType ty) #o)) :
    Ctx ∗ isChanBag γch ch (sp.chanMsgP γ γc γm c (swift.msgRep c)) ⊢ sp.entryOk γ γc γm c p := by
  obtain ⟨o, ho⟩ := hM
  rw [ho] at hp
  cases hp
  iintro ⟨Hctx, #Hb⟩
  unfold sp.entryOk
  iexists swift.msgRep c, γch
  iframe Hb
  iapply hnew o $$ Hctx

theorem tableOk_alloc_of (Ctx : IProp netDistGF) [Persistent Ctx] (γ : sp.Names) (γc γm : GName)
    (v : swift.CommunicationSupply) (M : GMap w8 rpc.Pair')
    (h9 : ∀ o : Loc, Ctx ⊢ sp.newOk (W8 9) (swift.msgRep (W8 9))
      (interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #o))
    (h10 : ∀ o : Loc, Ctx ⊢ sp.newOk (W8 10) (swift.msgRep (W8 10))
      (interface.mkOk (go.GoType.PointerType swift.MFastAckClient.ty) #o))
    (h11 : ∀ o : Loc, Ctx ⊢ sp.newOk (W8 11) (swift.msgRep (W8 11))
      (interface.mkOk (go.GoType.PointerType swift.MSlowAck.ty) #o))
    (h12 : ∀ o : Loc, Ctx ⊢ sp.newOk (W8 12) (swift.msgRep (W8 12))
      (interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #o))
    (h13 : ∀ o : Loc, Ctx ⊢ sp.newOk (W8 13) (swift.msgRep (W8 13))
      (interface.mkOk (go.GoType.PointerType swift.MAcks.ty) #o))
    (h14 : ∀ o : Loc, Ctx ⊢ sp.newOk (W8 14) (swift.msgRep (W8 14))
      (interface.mkOk (go.GoType.PointerType swift.MOptAcks.ty) #o))
    (h15 : ∀ o : Loc, Ctx ⊢ sp.newOk (W8 15) (swift.msgRep (W8 15))
      (interface.mkOk (go.GoType.PointerType swift.MReply.ty) #o))
    (h16 : ∀ o : Loc, Ctx ⊢ sp.newOk (W8 16) (swift.msgRep (W8 16))
      (interface.mkOk (go.GoType.PointerType swift.MNewLeader.ty) #o))
    (h17 : ∀ o : Loc, Ctx ⊢ sp.newOk (W8 17) (swift.msgRep (W8 17))
      (interface.mkOk (go.GoType.PointerType swift.MNewLeaderAckN.ty) #o))
    (h18 : ∀ o : Loc, Ctx ⊢ sp.newOk (W8 18) (swift.msgRep (W8 18))
      (interface.mkOk (go.GoType.PointerType swift.MSync.ty) #o))
    (h19 : ∀ o : Loc, Ctx ⊢ sp.newOk (W8 19) (swift.msgRep (W8 19))
      (interface.mkOk (go.GoType.PointerType swift.MPing.ty) #o))
    (h20 : ∀ o : Loc, Ctx ⊢ sp.newOk (W8 20) (swift.msgRep (W8 20))
      (interface.mkOk (go.GoType.PointerType swift.MPingRep.ty) #o))
    (h21 : ∀ o : Loc, Ctx ⊢ sp.newOk (W8 21) (swift.msgRep (W8 21))
      (interface.mkOk (go.GoType.PointerType swift.MCollect.ty) #o))
    (h22 : ∀ o : Loc, Ctx ⊢ sp.newOk (W8 22) (swift.msgRep (W8 22))
      (interface.mkOk (go.GoType.PointerType swift.MAccept.ty) #o)) :
    Ctx ∗ swift.csChans v ∗ ⌜swift.tableIs v M⌝ ⊢
      |={⊤}=> ∃ n : swift.CsNames, sp.tableOk γ γc γm M ∗ swift.csBags γ γc γm v n := by
  iintro ⟨#Hctx, Hch, %Ht⟩
  unfold swift.csChans swift.rd.freshChan
  icases Hch with ⟨⟨%g9, #Hc9, Ho9⟩, ⟨%g10, #Hc10, Ho10⟩, ⟨%g11, #Hc11, Ho11⟩,
    ⟨%g12, #Hc12, Ho12⟩, ⟨%g13, #Hc13, Ho13⟩, ⟨%g14, #Hc14, Ho14⟩, ⟨%g15, #Hc15, Ho15⟩,
    ⟨%g16, #Hc16, Ho16⟩, ⟨%g17, #Hc17, Ho17⟩, ⟨%g18, #Hc18, Ho18⟩, ⟨%g19, #Hc19, Ho19⟩,
    ⟨%g20, #Hc20, Ho20⟩, ⟨%g21, #Hc21, Ho21⟩, ⟨%g22, #Hc22, Ho22⟩⟩
  imod start_bag (sp.chanMsgP γ γc γm (W8 9) (swift.msgRep (W8 9))) (ChanState.Buffered []) _ g9
    (by trivial) $$ Hc9 Ho9 with #Hb9
  imod start_bag (sp.chanMsgP γ γc γm (W8 10) (swift.msgRep (W8 10))) (ChanState.Buffered []) _ g10
    (by trivial) $$ Hc10 Ho10 with #Hb10
  imod start_bag (sp.chanMsgP γ γc γm (W8 11) (swift.msgRep (W8 11))) (ChanState.Buffered []) _ g11
    (by trivial) $$ Hc11 Ho11 with #Hb11
  imod start_bag (sp.chanMsgP γ γc γm (W8 12) (swift.msgRep (W8 12))) (ChanState.Buffered []) _ g12
    (by trivial) $$ Hc12 Ho12 with #Hb12
  imod start_bag (sp.chanMsgP γ γc γm (W8 13) (swift.msgRep (W8 13))) (ChanState.Buffered []) _ g13
    (by trivial) $$ Hc13 Ho13 with #Hb13
  imod start_bag (sp.chanMsgP γ γc γm (W8 14) (swift.msgRep (W8 14))) (ChanState.Buffered []) _ g14
    (by trivial) $$ Hc14 Ho14 with #Hb14
  imod start_bag (sp.chanMsgP γ γc γm (W8 15) (swift.msgRep (W8 15))) (ChanState.Buffered []) _ g15
    (by trivial) $$ Hc15 Ho15 with #Hb15
  imod start_bag (sp.chanMsgP γ γc γm (W8 16) (swift.msgRep (W8 16))) (ChanState.Buffered []) _ g16
    (by trivial) $$ Hc16 Ho16 with #Hb16
  imod start_bag (sp.chanMsgP γ γc γm (W8 17) (swift.msgRep (W8 17))) (ChanState.Buffered []) _ g17
    (by trivial) $$ Hc17 Ho17 with #Hb17
  imod start_bag (sp.chanMsgP γ γc γm (W8 18) (swift.msgRep (W8 18))) (ChanState.Buffered []) _ g18
    (by trivial) $$ Hc18 Ho18 with #Hb18
  imod start_bag (sp.chanMsgP γ γc γm (W8 19) (swift.msgRep (W8 19))) (ChanState.Buffered []) _ g19
    (by trivial) $$ Hc19 Ho19 with #Hb19
  imod start_bag (sp.chanMsgP γ γc γm (W8 20) (swift.msgRep (W8 20))) (ChanState.Buffered []) _ g20
    (by trivial) $$ Hc20 Ho20 with #Hb20
  imod start_bag (sp.chanMsgP γ γc γm (W8 21) (swift.msgRep (W8 21))) (ChanState.Buffered []) _ g21
    (by trivial) $$ Hc21 Ho21 with #Hb21
  imod start_bag (sp.chanMsgP γ γc γm (W8 22) (swift.msgRep (W8 22))) (ChanState.Buffered []) _ g22
    (by trivial) $$ Hc22 Ho22 with #Hb22
  imodintro
  iexists ⟨g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22⟩
  isplitl
  · unfold sp.tableOk
    obtain ⟨t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, tr⟩ := Ht
    isplitr
    · ipureintro
      intro m hm _ _
      have hs : ∀ (c : w8) ty ch, swift.entryIs M c ty ch → (M !! c).isSome := by
        rintro c ty ch ⟨o, ho⟩; rw [ho]; rfl
      cases m <;> simp only [sp.Msg.isPeer] at hm
      · exact absurd rfl ‹W8 6 ≠ W8 6›
      · exact absurd rfl ‹W8 7 ≠ W8 7›
      · exact hs _ _ _ t9
      · exact hs _ _ _ t12
      · exact hs _ _ _ t13
      · exact hs _ _ _ t14
      · exact hs _ _ _ t16
      · exact hs _ _ _ t17
      · exact hs _ _ _ t18
    imodintro
    iintro %c %p %Hp
    have hr := tr c (by rw [Hp]; rfl)
    rcases code_cases c hr.1 hr.2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · iapply entryOk_of _ _ _ _ _ _ _ _ _ Ctx t9 Hp h9 $$ [$Hctx $Hb9]
    · iapply entryOk_of _ _ _ _ _ _ _ _ _ Ctx t10 Hp h10 $$ [$Hctx $Hb10]
    · iapply entryOk_of _ _ _ _ _ _ _ _ _ Ctx t11 Hp h11 $$ [$Hctx $Hb11]
    · iapply entryOk_of _ _ _ _ _ _ _ _ _ Ctx t12 Hp h12 $$ [$Hctx $Hb12]
    · iapply entryOk_of _ _ _ _ _ _ _ _ _ Ctx t13 Hp h13 $$ [$Hctx $Hb13]
    · iapply entryOk_of _ _ _ _ _ _ _ _ _ Ctx t14 Hp h14 $$ [$Hctx $Hb14]
    · iapply entryOk_of _ _ _ _ _ _ _ _ _ Ctx t15 Hp h15 $$ [$Hctx $Hb15]
    · iapply entryOk_of _ _ _ _ _ _ _ _ _ Ctx t16 Hp h16 $$ [$Hctx $Hb16]
    · iapply entryOk_of _ _ _ _ _ _ _ _ _ Ctx t17 Hp h17 $$ [$Hctx $Hb17]
    · iapply entryOk_of _ _ _ _ _ _ _ _ _ Ctx t18 Hp h18 $$ [$Hctx $Hb18]
    · iapply entryOk_of _ _ _ _ _ _ _ _ _ Ctx t19 Hp h19 $$ [$Hctx $Hb19]
    · iapply entryOk_of _ _ _ _ _ _ _ _ _ Ctx t20 Hp h20 $$ [$Hctx $Hb20]
    · iapply entryOk_of _ _ _ _ _ _ _ _ _ Ctx t21 Hp h21 $$ [$Hctx $Hb21]
    · iapply entryOk_of _ _ _ _ _ _ _ _ _ Ctx t22 Hp h22 $$ [$Hctx $Hb22]
  · unfold swift.csBags
    dsimp only
    isplitr
    · iexact Hb9
    isplitr
    · iexact Hb10
    isplitr
    · iexact Hb11
    isplitr
    · iexact Hb12
    isplitr
    · iexact Hb13
    isplitr
    · iexact Hb14
    isplitr
    · iexact Hb15
    isplitr
    · iexact Hb16
    isplitr
    · iexact Hb17
    isplitr
    · iexact Hb18
    isplitr
    · iexact Hb19
    isplitr
    · iexact Hb20
    isplitr
    · iexact Hb21
    iexact Hb22

end alloc

end swift.tbl

end Perennial.github_com.imdea_software.swiftpaxos
