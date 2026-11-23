/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/HandleMsgs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`handleMsgs()` (swift/client.go:126): the handler's loop, a `select` over seven of the
client's channels. Three carry what the readers deliver (`Readers.lean`: `repP`, `facP`,
`lsP`); the other four (`acceptChan`, `fastAckChan`, `acksChan`, `optAcksChan`) never receive on
the client node (no reader sends to them: the stream to a client carries only `MReply`,
`MFastAckClient`, `MLightSlowAck`), so their protocol is `False`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.ReadersDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.FastAckObjDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandleMsgsDefs

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

end defs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [client.Assumptions] [time.Assumptions]
  [dlog.Assumptions] [bytes.Assumptions]

set_option goose.wp.extras true

theorem handleMsgs.wp_proof
    (wp_hr : handleReply.specI (hG := hG)) (wp_hfa : handleFastAck.specI (hG := hG))
    (wp_hls : handleLightSlowAck.specI (hG := hG)) (wp_new : newFastAck.specI (hG := hG)) :
    handleMsgs.specI (hG := hG) := by
  intro H
  wp_start as ⟨#Hctx, #Hq, Hst, Hcs⟩
  wp_auto_lc 2
  unfold csOk
  icases Hcs with ⟨%chR, %chF, %chL, %chA, %chFA, %chAk, %chO, %gR, %gF, %gL, %gA, %gFA, %gAk, %gO,
    #HfR, #HbR, #HfF, #HbF, #HfL, #HbL, #HfA, #HbA, #HfFA, #HbFA, #HfAk, #HbAk, #HfO, #HbO⟩
  ihave HL : ("Hst" ∷ hst H ∗ "Hlc1" ∷ £ 1 ∗ "Hlc2" ∷ £ 1 : IProp netDistGF) $$ [Hst Hlc1 Hlc2]
  · iframe
  wp_for HL
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `replyChan`
    iapply bag_clause $$ Hlc1 Hlc2 HbR
    inext
    iintro %v HP
    iunfold repP at HP
    icases HP with ⟨%x, %l, %Hv, #Harg⟩
    subst Hv
    wp_auto_lc 2
    wp_apply wp_hr H x l $$ [$Hpkg $Hpkg2 $Hctx $Hq $Hst $Harg] as Hst
    wp_for_post
    iframe
    isplitl [Hst]
    · iexact Hst
    isplitl [Hlc1]
    · iexact Hlc1
    iexact Hlc2
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `acceptChan`: never
    iapply bag_clause $$ Hlc1 Hlc2 HbA
    inext
    iintro %v HF
    iexfalso; iexact HF
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `fastAckChan`: never
    iapply bag_clause $$ Hlc1 Hlc2 HbFA
    inext
    iintro %v HF
    iexfalso; iexact HF
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `fastAckClientChan`
    iapply bag_clause $$ Hlc1 Hlc2 HbF
    inext
    iintro %v HP
    iunfold facP at HP
    icases HP with ⟨%l, %fac, %hs, ⟨%Hv, %Hh, %Hcl⟩, #Hl, #Hcs, #Hw⟩
    subst Hv
    ihave #Hctx' := Hctx
    iunfold ctxOk at Hctx'
    icases Hctx' with ⟨-, -, -, -, -, -, -, -, -, #Hpool, -⟩
    ihave %Hwire : ⌜sp.wireOk fac.Replica' fac.Ballot'⌝ $$ [Hw]
    · ihave Hw2 := Hw
      simp only [sp.msgOk]
      icases Hw2 with ⟨%D, %P, %c, %Hw', -⟩
      ipureintro; exact Hw'
    wp_auto_lc 2
    wp_apply wp_new $$ [$Hpkg $Hpool] as %f Hf
    ihave #Hl' := Hl
    iStructNamed Hl'
    wp_auto
    ipersist Hf
    wp_apply wp_hfa H (cmdOf fac.CmdId') f false $$ [$Hpkg $Hpkg2 $Hctx $Hq $Hst] as %b Hst
    · unfold fastArg
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists fac.Replica'
      unfold entryW
      iexists _, hs
      isplitr
      · unfold ackObj
        iexists f
        isplitr
        · ipureintro; exact ⟨rfl, Hh⟩
        iframe Hf
        iexact Hcs
      isplitr
      · ipureintro; exact ⟨rfl, rfl, Hcl, rfl, Hwire⟩
      ileft
      isplitr
      · ipureintro; rfl
      iexact Hw
    wp_for_post
    iframe
    isplitl [Hst]
    · iexact Hst
    isplitl [Hlc1]
    · iexact Hlc1
    iexact Hlc2
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `lightSlowAckChan`
    iapply bag_clause $$ Hlc1 Hlc2 HbL
    inext
    iintro %v HP
    iunfold lsP at HP
    icases HP with ⟨%x, %l, %Hv, #Harg⟩
    subst Hv
    wp_auto_lc 2
    wp_apply wp_hls H x l $$ [$Hpkg $Hpkg2 $Hctx $Hq $Hst $Harg] as Hst
    wp_for_post
    iframe
    isplitl [Hst]
    · iexact Hst
    isplitl [Hlc1]
    · iexact Hlc1
    iexact Hlc2
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `acksChan`: never
    iapply bag_clause $$ Hlc1 Hlc2 HbAk
    inext
    iintro %v HF
    iexfalso; iexact HF
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `optAcksChan`: never
    iapply bag_clause $$ Hlc1 Hlc2 HbO
    inext
    iintro %v HF
    iexfalso; iexact HF
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
