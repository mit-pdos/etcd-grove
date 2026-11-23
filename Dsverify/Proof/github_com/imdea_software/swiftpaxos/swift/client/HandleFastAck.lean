/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/HandleFastAck.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`handleFastAck(f, fromLeader)` (swift/client.go:200): the N4 check (a ballot's leader counts
once, by its reply), the ballot filter, the delivered check, then `f` added to the command's
fast message set.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.InitMsgSetsDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.LeaderDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandleFastAckDefs

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

theorem handleFastAck.wp_proof
    (wp_init : initMsgSets.specI (hG := hG))
    (wp_Add : replica.mset.MsgSet.Add.specI (hG := hG))
    (wp_Leader : replica.leader.Leader.specI (hG := hG)) :
    handleFastAck.specI (hG := hG) := by
  intro H x l fromLeader
  haveI := cmdId_intoValInj (sem := sem)
  wp_start as ⟨#Hctx, #Hq, Hst, #Harg⟩
  unfold hst
  icases Hst with ⟨Hcore, HF, HS, %bal, Hbal⟩
  ihave ⟨%fa, %hs, #Ho⟩ : (∃ fa hs, ackObj (interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l)
      fa hs : IProp netDistGF) $$ []
  · unfold fastArg
    cases fromLeader
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Harg with ⟨%k, #Hw⟩
      unfold entryW
      icases Hw with ⟨%fa, %hs, #Ho, -⟩
      iexists fa, hs; iexact Ho
    · simp only [↓reduceIte]
      unfold leaderP
      icases Harg with ⟨%fa, %hs, %csL, %v, #Ho, -⟩
      iexists fa, hs; iexact Ho
  ihave #Ho' := Ho
  iunfold ackObj at Ho'
  icases Ho' with ⟨%l', ⟨%Hl', %Hlen⟩, #Hl, #Hcs⟩
  have : l' = l := by
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at Hl'
    exact (go.intoVal_inj Hl').symm
  subst l'
  ihave #Hf := Hl
  iStructNamed Hf
  ihave %HN := ctxOk_N H $$ Hctx
  ihave #Hctx0 := Hctx
  iunfold ctxOk at Hctx
  icases Hctx with ⟨#Hinv, #Hcfg, #Hb, #Hbag, #HcB, #HLg, #Hqt, #Hn, #Hhook, #Hpool, -⟩
  wp_auto
  wp_join (Q := fun v => iprop(∃ r : Bool, «$res0_ptr» ↦ r ∗ f_ptr ↦ l ∗ c_ptr ↦ H.c ∗
      ((⌜v = executeVal⌝ ∗ ⌜fromLeader = false → sp.rid fa.Replica' ≠ sp.leaderOf H.N (sp.bal fa.Ballot')⌝) ∨
        ⌜v = returnVal #()⌝))) at next with [«$res0» f c]
  · cases fromLeader
    · wp_auto
      wp_apply wp_Leader as %r %Hr
      · ipureintro; exact HN
      unfold fastArg
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Harg with ⟨%k, #Hw⟩
      unfold entryW
      icases Hw with ⟨%fa', %hs', #Ho2, ⟨%Hk, -, -, -, %Hwire⟩, -⟩
      ihave %Hag := ackObj_agree _ fa fa' hs hs' $$ [Ho Ho2]
      · iframe #
      obtain ⟨rfl, rfl⟩ := Hag
      subst Hk
      wp_if_destruct
      · iexists _; iframe; iright; ipureintro; first | rfl | trivial
      · iexists _; iframe; ileft; isplitr; · ipureintro; first | rfl | trivial
        ipureintro; intro _ heq
        exact Hif ((Hr Hwire.2 fa.Replica' Hwire.1).mpr heq)
    · wp_auto
      iexists _; iframe; ileft; isplitr; · ipureintro; first | rfl | trivial
      ipureintro; intro h; cases h
  rename_i v
  iintro ⟨%r, «$res0», f, c, Hv⟩
  icases Hv with (⟨%Hv, %Hnl⟩ | %Hv)
  rotate_left
  · subst Hv
    wp_auto
    iapply HΦ
    iframe
  subst Hv
  wp_auto
  wp_join (Q := fun v => iprop(∃ (r : Bool) (bal' : w32), «$res0_ptr» ↦ r ∗ f_ptr ↦ l ∗
      c_ptr ↦ H.c ∗ structFieldRef swift.Client go!"ballot" H.c ↦ bal' ∗
      (⌜v = executeVal⌝ ∨ ⌜v = returnVal #()⌝))) at next with [«$res0» f c Hbal]
  · wp_if_destruct
    · iexists _, _; iframe; ileft; ipureintro; first | rfl | trivial
    wp_if_destruct
    · iexists _, _; iframe; ileft; ipureintro; first | rfl | trivial
    wp_if_destruct
    · iexists _, _; iframe; iright; ipureintro; first | rfl | trivial
    · iexists _, _; iframe; ileft; ipureintro; first | rfl | trivial
  rename_i v
  iintro ⟨%r', %bal', «$res0», f, c, Hbal, Hv⟩
  icases Hv with (%Hv | %Hv)
  rotate_left
  · subst Hv
    wp_auto
    iapply HΦ
    iframe
  subst Hv
  wp_auto
  unfold core
  icases Hcore with ⟨%dref, %rref, %aref, %D, %Rm, %Dn, %Gr, %As, %spn, Hdel, HD, Hreps, HRm,
    HRe, HspN, Hal, HAs, HDn, HGr, %Hok⟩
  wp_auto
  wp_apply (wp_map_lookup2 (K := swift.CommandId) (V := Unit)) $$ [$HD] as HD
  cases hDx : D.lookup fa.CmdId' with
  | some u =>
    simp only [Option.isSome_some, _root_.decide_true]
    wp_auto
    iapply HΦ
    iframe
    ipureintro; exact Hok
  | none =>
  simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
  wp_auto
  wp_apply wp_init $$ [HF HS] as ⟨HF, HS⟩
  · iframe; iframe #
  iunfold pathsOwn at HF
  icases HF with ⟨%fref, %FP, Hfld, HFP, HFs, %Hset⟩
  simp only [↓reduceIte]
  obtain ⟨ms, hms, hmsn⟩ := Hset
  wp_auto
  wp_apply (wp_map_lookup1 (K := swift.CommandId) (V := Loc)) $$ [$HFP] as HFP
  rw [show (FP !! fa.CmdId').getD (zero_val Loc) = ms by
    show (FP.lookup fa.CmdId').getD _ = ms; rw [hms]; rfl]
  ihave ⟨Hms, HFback⟩ := (BigSepM.bigSepM_lookup_acc (Φ := setOwn H true) hms).1 $$ HFs
  unfold setOwn
  icases Hms with (%Hn | Hms)
  · exact absurd Hn hmsn
  ihave %Hxf : ⌜cmdOf fa.CmdId' = x⌝ $$ []
  · unfold fastArg
    cases fromLeader
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Harg with ⟨%k, #Hw⟩
      unfold entryW
      icases Hw with ⟨%fa', %hs', #Ho2, ⟨-, %Hx', -⟩, -⟩
      ihave %Hag := ackObj_agree _ fa fa' hs hs' $$ [Ho Ho2]
      · iframe #
      obtain ⟨rfl, rfl⟩ := Hag
      ipureintro; exact Hx'
    · simp only [↓reduceIte]
      unfold leaderP
      icases Harg with ⟨%fa', %hs', %csL, %v, #Ho2, ⟨%Hx', -⟩, -⟩
      ihave %Hag := ackObj_agree _ fa fa' hs hs' $$ [Ho Ho2]
      · iframe #
      obtain ⟨rfl, rfl⟩ := Hag
      ipureintro; exact Hx'
  subst Hxf
  wp_apply wp_Add $$ [Hms HspN Hal HAs HDn HGr Hdel HD Hreps HRm HRe] as %added ⟨Hms, Hcore⟩
  · iframe Hms
    isplitl [HspN Hal HAs HDn HGr Hdel HD Hreps HRm HRe]
    · unfold core
      iexists dref, rref, aref, D, Rm, Dn, Gr, As, spn
      iframe; ipureintro; exact Hok
    unfold fastArg
    cases fromLeader
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Harg with ⟨%k, #Hw⟩
      ihave #Hw' := Hw
      iunfold entryW at Hw'
      icases Hw' with ⟨%fa', %hs', #Ho2, ⟨%Hk, -⟩, -⟩
      ihave %Hag := ackObj_agree _ fa fa' hs hs' $$ [Ho Ho2]
      · iframe #
      obtain ⟨rfl, rfl⟩ := Hag
      subst Hk
      imodintro
      iapply entryW_entryP
      iframe #
      ipureintro; exact Hnl rfl
    · simp only [↓reduceIte]
      isplitr
      · ipureintro; simp
      imodintro; iexact Harg
  iapply HΦ
  isplitl [Hcore]
  · iunfold core at Hcore; iexact Hcore
  isplitl [Hfld HFP HFback Hms]
  · unfold pathsOwn
    iexists fref, FP
    simp only [↓reduceIte]
    iframe
    isplitl
    · unfold setOwn; iapply HFback; iright; iexact Hms
    ipureintro; trivial
  isplitl [HS]
  · iapply pathsOwn_weaken $$ HS
  iexists _; iexact Hbal

end proof

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
