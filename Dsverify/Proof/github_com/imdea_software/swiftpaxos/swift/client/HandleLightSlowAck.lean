/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/HandleLightSlowAck.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`handleLightSlowAck(ls)` (swift/client.go:224): a light slow ack of the client's command,
not from its ballot's leader (N4), goes to the fast set (as an ack with no checksum) and to the
slow set.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandleFastAck
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.FastAckObj

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.handler

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
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

theorem handleLightSlowAck.wp_proof
    (wp_hfa : handleFastAck.specI (hG := hG))
    (wp_init : initMsgSets.specI (hG := hG))
    (wp_Add : replica.mset.MsgSet.Add.specI (hG := hG))
    (wp_Leader : replica.leader.Leader.specI (hG := hG))
    (wp_new : newFastAck.specI (hG := hG))
    (wp_copy : copyFastAck.specI (hG := hG)) :
    handleLightSlowAck.specI (hG := hG) := by
  intro H x l
  haveI := cmdId_intoValInj (sem := sem)
  wp_start as ⟨#Hctx, #Hq, Hst, #Harg⟩
  iunfold hst at Hst
  icases Hst with ⟨Hcore, HF, HS, %bal, Hbal⟩
  ihave %HN := ctxOk_N H $$ Hctx
  ihave #Hctx0 := Hctx
  iunfold ctxOk at Hctx
  icases Hctx with ⟨#Hinv, #Hcfg, #Hb, #Hbv, #HcB, #HLg, #Hqt, #Hn, #Hhook, #Hpool, -⟩
  iunfold lsArg at Harg
  icases Harg with ⟨%lsv, #Hl, ⟨%Hx, %Hcl, %Hwire⟩, #Hw⟩
  ihave #Hf := Hl
  iStructNamed Hf
  iunfold core at Hcore
  icases Hcore with ⟨%dref, %rref, %aref, %D, %Rm, %Dn, %Gr, %As, %spn, Hdel, HD, Hreps, HRm,
    HRe, HspN, Hal, HAs, HDn, HGr, %Hok⟩
  wp_auto
  wp_apply (wp_map_lookup2 (K := swift.CommandId) (V := Unit)) $$ [$HD] as HD
  cases hDx : D.lookup lsv.CmdId' with
  | some u =>
    simp only [Option.isSome_some, _root_.decide_true]
    wp_auto
    iapply HΦ
    unfold hst core
    iframe; ipureintro; exact Hok
  | none =>
  simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
  wp_auto
  wp_apply wp_Leader as %r %Hr
  · ipureintro; exact HN
  by_cases hrl : lsv.Replica' = r
  · rw [decide_eq_true hrl]; wp_auto; iapply HΦ; unfold hst core; iframe; ipureintro; exact Hok
  rw [decide_eq_false hrl]
  have Hnl : sp.rid lsv.Replica' ≠ sp.leaderOf H.N (sp.bal lsv.Ballot') :=
    fun h => hrl ((Hr Hwire.2 _ Hwire.1).mpr h)
  wp_auto
  wp_apply (wp_map_lookup2 (K := swift.CommandId) (V := Unit)) $$ [$HAs] as HAs
  wp_join iprop(∃ (spn' : w64) (As' : GMap swift.CommandId Unit),
      structFieldRef swift.Client go!"slowPaths" H.c ↦ spn' ∗ aref ↦$ As' ∗ ls_ptr ↦ l ∗
      structFieldRef swift.Client go!"alreadySlow" H.c ↦ aref ∗ c_ptr ↦ H.c)
    at (if: _ then _ else _) with [HspN HAs ls Hal c]
    as ⟨%spn', %As', HspN, HAs, ls, Hal, c⟩
  · cases hA : (As !! lsv.CmdId').isSome
    · simp only [Bool.false_eq_true, decide_false]
      wp_auto
      wp_apply (wp_mapInsert (K := swift.CommandId) (V := Unit)) $$ [$HAs] as HAs
      wp_join_done
    · simp only [_root_.decide_true]
      wp_auto
      wp_join_done
  wp_apply wp_new as %f Hfz
  · iframe #
  isimp at Hfz
  ipersist Hfz
  wp_apply wp_hfa H x f false $$ [Hdel HD Hreps HRm HRe HspN Hal HAs HDn HGr HF HS Hbal]
    as %b Hst
  · iframe #
    isplitl [Hdel HD Hreps HRm HRe HspN Hal HAs HDn HGr HF HS Hbal]
    · unfold hst core
      iframe HF HS
      isplitl [Hdel HD Hreps HRm HRe HspN Hal HAs HDn HGr]
      · iexists dref, rref, aref, D, Rm, Dn, Gr, As', spn'
        iframe; ipureintro; exact Hok
      iexists _; iframe Hbal
    unfold fastArg
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexists lsv.Replica'
    unfold entryW ackObj
    iexists _, ([] : List sp.Hash)
    isplitl
    · iexists f
      iframe #
      isplitr
      · ipureintro; simp
      simp only [List.map_nil]
      iapply ownSlice_nil
    isplitr
    · ipureintro; exact ⟨rfl, Hx, Hcl, rfl, Hwire⟩
    iright
    iframe #
    ipureintro; trivial
  ihave #Hff := Hfz
  iStructNamedSuffix Hff "f"
  iunfold hst at Hst
  icases Hst with ⟨Hcore, HF, HS, %bal2, Hbal⟩
  iunfold core at Hcore
  icases Hcore with ⟨%dref, %rref, %aref, %D, %Rm, %Dn, %Gr, %As, %spn, Hdel, HD, Hreps, HRm,
    HRe, HspN, Hal, HAs, HDn, HGr, %Hok⟩
  wp_auto
  wp_apply (wp_map_lookup2 (K := swift.CommandId) (V := Unit)) $$ [$HD] as HD
  cases hDx : D.lookup lsv.CmdId' with
  | some u =>
    simp only [Option.isSome_some, _root_.decide_true]
    wp_auto
    iapply HΦ
    unfold hst core
    iframe HF HS
    isplitl [Hdel HD Hreps HRm HRe HspN Hal HAs HDn HGr]
    · iexists dref, rref, aref, D, Rm, Dn, Gr, As, spn
      iframe; ipureintro; exact Hok
    iexists _; iframe Hbal
  | none =>
  simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
  wp_auto
  wp_apply wp_copy $$ [] as %f2 Hf2
  · iframe #
  wp_auto
  isimp at Hf2
  ipersist Hf2
  ihave #Hf2f := Hf2
  iStructNamedSuffix Hf2f "g"
  wp_apply wp_init $$ [HF HS] as ⟨HF, HS⟩
  · iframe; iframe #
  iunfold pathsOwn at HS
  icases HS with ⟨%sref, %SP, Hsld, HSP, HSs, %Hset⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  obtain ⟨ms, hms, hmsn⟩ := Hset
  wp_auto
  wp_apply (wp_map_lookup1 (K := swift.CommandId) (V := Loc)) $$ [$HSP] as HSP
  rw [show (SP !! lsv.CmdId').getD (zero_val Loc) = ms by
    show (SP.lookup lsv.CmdId').getD _ = ms; rw [hms]; rfl]
  ihave ⟨Hms, HSback⟩ := (BigSepM.bigSepM_lookup_acc (Φ := setOwn H false) hms).1 $$ HSs
  iunfold setOwn at Hms
  icases Hms with (%Hn | Hms)
  · exact absurd Hn hmsn
  subst Hx
  wp_apply wp_Add $$ [Hms HspN Hal HAs HDn HGr Hdel HD Hreps HRm HRe] as %added ⟨Hms, Hcore⟩
  · iframe Hms
    isplitl [HspN Hal HAs HDn HGr Hdel HD Hreps HRm HRe]
    · unfold core
      iexists dref, rref, aref, D, Rm, Dn, Gr, As, spn
      iframe; ipureintro; exact Hok
    simp only [Bool.false_eq_true, ↓reduceIte]
    imodintro
    unfold entryP ackObj
    iexists _, ([] : List sp.Hash)
    isplitl
    · iexists f2
      iframe #
      isplitr
      · ipureintro; simp
      simp only [List.map_nil]
      iapply ownSlice_nil
    isplitr
    · ipureintro; exact ⟨rfl, rfl, Hcl, rfl, Hnl⟩
    iright
    iframe #
    ipureintro; trivial
  iapply HΦ
  unfold hst
  isplitl [Hcore]
  · iexact Hcore
  isplitl [HF]
  · iapply pathsOwn_weaken $$ HF
  isplitl [Hsld HSP HSback Hms]
  · unfold pathsOwn
    iexists sref, SP
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
    isplitl
    · iapply HSback; unfold setOwn; iright; iexact Hms
    ipureintro; trivial
  iexists _; iexact Hbal

end proof

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
