/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/AcksCommon.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The proof of `r.commonCaseFastAck(msg, desc)` (spec: Proof/swift/AcksSpecs.lean).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AcksSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.LeaderM
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.PoolFnsDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AcksCommonDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section c16
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]

end c16

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

end lemmas

section hdLemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [hook.Assumptions]

end hdLemmas

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [sync.Assumptions] [hook.Assumptions]
  [github_com.orcaman.concurrent_map.Assumptions]

theorem swift.Replica.commonCaseFastAck.wp_proof (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF)
    (wp_Add : replica.mset.MsgSet.Add.specQ)
    (wp_Leader : replica.Leader.spec)
    (str : swift.CommandId → GoString)
    (wp_String0 : swift.CommandId.String.specS str)
    (wp_HasV : ∀ dm γdl, swift.cmapHasV.spec dm γdl) :
    ∀ c : swift.DC, c.str = str → swift.Replica.commonCaseFastAck.specIc RC MP c := by
  intro c hc γd d x b Do l fa cf cond fs v
  have wp_String : ∀ _c : swift.DC, swift.CommandId.String.specS c.str := fun _ => hc ▸ wp_String0
  wp_start as ⟨#Hctx, Hown, Hocf, #Hl, #HDep, %Hx, #Hwhy⟩
  ihave #Hfa := Hl
  iStructNamed Hfa
  ihave #Hctx2 := Hctx
  iunfold swift.DC.ctx at Hctx2
  iunfold swift.descCtxE at Hctx2
  icases Hctx2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, #Hrr, #Hrep, %Hids, -, -, -, #Hinv,
    #Hcfg, #Hninv, #Hdm, #Hcm, #HdI, -⟩
  ihave #HN := Hrep
  iunfold replica.isReplica at HN
  icases HN with ⟨%lg', %cfgp, %tbl, %pc, %fr', %nid, %ents, %γpc, %pwsl, %alsl, %latsl, %pws,
    %cwm, -, -, #HN, #Hid, -⟩
  iunfold swift.descOwn at Hown
  icases Hown with ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #HhS, #HhF, HdS,
    HR⟩
  iunfold swift.setR at HR
  iunfold swift.descSt at HR
  icases HR with ⟨%qe, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, HRC, Hd, Htok, Hcom, #Hra, %Hph,
    #Hpw, #Hdw, %Hrp, #HsB, ⟨HsF, HfF, HdF, HDo⟩⟩
  iunfold swift.epochRd at Hrd
  icases Hrd with ⟨Hbal, HStf, Hrcf, Het, Hxe, %Hbw⟩
  iunfold swift.shOwn at Hsh
  icases Hsh with ⟨Hshe, HshR⟩
  iunfold swift.shOwnR at HshR
  icases HshR with ⟨⟨%st, Hst⟩, HfqS⟩
  wp_auto
  by_cases hst : st = W64 0
  rotate_left
  · rw [decide_eq_false hst]
    wp_auto
    iapply HΦ; ileft; iframe Hocf; repackOwn
  rw [decide_eq_true hst]
  wp_auto
  by_cases hbb : bw = fa.Ballot'
  rotate_left
  · rw [decide_eq_false hbb]
    wp_auto
    iapply HΦ; ileft; iframe Hocf; repackOwn
  rw [decide_eq_true hbb]
  wp_auto
  iunfold swift.ackWhy at Hwhy
  icases Hwhy with (%hne | #Hwhy)
  · exfalso; exact hne (by rw [← hbb]; exact Hbw.1)
  shPack
  ihave HR : swift.setR c RC MP γd d x b iprop(Do ∗ swift.ocfRes d cf cond fs v) s f qF szF memF hd
      true $$ [Hsh HRC Hd Htok Hcom HsF HfF HdF HDo Hocf Hbal HStf Hrcf Het Hxe]
  · iunfold swift.setR
    iunfold swift.descSt
    iexists qe, bw, stp, rcp, dv, rv
    iframe Hsh HRC Hd Htok Hcom Hra HsF HfF HdF HDo Hocf Hpw Hdw HsB
    isplitl [Hbal HStf Hrcf Het Hxe]
    · iunfold swift.epochRd; iframe Hbal HStf Hrcf Het Hxe; ipureintro; exact Hbw
    isplitr
    · ipureintro; exact Hph
    ipureintro; exact Hrp
  have hN : 1 ≤ c.N ∧ c.N ≤ 7 := ⟨Hids.2.2.2.1, Hids.2.2.2.2.1⟩
  have hbw : sp.bal bw = b ∧ 0 ≤ sint.Z bw := Hbw
  clear Hbw Hph Hrp
  wp_if_destruct
  · -- a slow ack: the slow set first
    ihave ⟨%qe', %bw', Hbal, HsF, HfF, %Hbw', HRb⟩ := swift.setR_open $$ HR
    wp_apply (swift.Replica.wp_leader wp_Leader c.rp c.rr bw' _ c.N hN) $$ [$Hbal $Hrr $HN] as Hbal
    ihave HR := HRb $$ Hbal HsF HfF
    ihave #HhSq := swift.descOwn_hdS c RC MP γd d x b Do iprop(Do ∗ swift.ocfRes d cf cond fs v) s f qS
      qF szS szF memS memF hd (swift.ocfDc_ok d cf cond fs v Do) $$ [HhS HhF]
    · iframe HhS HhF
    wp_apply (wp_Add s qS szS memS (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True)
        (swift.setR c RC MP γd d x b iprop(Do ∗ swift.ocfRes d cf cond fs v) s f qF szF memF hd true)
        (swift.descGone c b x d) hd
        fa.Replica' (decide (fa.Replica' = BitVec.srem bw' (W32 (sint.Z (W64 (c.N : Int))))))
        (interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l)) $$ [HdS HR]
      as %added ⟨-, Hres⟩
    · iframe HdS HR HhSq
      isplitr
      · imodintro; iintro HR; isplitl []; · itrivial
        iintro -; iexact HR
      ackCond
    wp_apply (wp_String c) $$ [$msgCmdId] as msgCmdId
    wp_method_call
    wp_auto
    icases Hres with (⟨HdS, HR⟩ | Hgone)
    · ihave ⟨HrdR, HRr⟩ := swift.setR_rdr c RC MP γd d x b _ s f qF szF memF hd true $$ HR
      ihave Hb : iprop(|={⊤}=> github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ∗
          (github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ={⊤}=∗
            swift.ownRdr c.rp c.γdl)) $$ [HrdR]
      · iapply swift.ownRdr_take; iframe Hdm HrdR
      iapply fupd_wp
      imod Hb with ⟨Hrdr, Hback⟩
      imodintro
      wp_apply (wp_HasV dm c.γdl _ ((⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ (↑swift.delivN : CoPset))
          (fun _ => iprop(True))) $$ [$Hrdr] as %dl ⟨Hrdr, -⟩
      · imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.delivN)
          swift.delivN_sub) $$ HdI with ⟨Hi, Hclose⟩
        iunfold swift.delivInv at Hi
        icases Hi with ⟨%M, %bX', %X', %Mx, %rm, >HV, >HXi, >HXeD, >HMx, >HXx, >%HM⟩
        imodintro
        iexists M
        iframe HV
        iintro HV
        imod Hclose $$ [HV HXi HXeD HMx HXx] with -
        · inext; iunfold swift.delivInv; iexists M, bX', X', Mx, rm; iframe; ipureintro; exact HM
        imodintro
        itrivial
      iapply fupd_wp
      imod Hback $$ Hrdr with HrdR
      ihave HR := HRr $$ HrdR
      imodintro
      cases dl
      · wp_auto
        fastAdd
      · wp_auto
        iapply HΦ; ileft
        ihave ⟨HR, Hocf⟩ := swift.setR_take $$ HR
        iframe Hocf
        iunfold swift.descOwn
        iexists s, f, qS, qF, szS, szF, memS, memF, hd
        iframe HhS HhF HdS HR
    · -- `x` was executed in this epoch (its sequential descriptor retired by the handler):
      -- `delivered.Has(x)` is true, the epoch being still `b` by the caller's pin (SWB-5)
      iunfold swift.descGone at Hgone
      icases Hgone with ⟨%Hsq, #Hex, Hret, %qg, %bwg, %stpg, %rcpg, Hrdg, Hshg⟩
      ihave ⟨HrdR, Hpin, Hshr⟩ := swift.shOwnR_rdrP c d b qg $$ Hshg
      ihave Hb : iprop(|={⊤}=> github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ∗
          (github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ={⊤}=∗
            swift.ownRdr c.rp c.γdl)) $$ [HrdR]
      · iapply swift.ownRdr_take; iframe Hdm HrdR
      iapply fupd_wp
      imod Hb with ⟨Hrdr, Hback⟩
      imodintro
      wp_apply (wp_HasV dm c.γdl _ ((⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ (↑swift.delivN : CoPset))
          (fun ok => iprop(⌜ok = true⌝ ∗ swift.epochPinQ c.γxp qg b))) $$ [$Hrdr Hpin] as %dl ⟨Hrdr, %Hdl, Hpin⟩
      · imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.delivN)
          swift.delivN_sub) $$ HdI with ⟨Hi, Hclose⟩
        iunfold swift.delivInv at Hi
        icases Hi with ⟨%M, %bX', %X', %Mx, %rm, >HV, >HXi, >HXeD, >HMx, >HXx, >%HM⟩
        ihave ⟨Hpin, HXeD, %Hag⟩ := swift.epochPinQ_agree c.γxp qg b bX' rm $$ [Hpin HXeD]
        · iframe Hpin HXeD
        obtain ⟨rfl, rfl⟩ := Hag
        ihave %Hin := swift.exIn_delivered c.str c.γxm bX' x M X' Mx HM $$ [Hex HMx]
        · iframe Hex HMx
        imodintro
        iexists M
        iframe HV
        iintro HV
        imod Hclose $$ [HV HXi HXeD HMx HXx] with -
        · inext; iunfold swift.delivInv; iexists M, bX', X', Mx, false; iframe; ipureintro; exact HM
        imodintro
        isplitr
        · ipureintro; rw [Hx]; exact Hin
        iexact Hpin
      iapply fupd_wp
      imod Hback $$ Hrdr with HrdR
      ihave Hshg := Hshr $$ HrdR Hpin
      imodintro
      subst Hdl
      wp_auto
      iapply HΦ; iright; iunfold swift.descDone; iunfold swift.descGone; iframe Hex Hret
      isplitr
      · ipureintro; exact Hsq
      iexists qg, bwg, stpg, rcpg; iframe Hrdg Hshg
  -- an ack with dependencies: the fast set only
  fastAdd

theorem swift.Replica.handleLightSlowAck.wp_proof (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF)
    (wp_new : swift.newFastAck.specP)
    (str : swift.CommandId → GoString)
    (wp_common0 : ∀ c : swift.DC, c.str = str → swift.Replica.commonCaseFastAck.specIc RC MP c) :
    ∀ c : swift.DC, c.str = str → swift.Replica.handleLightSlowAck.specIc RC MP c := by
  intro c hc γd d x b Do l sa cf cond fs v
  have wp_common : ∀ _c : swift.DC, swift.Replica.commonCaseFastAck.specIc RC MP c :=
    fun _ => wp_common0 c hc
  wp_start as ⟨#Hctx, ⟨%u, #Hufp⟩, Hown, Hocf, #Hl, %Hx, #Hwhy⟩
  ihave #Hsa := Hl
  iStructNamed Hsa
  wp_auto
  wp_apply (wp_new u) $$ [$Hufp] as %la ⟨%fa0, Hla⟩
  ipersist Hla
  wp_apply (wp_common c γd d x b Do la _ cf cond fs v) $$ [Hown Hocf] as Hres
  · iframe Hctx Hown Hocf Hla
    isplitr
    · iexists []; iapply (ownSlice_nil (V := swift.CommandId) DFrac.discard)
    isplitr
    · ipureintro; simpa using Hx
    iexact Hwhy
  iapply HΦ $$ Hres

end proof

section proofOcf
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [sync.Assumptions] [hook.Assumptions]
  [github_com.orcaman.concurrent_map.Assumptions]

theorem swift.Replica.handleFastAck.wp_proof (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF)
    (wp_Leader : replica.Leader.spec)
    (AC : swift.DC → IProp netDistGF)
    (str : swift.CommandId → GoString)
    (wp_lead0 : ∀ c : swift.DC, c.str = str → swift.Replica.fastAckFromLeader.specIc RC MP AC c)
    (wp_common0 : ∀ c : swift.DC, c.str = str → swift.Replica.commonCaseFastAck.specIc RC MP c) :
    ∀ c : swift.DC, c.str = str → swift.Replica.handleFastAck.specIc RC MP AC c := by
  intro c hc γd d x b Do l fa
  have wp_lead : ∀ _c : swift.DC, swift.Replica.fastAckFromLeader.specIc RC MP AC c :=
    fun _ => wp_lead0 c hc
  have wp_common : ∀ _c : swift.DC, swift.Replica.commonCaseFastAck.specIc RC MP c :=
    fun _ => wp_common0 c hc
  wp_start as ⟨#Hctx, #Hack, Hown, #Hl, #HDep, ⟨%Hx, %Hpos⟩, Hw⟩
  ihave #Hfa := Hl
  iStructNamed Hfa
  ihave #Hctx2 := Hctx
  iunfold swift.DC.ctx at Hctx2
  iunfold swift.descCtxE at Hctx2
  icases Hctx2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, #Hrr, #Hrep, %Hids, -⟩
  ihave #HN := Hrep
  iunfold replica.isReplica at HN
  icases HN with ⟨%lg', %cfgp, %tbl, %pc, %fr', %nid, %ents, %γpc, %pwsl, %alsl, %latsl, %pws,
    %cwm, -, -, #HN, #Hid, -⟩
  have hN : 1 ≤ c.N ∧ c.N ≤ 7 := ⟨Hids.2.2.2.1, Hids.2.2.2.2.1⟩
  iunfold swift.descOwnF at Hown
  icases Hown with ⟨Hown, Hocf⟩
  ihave ⟨%qe, %bw, Hbal, %Hbw, Hback⟩ := swift.descOwn_ballot $$ Hown
  wp_auto
  wp_apply (swift.Replica.wp_leader wp_Leader c.rp c.rr bw _ c.N hN) $$ [Hbal] as Hbal
  · iframe Hbal Hrr HN
  ihave Hown := Hback $$ Hbal
  have hrl := swift.rid_leader bw c.N b hN Hbw.1 Hbw.2
  wp_if_destruct
  · icases Hw with (%hne | #HW)
    · exfalso; exact hne (by rw [Hif]; exact hrl)
    wp_apply (wp_lead c γd d x b Do l fa) $$ [Hown Hocf] as Hres
    · iframe Hctx Hack Hl HDep HW
      isplitl [Hown Hocf]
      · iunfold swift.descOwnF; iframe Hown Hocf
      ipureintro; exact ⟨Hx, by rw [Hif]; exact hrl⟩
    iapply HΦ $$ Hres
  · iunfold swift.descOcf at Hocf
    icases Hocf with ⟨%cf, %cond, %fs, %v, Hocf, #Hcond, #Hvf, #Hfs⟩
    wp_apply (wp_common c γd d x b iprop(swift.descCore c d x b ∗ Do) l fa cf cond fs v)
      $$ [Hown Hocf] as Hres
    · iframe Hctx Hown Hocf Hl HDep
      isplitr
      · ipureintro; exact Hx
      iunfold swift.ackWhy; iright; ipureintro; intro h; apply Hif
      rw [← hrl] at h
      have hv := replica.quorum.leader_val bw c.N (by omega) Hbw.2
      have hN' : sint.Z (W64 (c.N : Int)) = c.N := by word
      have hl0 : 0 ≤ sint.Z (BitVec.srem bw (W32 (sint.Z (W64 (c.N : Int))))) := by
        rw [hN']; have : (BitVec.srem bw (W32 (c.N : Int))).toInt = bw.toInt % (c.N : Int) := hv
        show 0 ≤ (BitVec.srem bw (W32 (c.N : Int))).toInt
        rw [this]; exact Int.emod_nonneg _ (by omega)
      unfold sp.rid at h
      apply BitVec.eq_of_toInt_eq
      have := congrArg (fun n : Nat => (n : Int)) h
      simp only [Int.toNat_of_nonneg Hpos, Int.toNat_of_nonneg hl0] at this
      exact this
    iapply HΦ
    icases Hres with (⟨Hown, Hocf⟩ | Hdone)
    · ileft; iunfold swift.descOwnF; iframe Hown
      iunfold swift.descOcf
      iexists cf, cond, fs, v
      iframe Hocf Hcond Hvf Hfs
    · iright; iexact Hdone

end proofOcf

end Perennial.github_com.imdea_software.swiftpaxos
