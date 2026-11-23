/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SlotProofG.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The history slot's case by a goroutine: `slotSpecG.wp_proof`** (round 44, sv-swb; table §3R11
T16aG, T16b, T16c; plan R11.4 (4) 1).

From the goroutine record's owner state opened for the slot case (`descOwnF_slotG`): the row token
back to the store (`store_put` with the `exec` record; the slot `none`), the history writes, the
`Remove` with its ghost part `descInv_removeG` (T16aG), the registry share back inside `cntL`
(T16b: the loan back by `descInv_returnLoanO` with `shOwnR`'s pin, `cntLGhost_exit`; `j ≠ 0` by
`cntLGhost_ne0`; `delReader x.dm` by `descDSCtx`'s `delivered ↦□ x.dm`), `active := false` (whole:
`kfK` ½ + `descGo`'s ½ from `removeG`), the sets freed (T16c.f), and the tail `tailG` for
`drainStops`/`freeDesc` (T16c.p, T17).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SlotProofS
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

set_option goose.wp.extras true

theorem swift.Replica.handleMsg.slotSpecG.wp_proof (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (hinj : Function.Injective x.str)
    (wp_Str : swift.CommandId.String.specS x.str)
    (wp_Remove : github_com.orcaman.concurrent_map.ConcurrentMap.RemoveL.spec (GF := netDistGF))
    (wp_Free : replica.mset.MsgSet.Free.specQ (hG := hG)) :
    swift.Replica.handleMsg.slotSpecG γ0 γc γm x := by
  intro rp g j iL γi γsg γd d y dv rv s q sl fa cf cond fs v bw stp rcp
  simp only [swift.RunX.dcK, swift.OwnK.isSeq, swift.kfK, Bool.false_eq_true, ↓reduceIte]
  wp_start as ⟨#Hctx, Hm, %Hseq, Hd, Htok, Hshe, HsF, HfF, Hms, Hmf, Hcore, Hrest, Hocf, Hkf, Hrd,
    HshR⟩
  iunfold swift.shOwnR at HshR
  icases HshR with ⟨⟨%st, Hst⟩, ⟨%fq, %szF', %memF', Hfq, -⟩, Hrdr, Henv, Hpin⟩
  iunfold swift.envK at Henv
  icases Henv with ⟨Hloan, Hlr, Hnj, ⟨%dm, HX⟩, Hei⟩
  iunfold swift.epInvs at Hei
  icases Hei with ⟨#HI, #HSI, #Hown⟩
  ihave #Hown2 := Hown
  iunfold swift.ownCtx at Hown2
  icases Hown2 with ⟨#Hdsc, #HpB, ⟨%hsl, #Hhist, #HhL⟩, -, %Hpure, -⟩
  obtain ⟨hmp, hsq, hsr, hshsr, hsrA⟩ := Hpure
  ihave #Hdsc2 := Hdsc
  iunfold swift.descDSCtx at Hdsc2
  icases Hdsc2 with ⟨#HcntL, -, -, -, -, #Hdl2⟩
  iunfold swift.descX at HX
  icases HX with ⟨Hcd, #Hcm⟩
  ihave #Hctx2 := Hctx
  iunfold swift.DC.ctx at Hctx2
  iunfold swift.descCtxE at Hctx2
  icases Hctx2 with ⟨%me, %fr, %lg, %dm', %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, -, -, -, -, -, -, -,
    -, #HN, -⟩
  icases Hm with ⟨Hmp, #Hw0⟩
  ihave ⟨%Hin, #Hex⟩ := swift.mp_slot x γ0 γc γm rp g y s hmp $$ Hmp
  -- T16aG's token: back to the store with its `exec` record (`store_put`), the slot `none`
  iunfold swift.rowTokO at Htok
  iapply fupd_wp
  ihave Hst : (|={⊤}=> swift.epochLoan g.γq iL q ∗
      ghostMapElem x.γn j (DFrac.own (1 : Qp).half.half) false : IProp netDistGF) $$ [Htok Hloan]
  · icases Htok with (⟨Htk, Hsx⟩ | ⟨-, -, Hslot⟩)
    · iunfold swift.slotT at Hsx
      icases Hsx with ⟨Hslot, Htx⟩
      imod swift.store_put γ0 x.γv x.γe x.γo x.sn x.k x.γd x.γn g (x.epN rp) (x.DR γ0 g.ev.b)
          (swift.descGo x.γn g x.str) x.str iL q (g.ev.b, toCmdId y) .exec rv (j, (1 : Qp).half.half)
        $$ [Hloan Htk Hslot Htx] with ⟨Hloan, Hslot⟩
      · iframe Hloan
        isplitr
        · iExactEq HN; rfl
        isplitr
        · iExactEq HI; rfl
        isplitl [Htk]
        · iExactEq Htk; rfl
        isplitr
        · simp only [swift.retWhy]
          iexists y
          isplitr
          · ipureintro; rfl
          iExactEq Hex; rfl
        isplitl [Htx]
        · iExactEq Htx; rfl
        iExactEq Hslot; rfl
      imodintro
      iframe Hloan
      iExactEq Hslot; rfl
    · imodintro
      iframe Hloan
      iExactEq Hslot; rfl
  imod Hst with ⟨Hloan, Hslot⟩
  imodintro
  -- the frame
  icases Hkf with ⟨Hak, ⟨%q', Hshk⟩, Hv, Hjr, %sc, %γsc, %γsg', Hsc, #Hbs, #Hw⟩
  isimp only [swift.OwnK.γi, swift.OwnK.jq] at Hv Hjr Hw
  iunfold swift.ocfRes at Hocf
  icases Hocf with ⟨Hapf, Hocw, Hpv, %sb, %bs, Hsb, -, -, -⟩
  iunfold swift.descF at Hd
  icases Hd with ⟨Hph, Hcmd, #Hvs, Hdep, #HD, Hhs, #HHs, Hprop, Hseqf, Hmsgs, #Hmb, #HsL, %Hop⟩
  isimp only [Hseq] at Hseqf
  iunfold swift.descCore at Hcore
  icases Hcore with ⟨%wa, %slp, Hwa, Hslp, Hwaw⟩
  iunfold swift.descRest at Hrest
  icases Hrest with ⟨%pd, %hs0, %sqn, %df, Hpd, Hsqn, Hhs0, Hdf, Hpdok⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$HhL] as ⟨Hlk, HH⟩
  iunfold swift.historyLInv at HH
  icases HH with ⟨%cs, Hcs, %Hcsl⟩
  have hs0 : 0 ≤ sint.Z s := Hin.1
  have hslt : (sint.Z s).toNat < cs.length := by have := Hin.2; omega
  obtain ⟨e, he⟩ : ∃ e, cs[(sint.Z s).toNat]? = some e := ⟨_, List.getElem?_eq_getElem hslt⟩
  ihave %Hlen := ownSlice_len $$ Hcs
  have hb : 0 ≤ sint.Z s ∧ sint.Z s < sint.Z hsl.len := by
    refine ⟨hs0, ?_⟩
    have h2 := Hin.2
    have h1 : (sint.Z hsl.len).toNat = 10010001 := by rw [← Hcsl]; exact Hlen.1.symm
    omega
  icases ownSlice_elem_acc (sint.Z s) e hsl _ cs hs0 he $$ Hcs with ⟨He, Hcsb⟩
  ihave ⟨He, %Hnn⟩ := typedPointsto_not_null_dup _ _ _ $$ He
  iStructNamedPrefix He "E"
  repeat (first | (rw [ite_eq_left hb]) | wp_auto)
  -- the history element back; `Unlock`
  ihave Hel : typedPointsto (sliceIndexRef swift.commandStaticDesc (sint.Z s) hsl)
      (swift.commandStaticDesc.mk y dv.phase (state.Command.mk dv.c.op dv.c.key dv.vs) dv.dep slp df)
      (DFrac.own 1) $$ [EcmdId Ephase Ecmd Edep EslowPath Edefered]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ihave Hcs := Hcsb $$ Hel
  wp_apply sync.Mutex.wp_Unlock $$ [$HhL $Hlk Hcs]
  · iunfold swift.historyLInv
    iexists _
    iframe Hcs
    ipureintro; rw [List.length_set]; exact Hcsl
  wp_apply wp_Str $$ [$cmdId] as cmdId
  wp_method_call
  wp_auto_lc 2
  -- T16aG: `Remove`, ghost part `descInv_removeG`
  wp_apply (wp_Remove dm g.γdc (swift.descR x.γd) (x.str y)
      iprop(swift.epochLoan g.γq iL q ∗
        typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
        swift.dfld d go!"active" ↦ true ∗ ghostMapElem x.γn j (DFrac.own (1 : Qp).half.half) false ∗
        ∃ (sc' : Loc) (γc' : ChanNames) (m : Loc) (y' : swift.CommandId), ⌜x.str y' = x.str y⌝ ∗
          typedPointsto (swift.dfld d go!"seq") false ((DFrac.own (1 : Qp).half)) ∗
          typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
          typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half) ∗ swift.bagW m (g.mp y') ∗
          swift.stopBag γc' sc' (swift.stopMP g.γs γsg' (x.str y) d sc') ∗
          (swift.sgTok γsg' ∨ ghostMapElem g.γs (x.str y) (DFrac.own (1 : Qp).half) true) ∗
          typedPointsto (swift.dfld d go!"stopChan") sc' (DFrac.own (1 : Qp).half)))
    $$ [Hloan Hv Hjr Hseqf Hak] as ⟨Hloan, Hseqf, Ha, Hn3, %sc', %γc', %m, %y', %Hy', Hso, Hso2, Hmo, -,
      HsB, Hsig, Hsc'⟩
  · iframe Hcm
    iintro %o %t Hlc Hlk
    imod swift.descInv_removeG γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b) x.str iL q d y γi γsg' j o t
      $$ [Hlc Hloan Hlk Hv Hjr Hseqf Hak] with ⟨Hloan, Hlk, Hseqf, Ha, Hn3, Hrest⟩
    · iframe HI Hlc Hloan Hlk Hw Hv Hjr Hseqf Hak
    imodintro
    iframe Hlk Hloan Hseqf Ha Hn3 Hrest
  -- `!desc.seq`: true; T16b inside `cntL`
  wp_apply sync.Mutex.wp_Lock $$ [$HcntL] as ⟨Hlk, HC⟩
  iunfold swift.cntLInvR at HC
  icases HC with ⟨%n, %c, %T, Hsn, Hrc, HG⟩
  try wp_auto
  iapply fupd_wp
  imod swift.descInv_returnLoanO γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b) (swift.descGo x.γn g x.str)
      x.str iL q j (1 : Qp).half.half dm g.ev.b bw stp rcp st fq
    $$ [Hlc1 Hlc2 Hrd Hpin Hst Hfq Hcd Hloan Hlr] with Hn4
  · iframe HI Hlc1 Hlc2 Hloan Hlr
    isplitl [Hrd]
    · iExactEq Hrd; rfl
    isplitl [Hpin]
    · iExactEq Hpin; rfl
    isplitl [Hst]
    · iExactEq Hst; rfl
    isplitl [Hfq]
    · iExactEq Hfq; rfl
    iunfold swift.descX
    iframe Hcm
    iExactEq Hcd; rfl
  ihave Hnj : ghostMapElem x.γn j (DFrac.own (1 : Qp).half.half) false $$ [Hnj]
  · iExactEq Hnj; rfl
  ihave Hq1 := (swift.elem_quarters x.γn j false).2 $$ [Hnj Hslot]
  · iframe
  ihave Hq2 := (swift.elem_quarters x.γn j false).2 $$ [Hn3 Hn4]
  · iframe
  ihave Hnw := (ghostMapElem_halves x.γn j false).2 $$ [Hq1 Hq2]
  · iframe
  ihave ⟨HG, Hnw, %Hj0⟩ := swift.cntLGhost_ne0 x.γn x.dm x.γdl x.d c T j $$ [HG Hnw]
  · iframe
  iunfold swift.ownRdr at Hrdr
  icases Hrdr with ⟨%dm2, #Hdl, Hrv⟩
  ihave #Hdl : swift.fld rp go!"delivered" ↦□ dm2 $$ [Hdl]
  · iExactEq Hdl; rfl
  icombine Hdl Hdl2 gives %Hdeq
  subst Hdeq
  ihave Hslot : swift.descSlot x.γn x.dm x.γdl j $$ [Hnw Hrv]
  · iunfold swift.descSlot
    iframe Hnw
    isplitr
    · ipureintro; exact Hj0
    iExactEq Hrv; rfl
  imod swift.cntLGhost_exit x.γn x.dm x.γdl x.d c T j $$ [HG Hslot] with ⟨%Hc1, HG⟩
  · iframe
  imodintro
  wp_apply sync.Mutex.wp_Unlock $$ [$HcntL $Hlk Hsn Hrc HG]
  · iunfold swift.cntLInvR; iexists n, (c - W64 1), (T.erase j); iframe
  try wp_auto
  -- T16c.f: the sets
  iunfold swift.msetF at Hms
  icases Hms with ⟨%q1, %sz1, %mem1, %P1, %A1, %PL1, %hd1, Hms⟩
  iunfold swift.msetF at Hmf
  icases Hmf with ⟨%q2, %sz2, %mem2, %P2, %A2, %PL2, %hd2, Hmf⟩
  wp_apply (wp_Free sl q1 sz1 mem1 P1 A1 PL1 iprop(True) hd1) $$ [Hms] as ⟨-, Hms⟩
  · isplitl [Hms]
    · iright; iexact Hms
    itrivial
  try wp_auto
  wp_apply (wp_Free fa q2 sz2 mem2 P2 A2 PL2 iprop(True) hd2) $$ [Hmf] as ⟨-, Hmf⟩
  · isplitl [Hmf]
    · iright; iexact Hmf
    itrivial
  try wp_auto
  -- T16c.p: the tail
  icombine Hmsgs Hmo gives %Hmoe
  subst Hmoe
  ihave Hmw := (swift.pt_halvesW (swift.dfld d go!"msgs") dv.msgs).2 $$ [Hmsgs Hmo]
  · iframe
  ihave Hsqq := (swift.pt_quarters (V := Bool) (swift.dfld d go!"seq") false).2 $$ [Hseqf Hso2]
  · iframe
  ihave Hsqw := (swift.pt_halvesW (V := Bool) (swift.dfld d go!"seq") false).2 $$ [Hso Hsqq]
  · iframe
  icombine Hsc Hsc' gives %Hsce
  subst Hsce
  ihave Hscw := (swift.pt_halvesW (swift.dfld d go!"stopChan") sc).2 $$ [Hsc Hsc']
  · iframe
  ihave Hshe : ghostMapElem x.γsh d (DFrac.own (1 : Qp).half) q $$ [Hshe]
  · iExactEq Hshe; rfl
  icombine Hshe Hshk gives %Hqq
  obtain ⟨-, Hqq⟩ := Hqq
  subst Hqq
  ihave Hshw := (ghostMapElem_halves x.γsh d q).2 $$ [Hshe Hshk]
  · iframe
  iunfold swift.proposeHalf at Hpv
  icases Hpv with ⟨%p, Hp2, -⟩
  icombine Hprop Hp2 gives %Hpe
  subst Hpe
  ihave Hpw := (swift.pt_halvesW (swift.dfld d go!"propose") dv.propose).2 $$ [Hprop Hp2]
  · iframe
  icombine Hhs Hhs0 gives %Hhe
  subst Hhe
  ihave Hhsw := (swift.pt_halvesW (swift.dfld d go!"hs") dv.hs).2 $$ [Hhs Hhs0]
  · iframe
  ihave Hoa : swift.ocfAny cf $$ [Hocw]
  · iunfold swift.ocfAny
    iright
    iunfold hook.ocf.ownOcf at Hocw
    icases Hocw with ⟨%osl, %oL, Hocw⟩
    iexists cond, fs, osl, oL
    iexact Hocw
  iapply HΦ
  iunfold swift.tailG
  iexists dv.msgs, sl, fa, sc, γc', γsg'
  iframe Hmw HsF HfF Hscw HsB Hsig
  isplitl [Hms]
  · iunfold swift.msetAny
    icases Hms with (%Hn | Hms)
    · ileft; ipureintro; exact Hn
    · iright; iapply replica.mset.ownD_ownAny $$ Hms
  isplitl [Hmf]
  · iunfold swift.msetAny
    icases Hmf with (%Hn | Hmf)
    · ileft; ipureintro; exact Hn
    · iright; iapply replica.mset.ownD_ownAny $$ Hmf
  iunfold swift.descDFA
  iunfold swift.descDF
  iexists false, false
  iframe Ha Hsqw
  isplitr
  · ipureintro; intro h; cases h
  iunfold swift.descRestA
  iexists q, dv.phase, sqn, dv.c, dv.vs, dv.dep, dv.hs, pd, sb, dv.propose, cf, wa, slp, df
  iframe Hshw HsL Hph Hcmd Hvs Hdep Hhsw Hsqn Hpw Hpd Hapf Hoa Hslp Hdf Hwa Hsb
  ipureintro; exact Hop

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
