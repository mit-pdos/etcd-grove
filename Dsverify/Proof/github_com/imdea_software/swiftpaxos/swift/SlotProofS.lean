/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SlotProofS.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The history slot's case by the inline owner: `slotSpecS.wp_proof`** (round 43, sv-swb; table
§3R11 T16aI, T16c with `freeDesc`; plan R11.4 (4) 1).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SlotSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SlotProofSDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

end lemmas

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

set_option goose.wp.extras true

theorem swift.Replica.handleMsg.slotSpecS.wp_proof (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (hinj : Function.Injective x.str)
    (wp_Str : swift.CommandId.String.specS x.str)
    (wp_Remove : github_com.orcaman.concurrent_map.ConcurrentMap.RemoveL.spec (GF := netDistGF))
    (wp_Free : replica.mset.MsgSet.Free.specQ (hG := hG))
    (wp_freeDesc : swift.Replica.freeDesc.specI (swift.descDFA x.γsh)) :
    swift.Replica.handleMsg.slotSpecS γ0 γc γm x := by
  intro rp g γi γsg γd d y dv rv s q sl fa cf cond fs v
  simp only [swift.RunX.dcK, swift.OwnK.isSeq, swift.kfK, ↓reduceIte]
  wp_start as ⟨#Hctx, Hm, #Hex, %Hseq, Hd, Htok, Hshe, HsF, HfF, Hms, Hmf, Hocf, Hcore, Hrest, Hkf,
    Henv⟩
  iunfold swift.envK at Henv
  icases Henv with ⟨⟨%iL, Hloan, Hlr⟩, ⟨%dm, HX⟩, Hei⟩
  iunfold swift.epInvs at Hei
  icases Hei with ⟨#HI, #HSI, #Hown⟩
  ihave #Hown2 := Hown
  iunfold swift.ownCtx at Hown2
  icases Hown2 with ⟨#Hdsc, #HpB, ⟨%hsl, #Hhist, #HhL⟩, -, %Hpure, -⟩
  obtain ⟨hmp, hsq, hsr, hshsr, hsrA⟩ := Hpure
  iunfold swift.descX at HX
  icases HX with ⟨Hcd, #Hcm⟩
  ihave #Hctx2 := Hctx
  iunfold swift.DC.ctx at Hctx2
  iunfold swift.descCtxE at Hctx2
  icases Hctx2 with ⟨%me, %fr, %lg, %dm', %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, -, -, -, -, -, -, -,
    -, #HN, -⟩
  -- T16aI's token: back to the store with its `exec` record (`store_put`), the slot `none`
  iunfold swift.rowTokO at Htok
  iapply fupd_wp
  ihave Hst : (|={⊤}=> swift.epochLoan g.γq iL q ∗ swift.slotK x (.seq γi) none : IProp netDistGF)
    $$ [Htok Hloan]
  · icases Htok with (⟨Htk, Hsx⟩ | ⟨-, -, Hslot⟩)
    · iunfold swift.slotT at Hsx
      icases Hsx with ⟨Hslot, Htx⟩
      imod swift.store_put γ0 x.γv x.γe x.γo x.sn x.k x.γd x.γn g (x.epN rp) (x.DR γ0 g.ev.b)
          (swift.descGo x.γn g x.str) x.str iL q (g.ev.b, toCmdId y) .exec rv (0, (1 : Qp).half.half.half)
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
  icases Hkf with ⟨Hak, ⟨%q', Hshk⟩, Hv, %sc, Hsc⟩
  isimp only [swift.OwnK.γi] at Hv
  iunfold swift.ocfRes at Hocf
  icases Hocf with ⟨Hapf, Hocw, Hpv, %sb, %bs, Hsb, -, -, -⟩
  icases Hm with ⟨Hmp, #Hw⟩
  ihave ⟨%Hin, -⟩ := swift.mp_slot x γ0 γc γm rp g y s hmp $$ Hmp
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
  wp_auto_lc 1
  -- T16aI: `Remove`, ghost part `descInv_removeI`
  wp_apply (wp_Remove dm g.γdc (swift.descR x.γd) (x.str y)
      iprop(swift.epochLoan g.γq iL q ∗
        typedPointsto (swift.dfld d go!"seq") true (DFrac.own (1 : Qp).half.half) ∗
        ghostMapElem x.γsh d (DFrac.own (1 : Qp).half) q ∗
        ghostMapElem g.γS d (DFrac.own 1) y ∗ swift.sqC d y ∗
        ∃ m : Loc, typedPointsto (swift.dfld d go!"seq") true (DFrac.own (1 : Qp).half) ∗
          typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half.half)))
    $$ [Hlc1 Hloan Hv Hseqf Hshe] as ⟨Hloan, Hseqf, Hshe, HγS, HsqC, %mo, Hso, Hmo⟩
  · iframe Hcm
    iintro %o %t Hlc Hlk
    imod swift.descInv_removeI γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b) x.str hinj x.γsh hshsr iL q d y
        γi γsg o t q
      $$ [Hlc Hlc1 Hloan Hlk Hv Hseqf Hshe] with ⟨Hloan, Hlk, Hseqf, Hshe, HγS, HsqC, %mo, Hso, Hmo⟩
    · iframe HI HSI Hlc Hlc1 Hloan Hlk Hw Hv Hseqf Hshe
    imodintro
    iframe Hlk Hloan Hseqf Hshe HγS HsqC
    iexists mo
    iframe Hso Hmo
  -- `!desc.seq`: false
  iunfold swift.sqC at HsqC
  icases HsqC with ⟨Ha2, Hsq2, %m2, Hm2⟩
  -- T16c.a: `active` whole, `desc.active = false`
  ihave Ha := (swift.pt_halvesW (V := Bool) (swift.dfld d go!"active") true).2 $$ [Hak Ha2]
  · iframe
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
  -- T16c.p: `freeDesc`
  icombine Hmsgs Hm2 gives %Hm2e
  icombine Hmsgs Hmo gives %Hmoe
  subst Hm2e Hmoe
  ihave Hmq := (swift.pt_quarters (swift.dfld d go!"msgs") dv.msgs).2 $$ [Hm2 Hmo]
  · iframe
  ihave Hmw := (swift.pt_halvesW (swift.dfld d go!"msgs") dv.msgs).2 $$ [Hmsgs Hmq]
  · iframe
  ihave Hsqq := (swift.pt_quarters (V := Bool) (swift.dfld d go!"seq") true).2 $$ [Hseqf Hsq2]
  · iframe
  ihave Hsqw := (swift.pt_halvesW (V := Bool) (swift.dfld d go!"seq") true).2 $$ [Hso Hsqq]
  · iframe
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
  ihave #HpoolF : swift.descPoolCtxF (swift.descDFA x.γsh) rp $$ []
  · ihave #Hdsc2 := Hdsc
    iunfold swift.descDSCtx at Hdsc2
    icases Hdsc2 with ⟨-, #Hpool, -⟩
    iunfold swift.descPoolCtxF
    iexists (swift.descDFA x.γsh)
    iframe Hpool
    imodintro
    iintro %d' H
    imodintro; iexact H
  wp_apply (wp_freeDesc rp d) $$ [Hmw Hsc HsF HfF Hms Hmf Ha Hsqw Hshw Hph Hcmd Hdep Hhsw Hsqn Hpw Hpd
      Hapf Hoa Hslp Hdf Hwa Hsb]
  · iframe HpoolF
    iunfold swift.descPooled
    iexists dv.msgs, sc, sl, fa
    iframe Hmw Hsc HsF HfF
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
    iexists false, true
    iframe Ha Hsqw
    isplitr
    · ipureintro; intro h; cases h
    iunfold swift.descRestA
    iexists q, dv.phase, sqn, dv.c, dv.vs, dv.dep, dv.hs, pd, sb, dv.propose, cf, wa, slp, df
    iframe Hshw HsL Hph Hcmd Hvs Hdep Hhsw Hsqn Hpw Hpd Hapf Hoa Hslp Hdf Hwa Hsb
    ipureintro; exact Hop
  try wp_auto
  iapply HΦ
  iframe HγS
  isplitl [Hslot]
  · iExactEq Hslot; rfl
  iunfold swift.envK
  isplitl [Hloan Hlr]
  · iexists iL; iframe
  isplitl [Hcd]
  · iexists dm
    iunfold swift.descX
    iframe Hcd Hcm
  iunfold swift.epInvs
  iframe HI HSI Hown

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
