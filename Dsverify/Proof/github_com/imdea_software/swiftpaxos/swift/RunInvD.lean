/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RunInvD.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The run loop's invariant at the descriptors' state** (round 23, sv-swb; task 3): `swift.runInv`
(moved from RunInv.lean) holds `swift.descDS` (DescDS.lean: the running epoch `epRunL` with the
descriptors' sub-pool and state) in place of `epRun ∗ descState`; `runInv_alloc` (moved from
RunAlloc.lean) allocates it with `swift.descDS_alloc` (DescFresh.lean); `runLoopOk_of`,
`runInv_ctx` moved with it (unchanged). Applied by sv-swc (round 19, D20 (2)), with the run
loop's numbering `swift.seqOwn` (change log C22).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescFresh
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.CmdStr

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- **The run loop's invariant** (RunInv.lean's header; round 23: the running epoch and the
descriptors' part are `swift.descDS` (DescDS.lean), which contains the running epoch `epRunL`). -/
def swift.runInv (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) : IProp netDistGF :=
  iprop(swift.descCtxE γ γc γm x.γl x.γw x.γv x.γe x.γo x.γx x.γxe x.γxm x.γxp x.γxu x.γrp x.γcg x.γout x.γcl x.γdc x.γdl x.str
      rp x.rr x.N x.r x.k ∗
    swift.syncCtx γ x.N x.r x.syncN rp ∗
    swift.runLoopCtx rp γ γc γm x ∗
    (∃ (ld : Bool) (v : swift.RunV) (M : Option sp.SyncMsg) (bs hd : sp.Seq) (w : swift.LView),
      swift.runSt γ x.γv rp x.N x.r ld v M bs hd w ∗ swift.propDepsOwn rp (bs ++ hd) ∗
      ⌜w.2.2.1 = true⌝) ∗
    swift.seqOwn γ rp x.k ∗
    swift.runReader rp x.γdl ∗
    swift.runFields γ rp x.rr x.N x.r ∗
    swift.descDS γ γc γm x rp)

end defs

section main
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

/-- The initial run-loop values. -/
def swift.RunV.init (propm km hm pm : Loc) : swift.RunV :=
  ⟨W32 0, W32 0, swift.stNORMAL, slice.nil, [], propm, ∅, km, ∅, hm, ∅, pm, ∅, null⟩

theorem swift.localOk_init (N r : Nat) (propm km hm pm : Loc) :
    swift.localOk N r (decide (sp.leaderOf N 0 = r)) (swift.RunV.init propm km hm pm) none
      (swift.viewOf sp.RState.init) := by
  unfold swift.localOk
  simp [swift.RunV.init, swift.viewOf, sp.RState.init, swift.LView.locAt, sp.bal, swift.stNORMAL]

/-- **The allocation** (see the file header). -/
theorem swift.runInv_alloc (hhooks : swift.HooksFact)
    (rp : Loc) (γ : sp.Names) (γc γm γl : GName) (N k : Nat)
    (me : w32) (fr : Bool) (l : List GoString) (pl : w64) (γw : GName)
    (csv : swift.CommunicationSupply) (n : swift.CsNames) :
    isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.runLoopPre rp γ γc γm γl N k me fr l pl γw csv n ⊢
      |={⊤}=> ∃ x : swift.RunX, swift.runInv rp γ γc γm x := by
  iintro ⟨#Hpkg, Hpre⟩
  have hh := hhooks
  unfold swift.HooksFact at hh
  ihave ⟨#HEH, #HSH⟩ := hh $$ Hpkg
  iunfold swift.runLoopPre at Hpre
  icases Hpre with ⟨%rr, %s, %b, %rc, %qs, %γs, %γrl, %γd, %γdc1, %γdl, %dm1, %dch, %rch,
    %γdc, %γrc, %hsl, %km, %hm, %pm, %propm, %accm, %waitm, %sam, %sq, %fq, %d,
    #Hrcvr, #Hinv, #Hcfg, %Hids, #FReplica, #HisR, #Fsender, #Hsbag, #Fbatcher, #Hbh, #FSQ, #HSQq0,
    #Fhistory, #FhistoryStart, #FoptExec, #FfastRead, #FfixedMajority, #FpoolLevel,
    #FslowAddrs, #Hsam, #FdeliverChan, #FrecheckChan, #Hmax, %Hdb, #Hpool, #Hshard, #Hcell,
    #Fcs, %Hcs, #Hbags, #Hgcs,
    Hstart, Fballot, Fcballot, Fstatus, FFQ, #HFQok, FcmdDescs, #Hdm1, Hv1, Hrd1, Hγd,
    ⟨%dm2, #Fdel, #HdelV, Hdview, Hdrd⟩, Frepchan, #Hrch, Fkeys, Hkm, Fhlog, Hhm, FcntL, Fseqnum,
    FpendingHashUpds, Hpm, FhistoryL, Hhsl, #Fqs, FexecL, FexecLog, HdescPool, FroutineCount,
    FrecStart, FnewLeaderAckNs, FnlBal, Fproposes, Hpropm, Fhandled, FlastSync, FacceptL, Faccepted,
    Haccm, Fwaiting, Hwaitm, Frechecks, #Hdch, #Hrchan, ⟨%ppsl, %pp, HPPO, Hpp, %Hpp⟩, ⟨%stp, HState, Hown⟩,
    #RExec, #RShut, ⟨%dr, #HDreply⟩, ⟨%pdm, Fpd, Hpdm⟩, #Hng⟩
  iunfold swift.descPoolOk at HdescPool
  icases HdescPool with ⟨%γsh, %pf, #Hsh, %Hpf, #HdescPool⟩
  ihave #HdpC : swift.descPoolCtx (swift.descDFA γsh) rp $$ []
  · iunfold swift.descPoolCtx; iexists pl; iframe FpoolLevel; iright; iexists pf
    iframe HdescPool; ipureintro; exact Hpf
  ihave #Hrcvr2 := Hrcvr
  iunfold swift.rcvrRes at Hrcvr2
  icases Hrcvr2 with ⟨%rr', %N', %fr', %l', %me', %dm', %qs', %rcc, %γrcc, %γdl', #FR', #FN', -, -,
    %Hn', -, -, #Hany, #Fqs', #Hqs', -, -, #HbL⟩
  ihave %Hrr : ⌜rr = rr'⌝ $$ [FReplica FR']
  · iapply typedPointsto_agree_wand _ _ _ _ _ $$ FReplica FR'
  subst Hrr
  ihave #HisR2 := HisR
  iunfold replica.isReplica at HisR2
  icases HisR2 with ⟨%lg, %cfgp, %tbl, %pc, %fr'', %nid, %ents, %γpc, %pwsl, %alsl, %latsl, %pws,
    %cwm, -, -, #HN, -⟩
  ihave %HNN : ⌜(W64 N : w64) = W64 N'⌝ $$ [FN' HN]
  · iapply typedPointsto_agree_wand _ _ _ _ _ $$ HN FN'
  have hNN : N = N' := by
    have h1 := congrArg (fun w : w64 => w.toNat) HNN
    have : N' ≤ 7 := Hn'.2.1
    have : N ≤ 7 := Hids.2.2.2.2
    rw [show (W64 (N' : Int)).toNat = N' by word, show (W64 (N : Int)).toNat = N by word] at h1
    exact h1
  subst hNN
  ihave %Hhl := ownSlice_len _ _ _ $$ Hhsl
  -- the shared invariants
  imod swift.deliv_alloc γ N (sp.rid me) rp γdl swift.cmdStr stp accm waitm $$
    [Hdview FexecL FexecLog Hown FacceptL Faccepted Haccm Fwaiting Hwaitm Frechecks]
    with ⟨%γx, %γxe, %γxm, %γxp, %γa, %γrm, %γxu, #HdI, #HexL, Hxu, #HaccL, Hxe, Hxp, Hrm⟩
  · iframe
  -- round 32: the node invariant with the store (its ledger half `Hout0`: round 34, the first
  -- epoch's `descInv`, through `descDS_alloc`)
  imod swift.nodeInvD_alloc γ γxm γxu swift.cmdStr N (sp.rid me) k $$ [Hstart Hxu]
    with ⟨%γv, %γe, %γo, %γout, %γcl, %γrp, %γcg, #HnI, Hv, He, Hhi, Hout0, Hres0⟩
  · iframe Hstart Hxu
  have hd0 : 0 ≤ sint.Z d := Hdb.1
  have hd100 : sint.nat d ≤ 100 := by have h2 := Hdb.2; simp only [sint.nat, sint.Z] at h2 ⊢; omega
  icases swift.bundles_split _ (sint.nat d) hd100 $$ Hdrd with ⟨Hdrd, Hdr1⟩
  imod swift.cntL_alloc rp dm2 γdl d hd0 $$ [FcntL Fseqnum FroutineCount Hdrd] with ⟨%γn, #HcntL, Hfz, Fsq⟩
  · iframe
  imod sync.init_Mutex (swift.historyLInv hsl) ⊤ _ $$ [FhistoryL] [Hhsl] with #HhL
  · iexact FhistoryL
  · inext; iunfold swift.historyLInv; iexists _; iframe Hhsl; ipureintro; exact List.length_replicate
  -- the epoch: a quarter to the pool, the rest the run loop's
  icases (typedPointsto_half_split _ _ _).1 $$ Fballot with ⟨Fb1, Fb2⟩
  icases (typedPointsto_half_split _ _ _).1 $$ Fstatus with ⟨Fs1, Fs2⟩
  icases (typedPointsto_half_split _ _ _).1 $$ Fs2 with ⟨Fs2, Fs3⟩
  icases (typedPointsto_half_split _ _ _).1 $$ FFQ with ⟨FQ1, FQ2⟩
  icases (typedPointsto_half_split _ _ _).1 $$ FQ2 with ⟨FQ2, FQ3⟩
  iunfold swift.fqOk at HFQok
  icases HFQok with ⟨%szF, %memF, #HqF, %HmF⟩
  icases (typedPointsto_half_split _ _ _).1 $$ HState with ⟨HS1, HS2⟩
  icases (typedPointsto_half_split _ _ _).1 $$ HS2 with ⟨HS2, HS3⟩
  icases (typedPointsto_half_split _ _ _).1 $$ Frepchan with ⟨Fr1, Fr2⟩
  icases (typedPointsto_half_split _ _ _).1 $$ Fr2 with ⟨Fr2, Fr3⟩
  icases (ghostVar_split_half γe _ _).1 $$ He with ⟨He1, He2⟩
  icases (ghostVar_split_half γxe _ _).1 $$ Hxe with ⟨Hxe1, Hxe2⟩
  icases (ghostVar_split_half γxp _ _).1 $$ Hxp with ⟨Hxp1, Hxp2⟩
  ihave Hsh : swift.epochShare ⟨γe, γxe, γxp, rp, rr, N⟩
      ⟨0, W32 0, stp, rc, swift.stNORMAL, fq, szF, memF⟩
      (1 : Qp).half.half $$ [Fb2 HS2 Fr2 He1 Hxe1 Hxp1 Fs2 FQ2]
  · unfold swift.epochShare swift.epochRd swift.epochTok swift.fqShare
    iframe
    isplitr
    · ipureintro; exact ⟨rfl, by show (0 : Int) ≤ sint.Z (W32 0); decide⟩
    iframe HqF
    ipureintro; exact HmF
  imod swift.epochPool_init _ _ _ $$ Hsh with ⟨%γp, Hpool0⟩
  -- round 27 (D24, the descriptor side's framing edit): `SQ`'s quorum for `descDSCtx`/`syncCtx`.

  ihave #HSQq : (∃ (szS : Nat) (memS : w32 → Prop), replica.mset.quorumIs sq szS memS) $$ []
  · iexists _, _; iexact HSQq0
  ihave #HSQc : (∃ (sq : GoInterface) (szS : Nat) (memS : w32 → Prop),
      swift.fld rp go!"SQ" ↦□ sq ∗ replica.mset.quorumIs sq szS memS) $$ []
  · icases HSQq with ⟨%szS, %memS, #HSQq⟩
    iexists sq, szS, memS
    iframe FSQ HSQq
  -- round 54 (D74 (3), 53-1): `SQ` has every replica
  ihave #HSQd : (∃ (sq : GoInterface) (szS : Nat) (memS : w32 → Prop),
      swift.fld rp go!"SQ" ↦□ sq ∗ replica.mset.quorumIs sq szS memS ∗ ⌜∀ k, memS k⌝) $$ []
  · iexists sq, _, (fun _ => True)
    iframe FSQ HSQq0
    ipureintro; intro _; trivial
  ihave #HSQf : (∃ (sq : GoInterface) (szS : Nat),
      swift.fld rp go!"SQ" ↦□ sq ∗ replica.mset.quorumIs sq szS (fun _ => True)) $$ []
  · iexists sq, _
    iframe FSQ HSQq0
  -- round 23: the descriptors' state (`descDS`, DescFresh.lean) from the pool and `cmdDescs`
  imod (swift.descDS_alloc γ γc γm ⟨γl, γw, γv, γe, γo, γx, γxe, γxm, γxp, γa, γrm, γd, γdl, γn,
      γdc, swift.cmdStr, rr, N, sp.rid me, k, dm2, d, γsh, γout, γcl, γxu, γrp, γcg⟩ rp ⟨0, W32 0, stp, rc, swift.stNORMAL, fq, szF,
      memF⟩ γp γrl) $$ [Hpool0 Fs3 HS1 HS3 Fr3 He2 Hxe2 Hxp2 FQ1 Hrm FcmdDescs Hv1 Hrd1 Hfz Hout0 Hres0]
    with HDS
  · simp only [swift.RunX.epN]
    iframe Hpool0 Hrch Hcell Hrm Hfz
    isplitl [Fs3 HS1 HS3 Fr3 He2 Hxe2 Hxp2 FQ1]
    · unfold swift.epochRest swift.epochTok; iframe
    isplitl [FcmdDescs Hv1 Hrd1]
    · iunfold swift.descsFresh
      iexists dm1, γdc1
      iframe FcmdDescs Hdm1 Hv1 Hrd1
    iunfold swift.descDSCtx
    iframe HcntL HdpC Hsh Hmax HSQd Fdel
    -- round 34 (Phase 2): the ledger's epoch half, empty, to the first epoch's `descInv`
    iframe Hout0 Hres0
    iexact HnI
  imodintro
  iexists ⟨γl, γw, γv, γe, γo, γx, γxe, γxm, γxp, γa, γrm, γd, γdl, γn, γdc, swift.cmdStr, rr, N,
    sp.rid me, k, dm2, d, γsh, γout, γcl, γxu, γrp, γcg⟩
  iunfold swift.runInv
  -- descCtxE
  isplitr
  · iunfold swift.descCtxE
    iexists me, fr, l, dm2, dch, true, dr, true, γa, γrm, rch, γrc
    iframe #
    ipureintro; exact ⟨rfl, Hids.2.2.1, Hids.1, Hids.2.2.2.1, Hids.2.2.2.2, Hids.2.1⟩
  -- syncCtx
  isplitr
  · iunfold swift.syncCtx
    iexists dm2
    simp only [swift.RunX.syncN]
    iframe HSQc
    iframe #
    ipureintro; simp only [List.length_replicate] at Hhl; word
  -- runLoopCtx
  isplitr
  · iunfold swift.runLoopCtx
    iexists s, b, γs, sq, hsl, fr, pl, sam, csv, n
    ihave #Hpe : (∃ pf : GoFunc, ⌜pf ≠ func.nil⌝ ∗ sync.isPool (swift.fld rp go!"descPool") pf iprop(True)
        (swift.descPoolP (swift.descDFA γsh))) $$ []
    · iexists pf; iframe HdescPool; ipureintro; exact Hpf
    iframe #
    isplitr
    · ipureintro; exact Hdb
    isplitr
    · ipureintro; exact Hcs
    ipureintro; rfl
  -- the run loop's state and the epoch
  isplitl [Fb1 Fcballot Fs1 Fhandled Fproposes Hpropm Fkeys Hkm Fhlog Hhm FpendingHashUpds Hpm
      FlastSync Hv Fpd Hpdm]
  · iexists (decide (sp.leaderOf N 0 = sp.rid me)), (swift.RunV.init propm km hm pm), none, [], [],
      (swift.viewOf sp.RState.init)
    isplitr [Fpd Hpdm]
    · iunfold swift.runSt
      simp only [swift.RunV.init]
      iframe
      isplitr
      · iapply (ownSlice_nil (V := swift.CommandId) (DFrac.own 1))
      isplitr
      · iapply ownSliceCap_nil
      isplitl [Hpropm]
      · iunfold swift.propsOwn; iframe Hpropm; iapply BigSepM.bigSepM_empty.2; itrivial
      isplitl [Hkm]
      · iunfold swift.keysOwn; iframe Hkm; isplitr
        · iapply BigSepM.bigSepM_empty.2; itrivial
        ipureintro; intro _ _; rfl
      isplitl [Hhm]
      · iexists (fun _ _ _ => False)
        unfold swift.hlogOwn swift.ldSound
        iframe Hhm
        isplitr
        · isplitr
          · iapply BigSepM.bigSepM_empty.2; itrivial
          ipureintro; intro _ _; rfl
        · imodintro; iintro %k' %s' %P' %h; exact h.elim
      isplitl [Hpm]
      · iunfold swift.pendOwnH; iframe Hpm; iapply BigSepM.bigSepM_empty.2; itrivial
      isplitr
      · iunfold swift.syncObj; ipureintro; rfl
      isplitr
      · iunfold sp.locLb; simp only [List.append_nil]; iapply BigSepL.bigSepL_nil.2; itrivial
      ipureintro
      exact ⟨swift.localOk_init N (sp.rid me) propm km hm pm, rfl, rfl⟩
    isplitl [Fpd Hpdm]
    · iapply swift.propDepsOwn_empty rp pdm; iframe
    ipureintro; rfl
  isplitl [Fsq Hhi]
  · iunfold swift.seqOwn; iexists _; iframe Fsq Hhi; ipureintro; decide
  isplitl [Hdr1]
  · iunfold swift.runReader; iexists dm2; iframe Fdel Hdr1
  isplitl [FrecStart FQ3 Fr1 FnewLeaderAckNs FnlBal HPPO Hpp]
  · iunfold swift.runFields
    iexists _, _, rc, null, (W32 0), ppsl, pp
    iframe
    isplitr
    · iunfold swift.nlSet; ileft; ipureintro; rfl
    isplitr
    · ipureintro; exact Hpp
    ipureintro; intro h; exact absurd rfl h
  iexact HDS

/-- **`swift.RunLoopOk`** from the arms' specs over `swift.runInv` (the descriptor and recovery
sides'), with `runInv_alloc`'s hypothesis `HooksFact`. -/
theorem swift.runLoopOk_of (hhooks : swift.HooksFact (hG := hG))
    (arms : ∀ (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX),
      swift.RunArms rp γ γc γm (swift.runInv rp γ γc γm x)) :
    swift.RunLoopOk (hG := hG) :=
  ⟨swift.RunX, swift.runInv, ⟨fun rp γ γc γm γl N k me fr l pl γw csv n =>
    swift.runInv_alloc hhooks rp γ γc γm γl N k me fr l pl γw csv n, arms⟩⟩

end main

section ctx
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

/-- **The handlers' context from the run loop's invariant** (P2-B; `swift.runCtxD`). -/
theorem swift.runInv_ctx (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) :
    swift.runInv rp γ γc γm x ⊢
      swift.runCtxD γ γc γm x.γl x.γw x.γv x.γe x.γo x.sn x.γdl rp x.N x.r x.k := by
  iintro H
  iunfold swift.runInv at H
  icases H with ⟨#Hd, -, Hrl, -, -, -, -, -⟩
  iunfold swift.descCtxE at Hd
  icases Hd with ⟨%me, %fr, %l, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, #HR, #HisR, %Hids,
    -, -, -, #Hinv, #Hcfg, #HnI, #Hdel, #HdV, #HdI, -, -, -, -, -, -, -, -, #Hng⟩
  iunfold swift.runLoopCtx at Hrl
  icases Hrl with ⟨%s, %b, %γs, %sq, %hsl, %fr', %pl, %sam, %csv, %n, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, #HcntL, -, -, -⟩
  iunfold swift.runCtxD
  iexists x.rr, me, fr, l, dm
  iframe HR HisR Hinv Hcfg HnI Hdel HdV
  isplitr
  · ipureintro; exact Hids
  isplitr
  · iexists x.γx, x.γxp, x.γxm, γa, x.γxe, γrm, x.str; iexact HdI
  iframe Hng
  iexists x.dm, x.γn, x.d
  iexact HcntL

/-- D22 (1): `runInv`'s string function (in `runLoopCtx`). -/
theorem swift.runLoopCtx_str (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) :
    swift.runLoopCtx rp γ γc γm x ⊢ ⌜x.str = swift.cmdStr⌝ := by
  iintro H
  iunfold swift.runLoopCtx at H
  icases H with ⟨%s, %b, %γs, %sq, %hsl, %fr', %pl, %sam, %csv, %n, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, %Hs, -⟩
  ipureintro; exact Hs

/-- D22 (1): `runInv`'s string function. -/
theorem swift.runInv_str (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) :
    swift.runInv rp γ γc γm x ⊢ ⌜x.str = swift.cmdStr⌝ := by
  iintro H
  iunfold swift.runInv at H
  icases H with ⟨-, -, Hrl, -, -, -, -, -⟩
  iapply swift.runLoopCtx_str $$ Hrl

end ctx

end Perennial.github_com.imdea_software.swiftpaxos
