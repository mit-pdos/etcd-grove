/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RunAlloc.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The run loop's invariant, allocated** (`swift.RunLoopH.init` for `swift.runInv`): from what
`New` and the connection phase leave (`swift.runLoopPre`), the ghost state and invariants the
run loop and the descriptors share, in phases:

* `swift.nodeInvD_alloc`: the node invariant (`nodeInvD`, from `replicaStart`: the replica's
  half of its protocol state at `RState.init`), the run loop's half of the view `γv`, the epoch
  token's half `γe` at `(0, 0)`;
* `swift.deliv_alloc`: the execution record and `delivered`'s invariant (`delivInv`, empty
  record of epoch 0, not in removal mode), `execL`'s and `acceptL`'s mutexes, with the halves of
  `γxe`, `γxp` and the mirror `γrm` (`rmTok none`) the run loop keeps;
* `swift.cntL_alloc`: `cntL`'s mutex over `swift.cntLInvR` (P2-B: `d` reader bundles of
  `delivered`, no goroutine);
* `swift.bundles_split`: `d + 1` of `delivered`'s `cmapReaders` bundles (needs `d ≤ 100`: HUB
  SWC-H2);
* (round 23/D20: `swift.runInv_alloc`, `swift.runLoopOk_of`, `swift.runInv_ctx` moved to
  RunInvD.lean with `runInv`). Hypotheses defined here: `swift.HooksFact` (the hooks are nil:
  swift's package state, at the link). (Round 33: `swift.ReaderBorrowGap`, the FRAMEWORK
  `readerBorrowV` hypothesis of SW4, is gone: descCtx/syncCtx no longer carry `readerBorrowV`,
  descriptor side's round 30.)
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunInv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section facts
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]

/-- The hooks are nil (swift's package state `swift.pkgSt`; proved at the link). -/
def swift.HooksFact : Prop :=
  isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ⊢
    globalAddr swift.ExecHook ↦□ func.nil ∗ globalAddr swift.SyncHook ↦□ func.nil

end facts

section alloc
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

theorem swift.rowsOk_init : swift.rowsOk sp.RState.init ∅ := by
  intro b y
  show swift.rowsOf sp.RState.init b y = swift.rowEmpty
  rfl

/-- The node invariant (see the file header). -/
theorem swift.nodeInvD_alloc (γ : sp.Names) (γxm γxu : GName) (str : swift.CommandId → GoString)
    (N r k : Nat) :
    sp.replicaStart γ k ∗ swift.xuAuth γxu ∅ ⊢ |={⊤}=> ∃ γv γe γo γout γcl γrp γcg : GName,
      inv swift.nodeN (swift.nodeInvD γ γv γe γo ⟨γxm, γout, γcl, str, N, r, γxu, γrp, γcg⟩ k) ∗
      ghostVar γv (1 : Qp).half (swift.viewOf sp.RState.init) ∗
      ghostVar γe (1 : Qp).half (swift.epochOf sp.RState.init) ∗ sp.numHi γ k (W64 0) ∗
      ghostMapAuth γout (1 : Qp).half (∅ : GMap (Nat × sp.CmdId) (Nat × Qp)) ∗
      -- round 56 (D79 (1), 52-3): the first epoch's (ballot 0) reserved key in the epochs' map
      ghostMapElem γcg ((0 : Nat), false) (DFrac.own 1) (none : Option GName) := by
  iintro ⟨Hs, Hxu⟩
  ihave ⟨Hn, Hhi⟩ := sp.replicaStart_num k $$ Hs
  imod (ghostVar_alloc (GF := netDistGF) (swift.viewOf sp.RState.init)) with ⟨%γv, Hv⟩
  icases (ghostVar_split_half γv 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
  imod (ghostVar_alloc (GF := netDistGF) (swift.epochOf sp.RState.init)) with ⟨%γe, He⟩
  icases (ghostVar_split_half γe 1 _).1 $$ He with ⟨He1, He2⟩
  imod (ghost_map_alloc_empty (GF := netDistGF) (K := Nat × sp.CmdId) (V := swift.RowV))
    with ⟨%γo, Ho⟩
  -- round 32 (the store, notes/lifecycle-plan.md "Revision 5"): the ledger `γout` (half for the
  -- first epoch's `descInv`, Phase 2) and the claims `γcl`, both empty
  imod (ghost_map_alloc_empty (GF := netDistGF) (K := Nat × sp.CmdId) (V := Nat × Qp))
    with ⟨%γout, Hout⟩
  icases (ghostMapAuth_halves γout _).1 $$ Hout with ⟨Hout1, Hout2⟩
  imod (ghost_map_alloc_empty (GF := netDistGF) (K := Nat × sp.CmdId) (V := swift.ClK))
    with ⟨%γcl, Hcl⟩
  -- round N5 (D72 (1)): the report tokens' map, nothing minted
  imod (ghost_map_alloc_empty (GF := netDistGF) (K := Nat) (V := Unit)) with ⟨%γrp, Hrp⟩
  -- round 56 (D79 (1), 52-3): the epochs' map, ballot 0 reserved
  imod (ghost_map_alloc_empty (GF := netDistGF) (K := Nat × Bool) (V := Option GName))
    with ⟨%γcg, Hcg⟩
  imod ghost_map_insert (γ := γcg) ((0 : Nat), false) (none : Option GName)
    (GMap.lookup_empty _) $$ Hcg with ⟨Hcg, Hres⟩
  imod inv_alloc swift.nodeN ⊤ (swift.nodeInvD γ γv γe γo ⟨γxm, γout, γcl, str, N, r, γxu, γrp, γcg⟩ k)
    $$ [Hn Hv1 He1 Ho Hout1 Hcl Hxu Hrp Hcg] with #Hinv
  · inext
    iunfold swift.nodeInvD
    iexists sp.RState.init, ∅
    iframe Hn Hv1 He1 Ho
    isplitl [Hout1 Hcl Hxu]
    · iunfold swift.storeD
      iexists ∅, ∅, ∅, ∅
      iframe Hout1 Hcl Hxu
      isplitl []
      · iapply BigSepM.bigSepM_empty.2; iempintro
      isplitl []
      · ipureintro
        refine ⟨fun K h => ?_, fun K _ h => ?_, fun K h => ?_, fun K h => ?_, fun K c h => ?_⟩ <;>
          simp_all
      · ipureintro; intro K h; simp at h
    isplitl [Hrp Hcg]
    · iunfold swift.nodeX
      isplitl [Hrp]
      · iexists ∅; iframe Hrp; ipureintro; intro b h; simp at h
      isplitl []
      · rw [show sp.RState.init.repR = [] from rfl]; iapply BigSepL.bigSepL_nil.2; iempintro
      isplitl []
      · ileft; ipureintro; rfl
      · iunfold swift.cgAuth
        iexists _; iframe Hcg
        ipureintro
        constructor
        · intro k h
          rw [GMap.lookup_insert_eq_iff] at h
          by_cases e : (((0 : Nat), false) : Nat × Bool) = k
          · subst e; exact Nat.zero_le _
          · rw [if_neg e] at h; simp at h
        · intro b h
          rw [GMap.lookup_insert_eq_iff] at h
          rw [if_neg (by simp)] at h; simp at h
    ipureintro
    refine ⟨fun b x h => ?_, swift.rowsOk_init⟩
    simp [sp.RState.init] at h
  imodintro
  iexists γv, γe, γo, γout, γcl, γrp, γcg
  iframe
  iexact Hinv

/-- The execution record, `delivered`'s invariant, `execL`, `acceptL` (see the file header). -/
theorem swift.deliv_alloc (γ : sp.Names) (N r : Nat) (rp : Loc) (γdl : GName)
    (str : swift.CommandId → GoString) (stp accm waitm : Loc) :
    github_com.orcaman.concurrent_map.cmapView γdl ∅ ∗
      swift.fld rp go!"execL" ↦ Perennial.zero_val sync.Mutex ∗
      swift.fld rp go!"execLog" ↦ (slice.nil : GoSlice) ∗
      state.ownState stp (fun _ => none) ∗
      swift.fld rp go!"acceptL" ↦ Perennial.zero_val sync.Mutex ∗
      swift.fld rp go!"accepted" ↦ accm ∗ accm ↦$ (∅ : GMap swift.CommandId Unit) ∗
      swift.fld rp go!"waiting" ↦ waitm ∗ waitm ↦$ (∅ : GMap swift.CommandId GoSlice) ∗
      swift.fld rp go!"rechecks" ↦ (slice.nil : GoSlice) ⊢
    |={⊤}=> ∃ γx γxe γxm γxp γa γrm γxu : GName,
      inv swift.delivN (swift.delivInv γ N r γdl γx γxp γxm γa γxe γrm str) ∗
      sync.isMutex (swift.fld rp go!"execL") (swift.execLInvE γ γx γxe γxm γxu N r rp) ∗
      -- round 46 (D-SWC2-5): the tickets' authority, for the store (`nodeInvD_alloc`)
      swift.xuAuth γxu ∅ ∗
      sync.isMutex (swift.fld rp go!"acceptL") (swift.acceptInv γ r rp γa) ∗
      ghostVar γxe (1 : Qp).half ((0 : Nat), stp) ∗ ghostVar γxp (1 : Qp).half (0 : Nat) ∗
      swift.rmTok γrm none := by
  iintro ⟨Hview, FexecL, FexecLog, Hown, FacceptL, Facc, Haccm, Fwait, Hwaitm, Frk⟩
  imod (ghostVar_alloc (GF := netDistGF) ((0 : Nat), ([] : List swift.ExE))) with ⟨%γx, Hx⟩
  icases (ghostVar_split_half γx 1 _).1 $$ Hx with ⟨Hx1, Hx2⟩
  imod (ghostVar_alloc (GF := netDistGF) ((0 : Nat), stp)) with ⟨%γxe, Hxe⟩
  icases (ghostVar_split_half γxe 1 _).1 $$ Hxe with ⟨Hxe1, Hxe2⟩
  imod (ghost_map_alloc_empty (GF := netDistGF) (K := Nat × Nat) (V := swift.ExE)) with ⟨%γxm, Hxm⟩
  imod (ghostVar_alloc (GF := netDistGF) (0 : Nat)) with ⟨%γxp, Hxp⟩
  icases (ghostVar_split_half γxp 1 _).1 $$ Hxp with ⟨Hxp1, Hxp2⟩
  imod (ghostVar_alloc (GF := netDistGF) (0 : Nat)) with ⟨%γa, Ha⟩
  icases (ghostVar_split_half γa 1 _).1 $$ Ha with ⟨Ha1, Ha2⟩
  imod (ghostVar_alloc (GF := netDistGF) (none : swift.RmV)) with ⟨%γrm, Hrm⟩
  icases (ghostVar_split_half γrm 1 _).1 $$ Hrm with ⟨Hrm1, Hrm2⟩
  imod inv_alloc swift.delivN ⊤ (swift.delivInv γ N r γdl γx γxp γxm γa γxe γrm str)
    $$ [Hview Hx1 Hxp1 Hxm Ha1 Hrm1] with #HdI
  · inext
    ihave ⟨Hx1, Hxm, HFz⟩ := swift.delivFz_put γx γxp γxm 0 ([] : List swift.ExE)
      (∅ : GMap (Nat × Nat) swift.ExE) $$ [Hx1 Hxm]
    · iframe Hx1 Hxm; iapply swift.exLb_nil
    iunfold swift.delivInv
    iexists ∅, 0, [], ∅, false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hview Hx1 Hxp1 Hxm
    isplitl [Ha1 Hrm1 HFz]
    · iframe HFz
      iunfold swift.delivX
      iexists 0
      iframe Ha1
      isplitr
      · iapply BigSepL.bigSepL_nil.2; itrivial
      isplitr
      · ipureintro; intro _; rfl
      · iunfold swift.delivRm; simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hrm1
    · ipureintro
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro k v h; simp at h
      · intro _ e he; simp at he
      · intro i; simp
      · intro b' i _; rfl
  imod (swift.xuAuth_alloc ⊤) with ⟨%γxu, Hxu⟩
  imod sync.init_Mutex (swift.execLInvE γ γx γxe γxm γxu N r rp) ⊤ _ $$ [FexecL]
    [FexecLog Hx2 Hxe1 Hown] with #HexL
  · iexact FexecL
  · inext
    iapply swift.execLInvE_empty γ γx γxe γxm γxu N r rp slice.nil 0 stp
    iframe FexecLog Hx2 Hxe1
    isplitr
    · iapply (ownSlice_nil (V := swift.commandStaticDesc) (DFrac.own 1))
    isplitr
    · iapply ownSliceCap_nil
    iExactEq Hown; rfl
  imod sync.init_Mutex (swift.acceptInv γ r rp γa) ⊤ _ $$ [FacceptL]
    [Facc Haccm Fwait Hwaitm Ha2 Frk] with #HaccL
  · iexact FacceptL
  · inext
    iunfold swift.acceptInv
    iexists accm, waitm, ∅, ∅, 0
    iframe Facc Haccm Fwait Hwaitm Ha2
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · imodintro
      iintro %dd %h
      simp at h
    -- N2-loop: `rechecks` starts nil
    iunfold swift.recheckOwn
    iexists slice.nil, []
    iframe Frk
    isplitr
    · iapply (ownSlice_nil (V := swift.CommandId) (DFrac.own 1))
    · iapply ownSliceCap_nil
  imodintro
  iexists γx, γxe, γxm, γxp, γa, γrm, γxu
  iframe HdI HexL HaccL Hxe2 Hxp2 Hxu
  iunfold swift.rmTok
  iexact Hrm2

/-- `d + 1` of `delivered`'s bundles (`d ≤ 100`). -/
theorem swift.bundles_split (P : IProp netDistGF) (d : Nat) (hd : d ≤ 100) :
    ([∗list] _x ∈ List.replicate github_com.orcaman.concurrent_map.cmapReaders (), P) ⊢
      ([∗list] _x ∈ List.replicate d (), P) ∗ P := by
  have hc : d + 1 ≤ github_com.orcaman.concurrent_map.cmapReaders := by
    unfold github_com.orcaman.concurrent_map.cmapReaders
    rw [sync.rwmutex.actualMaxReaders_unseal]
    omega
  have he : github_com.orcaman.concurrent_map.cmapReaders =
      d + (1 + (github_com.orcaman.concurrent_map.cmapReaders - (d + 1))) := by omega
  rw [he, ← List.replicate_append_replicate, ← List.replicate_append_replicate,
    List.replicate_one]
  iintro H
  icases BigSepL.bigSepL_append.1 $$ H with ⟨H1, H2⟩
  icases BigSepL.bigSepL_append.1 $$ H2 with ⟨H2, -⟩
  iframe H1
  ihave H2' := BigSepL.bigSepL_singleton.1 $$ H2
  iexact H2'

/-- `cntL`'s mutex (see the file header). -/
theorem swift.cntL_alloc (rp : Loc) (dm : GoSlice) (γdl : GName) (d : w64) (hd : 0 ≤ sint.Z d) :
    swift.fld rp go!"cntL" ↦ Perennial.zero_val sync.Mutex ∗ swift.fld rp go!"seqnum" ↦ (W64 0) ∗
      swift.fld rp go!"routineCount" ↦ (W64 0) ∗
      ([∗list] _x ∈ List.replicate (sint.nat d) (), swift.delReader dm γdl) ⊢
    |={⊤}=> ∃ γn : GName, sync.isMutex (swift.fld rp go!"cntL") (swift.cntLInvR rp dm γdl γn d) ∗
      swift.cntFrozen γn false ∗
      typedPointsto (swift.fld rp go!"seqnum") (W64 0) (DFrac.own (1 : Qp).half) := by
  iintro ⟨FcntL, Fseq, Frc, Hr⟩
  icases (typedPointsto_half_split _ _ _).1 $$ Fseq with ⟨Fseq, Fseq2⟩
  imod swift.cntLGhost_init dm γdl d hd $$ Hr with ⟨%γn, Hg, Hfz⟩
  imod sync.init_Mutex (swift.cntLInvR rp dm γdl γn d) ⊤ _ $$ [FcntL] [Fseq Frc Hg] with #H
  · iexact FcntL
  · inext
    iunfold swift.cntLInvR
    iexists (W64 0), (W64 0), []
    iframe
  imodintro
  iexists γn
  iframe H Hfz Fseq2

end alloc

section fresh
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

/-- **A new epoch from `handleSync`'s fresh resources** (`EpS_start`, at the run loop's names
`x`): the reply goroutine's cell filled (the ballot's quarter and `historySize`, GAP H-size),
the pool allocated (`epochPool_init` on a quarter), the rest kept; the fresh `cmdDescs` back. -/
theorem swift.epRun_fresh (γ : sp.Names) (γc γm : GName) (rp : Loc) (x : swift.RunX) (b' : Nat)
    (hb : 0 < b') :
    swift.epFresh γ γc γm x.syncN x.γe x.γd rp x.rr b' ⊢
      |={⊤}=> swift.epRun γ γc γm rp x ∗ swift.descsFresh x.γd rp ∗ swift.cntFrozen x.γn false := by
  simp only [swift.RunX.syncN]
  iintro Hf
  iunfold swift.epFresh at Hf
  icases Hf with ⟨%bw, %stp', %rc, %γl, Hb, Hst, HS, Hrc, #HrcH, Hfill, He, Hxp, Hxe, Hrm, Hds,
    -, Hhs, %Hbw, Hfz, -, %fq, %szF, %memF, FQ1, FQ2, #HqF, %HmF⟩
  have hbw : 0 ≤ sint.Z bw := by
    unfold sp.bal at Hbw; show (0 : Int) ≤ bw.toInt; omega
  icases (typedPointsto_half_split _ _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
  icases (typedPointsto_half_split _ _ _).1 $$ Hst with ⟨Hs1, Hs2⟩
  icases (typedPointsto_half_split _ _ _).1 $$ HS with ⟨HS1, HS2⟩
  icases (typedPointsto_half_split _ _ _).1 $$ HS2 with ⟨HS2, HS3⟩
  icases (typedPointsto_half_split _ _ _).1 $$ Hrc with ⟨Hr1, Hr2⟩
  iunfold swift.epochTok at He
  icases (ghostVar_split_half _ _ _).1 $$ He with ⟨He1, He2⟩
  icases (ghostVar_split_half _ _ _).1 $$ Hxe with ⟨Hxe1, Hxe2⟩
  icases (ghostVar_split_half _ _ _).1 $$ Hxp with ⟨Hxp1, Hxp2⟩
  ihave #HrcH2 := HrcH
  iunfold swift.replyChanH at HrcH2
  icases HrcH2 with ⟨%rep, %ok, %ex, %ar, %γok, %γex, %γa, -, -, -, -, #Hcell⟩
  imod swift.cell_fill swift.replyCellN ⊤ (by simp) γl (swift.replyCellRes rp bw)
    $$ [$Hcell $Hfill Hb2 Hhs] with #Hfilled
  · unfold swift.replyCellRes swift.replyRes; iframe Hb2; iexists _; iframe Hhs
    ipureintro; decide
  ihave Hsh : swift.epochShare ⟨x.γe, x.γxe, x.γxp, rp, x.rr, x.N⟩
      ⟨b', bw, stp', rc, swift.stNORMAL, fq, szF, memF⟩
      (1 : Qp).half.half $$ [Hb1 HS2 Hr1 He1 Hxe1 Hxp1 Hs1 FQ2]
  · unfold swift.epochShare swift.epochRd swift.epochTok swift.fqShare
    iframe
    isplitr
    · ipureintro; exact ⟨Hbw, hbw⟩
    iframe HqF
    ipureintro; exact HmF
  imod swift.epochPool_init _ _ _ $$ Hsh with ⟨%γp, Hpool0⟩
  imodintro
  iframe Hds Hfz
  iunfold swift.epRun
  simp only [swift.RunX.epN]
  iexists ⟨b', bw, stp', rc, swift.stNORMAL, fq, szF, memF⟩, γp, γl
  iframe HrcH Hfilled
  isplitl [Hpool0]
  · iunfold swift.epochRun; iexists _, _; iexact Hpool0
  isplitl [Hs2 HS1 HS3 Hr2 He2 Hxe2 Hxp2 FQ1]
  · unfold swift.epochRest swift.epochTok; iframe
  iframe Hrm
  ipureintro; rfl

end fresh

section stop
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

/-- **The epoch once the reply goroutine stopped** (`EpH` of `replyChan.stop`/`stopDescs`): the
pool, the rest, the reply cell's content back (the ballot's quarter and `historySize`), the
mirror's half. -/
def swift.epHalted (rp : Loc) (x : swift.RunX) : IProp netDistGF :=
  iprop(∃ (ev : swift.EpV) (γp : GName),
    swift.epochRun (x.epN rp) ev (1 : Qp).half.half γp ∗ swift.epochRest (x.epN rp) ev ∗
    swift.replyCellRes rp ev.bw ∗ swift.rmTok x.γrm none ∗ ⌜ev.st = swift.stNORMAL⌝)

/-- **`r.repchan.stop()` on the running epoch** (`replyChan.stop.specI`'s instance, with the
receiver tied to the epoch's `repchan`): the reply goroutine's share comes back (if it never
claimed the cell, the run loop claims it: the cell was filled). -/
theorem swift.epRun_stop (wp_stop : swift.replyChan.stop.specR (hG := hG)) (γ : sp.Names)
    (γc γm : GName) (rp : Loc) (x : swift.RunX) (rc : Loc) :
    {{ swift.epRun γ γc γm rp x ∗
        typedPointsto (swift.fld rp go!"repchan") rc (DFrac.own (1 : Qp).half) }}
      (App (Val (rc @!! go.GoType.PointerType swift.replyChan.ty @!! go!"stop")) (Val #()))
    {{ RET #(); swift.epHalted rp x ∗
        typedPointsto (swift.fld rp go!"repchan") rc (DFrac.own (1 : Qp).half) }} := by
  unfold swift.epRun swift.epochRest swift.RunX.epN
  iintro %Φ ⟨Hep, Hrc⟩ HΦ
  icases Hep with ⟨%ev, %γp, %γl, Hpool, Hrest, #HrcH, #Hfilled, Hrm, %Hst⟩
  icases Hrest with ⟨Hs, HS1, HS2, Hr, He, Hxe, Hxp, HFQ1⟩
  ihave %Hrceq : ⌜rc = ev.rcp⌝ $$ [Hrc Hr]
  · iapply typedPointsto_agree_wand _ _ _ _ _ $$ Hrc Hr
  subst Hrceq
  ihave #HrcH2 := HrcH
  iunfold swift.replyChanH at HrcH2
  icases HrcH2 with ⟨%rep, %ok, %ex, %ar, %γok, %γex, %γa, -, -, -, -, #Hcell⟩
  iapply wp_fupd
  iapply (wp_stop γ γc γm rp γl ev.bw ev.rcp) $$ [HrcH]
  · iexact HrcH
  inext
  iintro Hback
  ihave Hres : |={⊤}=> swift.replyCellRes rp ev.bw $$ [Hback]
  · iunfold swift.replyBack at Hback
    icases Hback with (Hb | Hk)
    · imodintro; iexact Hb
    · imod swift.cell_claim swift.replyCellN ⊤ (by simp) γl (swift.replyCellRes rp ev.bw)
        $$ [$Hcell $Hk $Hfilled] with >Hb
      imodintro; iexact Hb
  imod Hres
  imodintro
  iapply HΦ
  iframe Hrc
  iunfold swift.epHalted
  iexists ev, γp
  simp only [swift.RunX.epN]
  iframe Hpool Hres Hrm
  isplitl [Hs HS1 HS2 Hr He Hxe Hxp HFQ1]
  · unfold swift.epochRest; iframe
  ipureintro; exact Hst

/-! ### Round 19 (sv-swb, §24 decision (1a)): the epoch's pool name and values exposed

`epRunAt … ev γp` / `epHaltedAt … ev γp` are `epRun`/`epHalted` at given epoch values `ev` and
pool name `γp` (additive; `epRun ⊣⊢ ∃ ev γp, epRunAt …`, `epHalted ⊣⊢ ∃ ev γp, epHaltedAt …`), so
that the descriptors' part `PR ev γp pM` of `EpR pM := ∃ ev γp, epRunAt … ev γp ∗ PR ev γp pM` can
return its loan of the same pool (`epochPool_return`). -/

/-- `epRun` at the epoch's values `ev` and pool name `γp`. -/
def swift.epRunAt (γ : sp.Names) (γc γm : GName) (rp : Loc) (x : swift.RunX) (ev : swift.EpV)
    (γp : GName) : IProp netDistGF :=
  iprop(∃ γl : swift.CellNames,
    swift.epochRun (x.epN rp) ev (1 : Qp).half.half γp ∗ swift.epochRest (x.epN rp) ev ∗
    swift.replyChanH γ γc γm rp γl ev.bw ev.rcp ∗ swift.cellFilled γl ∗
    swift.rmTok x.γrm none ∗ ⌜ev.st = swift.stNORMAL⌝)

/-- `epHalted` at the epoch's values `ev` and pool name `γp`. -/
def swift.epHaltedAt (rp : Loc) (x : swift.RunX) (ev : swift.EpV) (γp : GName) :
    IProp netDistGF :=
  iprop(swift.epochRun (x.epN rp) ev (1 : Qp).half.half γp ∗ swift.epochRest (x.epN rp) ev ∗
    swift.replyCellRes rp ev.bw ∗ swift.rmTok x.γrm none ∗ ⌜ev.st = swift.stNORMAL⌝)

theorem swift.epRun_at (γ : sp.Names) (γc γm : GName) (rp : Loc) (x : swift.RunX) :
    swift.epRun γ γc γm rp x ⊣⊢ ∃ (ev : swift.EpV) (γp : GName), swift.epRunAt γ γc γm rp x ev γp := by
  constructor
  · iintro H
    iunfold swift.epRun at H
    icases H with ⟨%ev, %γp, %γl, H⟩
    iexists ev, γp
    iunfold swift.epRunAt
    iexists γl
    iexact H
  · iintro ⟨%ev, %γp, H⟩
    iunfold swift.epRunAt at H
    icases H with ⟨%γl, H⟩
    iunfold swift.epRun
    iexists ev, γp, γl
    iexact H

theorem swift.epHalted_at (rp : Loc) (x : swift.RunX) :
    swift.epHalted rp x ⊣⊢ ∃ (ev : swift.EpV) (γp : GName), swift.epHaltedAt rp x ev γp := by
  constructor
  · iintro H
    iunfold swift.epHalted at H
    icases H with ⟨%ev, %γp, H⟩
    iexists ev, γp
    iunfold swift.epHaltedAt
    iexact H
  · iintro ⟨%ev, %γp, H⟩
    iunfold swift.epHaltedAt at H
    iunfold swift.epHalted
    iexists ev, γp
    iexact H

/-- **`r.repchan.stop()` at given epoch values and pool name** (`epRun_stop`'s `At` form: `ev`
and `γp` are kept). -/
theorem swift.epRunAt_stop (wp_stop : swift.replyChan.stop.specR (hG := hG)) (γ : sp.Names)
    (γc γm : GName) (rp : Loc) (x : swift.RunX) (ev : swift.EpV) (γp : GName) (rc : Loc) :
    {{ swift.epRunAt γ γc γm rp x ev γp ∗
        typedPointsto (swift.fld rp go!"repchan") rc (DFrac.own (1 : Qp).half) }}
      (App (Val (rc @!! go.GoType.PointerType swift.replyChan.ty @!! go!"stop")) (Val #()))
    {{ RET #(); swift.epHaltedAt rp x ev γp ∗
        typedPointsto (swift.fld rp go!"repchan") rc (DFrac.own (1 : Qp).half) }} := by
  unfold swift.epRunAt swift.epochRest swift.RunX.epN
  iintro %Φ ⟨Hep, Hrc⟩ HΦ
  icases Hep with ⟨%γl, Hpool, Hrest, #HrcH, #Hfilled, Hrm, %Hst⟩
  icases Hrest with ⟨Hs, HS1, HS2, Hr, He, Hxe, Hxp, HFQ1⟩
  ihave %Hrceq : ⌜rc = ev.rcp⌝ $$ [Hrc Hr]
  · iapply typedPointsto_agree_wand _ _ _ _ _ $$ Hrc Hr
  subst Hrceq
  ihave #HrcH2 := HrcH
  iunfold swift.replyChanH at HrcH2
  icases HrcH2 with ⟨%rep, %ok, %ex, %ar, %γok, %γex, %γa, -, -, -, -, #Hcell⟩
  iapply wp_fupd
  iapply (wp_stop γ γc γm rp γl ev.bw ev.rcp) $$ [HrcH]
  · iexact HrcH
  inext
  iintro Hback
  ihave Hres : |={⊤}=> swift.replyCellRes rp ev.bw $$ [Hback]
  · iunfold swift.replyBack at Hback
    icases Hback with (Hb | Hk)
    · imodintro; iexact Hb
    · imod swift.cell_claim swift.replyCellN ⊤ (by simp) γl (swift.replyCellRes rp ev.bw)
        $$ [$Hcell $Hk $Hfilled] with >Hb
      imodintro; iexact Hb
  imod Hres
  imodintro
  iapply HΦ
  iframe Hrc
  iunfold swift.epHaltedAt
  simp only [swift.RunX.epN]
  iframe Hpool Hres Hrm
  isplitl [Hs HS1 HS2 Hr He Hxe Hxp HFQ1]
  · unfold swift.epochRest; iframe
  ipureintro; exact Hst

end stop

end Perennial.github_com.imdea_software.swiftpaxos
