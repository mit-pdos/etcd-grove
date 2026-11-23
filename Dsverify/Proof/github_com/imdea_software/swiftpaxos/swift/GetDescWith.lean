/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/GetDescWith.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**`r.getCmdDescWith(x, msg, seq)`** (swift.go:846; round 24, sv-swb; notes/prove-swift.md §30):
the run loop's lookup-or-create of `x`'s descriptor over the descriptors' state `descDS`
(DescDS.lean), with `ConcurrentMap.UpsertVL` (G1: the callback holds the shard's lock token, so
`key`'s entry is fixed while it reads `desc.seq`/`desc.msgs`).

* `swift.descInv_lendL` / `swift.descInv_returnL`: `descInv_lend`/`descInv_return` (StopRound.lean)
  under the Upsert lock token `cmapLocked` (instead of `IterCb`'s pin): the entry's state is lent
  to the callback (`stopDescs`' borrow token `γb`, whose authority the run loop holds at `0`).
* `swift.descDSN`: `propSpecIN`'s `DS` (HandleProposal.lean): `descDS` at the run loop's names
  with the proposal's `γ N r` the replica's, and the descriptors' context `descCtx`.
-/
/- Round 43 (D52 (4)): split by phase; this module holds `wp_coreD`, `wp_proofDS`, `wp_proofD`
and re-exports GetDescWithDefs/Loan/Ents. -/
module


public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GetDescWithEnts
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section rch
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

/-- The running epoch's reply channel (round 45, D54): `epRunL`'s `replyChanH … ev.bw ev.rcp` and
its filled cell, both persistent, kept. -/
theorem swift.epRunL_rc (γ : sp.Names) (γc γm : GName) (rp : Loc) (x : swift.RunX)
    (ev : swift.EpV) (γp : GName) (i : Nat) (Qd : Qp) :
    swift.epRunL γ γc γm rp x ev γp i Qd ⊢
      swift.epRunL γ γc γm rp x ev γp i Qd ∗ ∃ γl : swift.CellNames,
        □ (swift.replyChanH γ γc γm rp γl ev.bw ev.rcp ∗ swift.cellFilled γl) := by
  iintro Hr
  iunfold swift.epRunL at Hr
  icases Hr with ⟨%γl, %q0, Hpool, Hrest, #Hrc, #Hfil, Hrm, %Hst⟩
  isplitl [Hpool Hrest Hrm]
  · iunfold swift.epRunL
    iexists γl, q0
    iframe Hpool Hrest Hrc Hfil Hrm
    ipureintro; exact Hst
  · iexists γl
    imodintro
    iframe Hrc Hfil

/-- **The creator's obligation for the reply channel object** (round 45, D54/D55 (1)): at a
record `c`, `RCh … rcp bw` from the epoch's `replyChanH … bw rcp` with its filled cell
(`descDS`/`epRunL`), the sending context of `ackCtx` (inside `proposeCtxB`) and `descCtx`'s
replica (`Replica ↦□ rr`, `isReplica`'s `N` field and `N ≤ 7`). -/
theorem swift.RCh_of (c : swift.DC) (γl : swift.CellNames) (bw : w32) (rcp : Loc) :
    c.ctx ∗ swift.proposeCtxB c ∗ swift.replyChanH c.γ c.γc c.γm c.rp γl bw rcp ∗
      swift.cellFilled γl ⊢ swift.RCh c.γ c.γc c.γm c.rp rcp bw := by
  iintro ⟨#Hc, #HpB, #Hh, #Hf⟩
  iunfold swift.DC.ctx at Hc
  iunfold swift.descCtxE at Hc
  icases Hc with ⟨%me, %fr, %l, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, #Hrr, #Hrep,
    %Hids, -⟩
  iunfold replica.isReplica at Hrep
  icases Hrep with ⟨%lg, %cfgp, %tbl, %pc, %fr', %nid, %ents, %γpc, %pwsl, %alsl, %latsl, %pws,
    %cwm, -, -, #HN, -⟩
  iunfold swift.proposeCtxB at HpB
  icases HpB with ⟨#Ha, -⟩
  iunfold swift.ackCtx at Ha
  icases Ha with ⟨%sq, %szS, %memS, %bt, %s, %γs, %csv, -, -, %-, -, -, #Hs, #Hsb, #Hcs, %Hcc, -⟩
  iunfold swift.RCh
  iexists γl, c.rr, s, c.N, γs, csv
  iframe Hh Hf Hrr HN Hs Hsb Hcs
  ipureintro; exact ⟨Hcc, Hids.2.2.2.2.1⟩

end rch

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [github_com.orcaman.concurrent_map.Assumptions] [hook.Assumptions]

set_option goose.wp.extras true

theorem swift.Replica.getCmdDescWith.wp_coreD (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (wp_Str : swift.CommandId.String.specS x.str) (hinj : Function.Injective x.str)
    (wp_HasV : ∀ dm γdl, swift.cmapHasV.spec dm γdl)
    (wp_Upsert : github_com.orcaman.concurrent_map.ConcurrentMap.UpsertVL.spec (GF := netDistGF))
    (wp_seq : swift.Replica.handleMsg.seqSpecD γ0 γc γm x)
    (wp_newDesc : ∀ (rp : Loc) (MP : GoInterface → IProp netDistGF), swift.mpTy MP →
      swift.Replica.newDesc.specNc (x.dc γ0 γc γm rp) (swift.RCh γ0 γc γm rp) MP)
    (wp_hd : swift.Replica.handleDesc.specD γ0 γc γm x (swift.RCh γ0 γc γm)) :
    swift.Replica.getCmdDescWith.coreSpecD (swift.descDSN γ0 γc γm x) x γ0 γc γm := by
  intro γ γdl rp xid msg sqb N r b Pm bw qb hmsg hconv
  obtain ⟨mi, rfl⟩ : ∃ mi, msg = GoInterface.ok mi := by
    cases msg with
    | nil => exact absurd rfl hmsg
    | ok mi => exact ⟨mi, rfl⟩
  wp_start as ⟨HDS, Hrdr, Hm, Hbal, %Hbw⟩
  iunfold swift.descDSN at HDS
  icases HDS with ⟨HDS, %Hnames, #Hctx, #HpB, #Hhist⟩
  obtain ⟨hγ, hdl, hN, hr⟩ := Hnames
  subst hγ hdl hN hr
  wp_auto
  wp_apply wp_Str $$ [$cmdId] as cmdId
  iunfold swift.runReader at Hrdr
  icases Hrdr with ⟨%dm, #Hdm, Hrd⟩
  wp_method_call
  wp_auto
  ihave #Hctx2 := Hctx
  iunfold swift.DC.ctx at Hctx2
  iunfold swift.descCtxE at Hctx2
  icases Hctx2 with ⟨%me, %fr, %l, %dm', %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, #Hrr, #Hrep,
    %Hids, #Hex, #Hdr, #Hoe, #Hinv, #Hcfg, #Hninv, #Hdm', #Hcm, #HdI, -⟩
  wp_apply (wp_HasV _ _ _ ((⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ (↑swift.delivN : CoPset))
      (fun _ => iprop(True))) $$ [$Hrd] as %dl ⟨Hrd, -⟩
  · imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.delivN)
      swift.delivN_sub) $$ HdI with ⟨Hi, Hclose⟩
    iunfold swift.delivInv at Hi
    icases Hi with ⟨%M', %bX', %X', %Mx, %rm, >HV, >HXi, >HXeD, >HMx, >HXx, >%HM⟩
    imodintro
    iexists M'
    iframe HV
    iintro HV
    imod Hclose $$ [HV HXi HXeD HMx HXx] with -
    · inext; iunfold swift.delivInv; iexists M', bX', X', Mx, rm; iframe; ipureintro; exact HM
    imodintro
    itrivial
  ihave Hrdr : swift.runReader rp x.γdl $$ [Hrd]
  · iunfold swift.runReader; iexists _; iframe Hrd; iassumption
  cases dl
  · wp_auto
    iunfold swift.descDS at HDS
    icases HDS with ⟨%g, %ev, %γp, %i, HrunL, HSR, Hloan, %Hgev, #HDctx, %Hsq, %Hmp, %HsoK, %HgO, #Hcg,
      Hfp, #HnIfp⟩
    iunfold swift.descStateR at HSR
    icases HSR with ⟨%dm1, Hcd, #Hdm1, Hrd1, #HI, Hst, Hfz, HSa, Hb, HSS, #HSI⟩
    wp_method_call
    wp_auto_lc 1
    irename Hlc1 => HlcC
    ipersist r
    ipersist cmdId
    wp_apply (wp_Upsert dm1 g.γdc (swift.descR x.γd) (x.str xid) interface.nil _
        (fun ex old res => if ex then iprop(⌜res = old⌝ ∗ ∃ (d m : Loc),
          ⌜old = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d⌝ ∗
          desc_ptr ↦ d ∗ msgs_ptr ↦ m ∗
          ghostVar g.γst (1 : Qp).half false ∗ ghostVar g.γb 1 (none : Option github_com.orcaman.concurrent_map.PinD) ∗ ghostMapAuth g.γs 1 (∅ : GMap GoString Bool) ∗
          swift.cntFrozen x.γn false ∗ swift.epRunL γ γc γm rp x ev γp i g.Qd ∗
          ((seqD_ptr ↦ false ∗ swift.bagW m (g.mp xid) ∗ swift.seqStore g) ∨
           (seqD_ptr ↦ true ∗ ∃ S : GMap Loc swift.CommandId, ⌜S !! d = some xid⌝ ∗
             ghostMapAuth g.γS 1 S ∗
             ([∗map] d' ↦ y' ∈ S.delete d, g.so d' y' ∨ ghostMapElem g.γS d' (DFrac.own 1) y') ∗
             g.so d xid)))
          else iprop(∃ (d m sc : Loc) (γi γsg : GName) (γmc : ChanNames),
          ⌜res = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d⌝ ∗
          desc_ptr ↦ d ∗ msgs_ptr ↦ m ∗
          ghostVar g.γst (1 : Qp).half false ∗ ghostVar g.γb 1 (none : Option github_com.orcaman.concurrent_map.PinD) ∗ ghostMapAuth g.γs 1 (∅ : GMap GoString Bool) ∗
          swift.cntFrozen x.γn false ∗ swift.epRunL γ γc γm rp x ev γp i g.Qd ∗ swift.seqStore g ∗
          ((seqD_ptr ↦ false ∗ ∃ (j : Nat) (γsc : ChanNames),
              ghostVar γi (1 : Qp).half (x.str xid, d) ∗
              ghostVar γi (1 : Qp).half.half (x.str xid, d) ∗
              ghostMapElem g.γj γi (DFrac.own (1 : Qp).half) (j, (1 : Qp).half.half) ∗
              typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half) ∗
              typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
              ghostMapElem x.γn j (DFrac.own (1 : Qp).half.half) false ∗
              typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) ∗
              typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half) ∗
              isChanBag γmc m (fun v => iprop(g.mp xid v ∗ □ swift.incW g γi γsg)) ∗
              isChanBag γsc sc (fun wg => iprop(swift.stopMP g.γs γsg (x.str xid) d sc wg ∗
                □ swift.incW g γi γsg)) ∗
              swift.sgTok γsg ∗ typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own (1 : Qp).half)) ∨
           (seqD_ptr ↦ true ∗ ∃ (sqv : GoInterface) (szS : Nat) (memS : w32 → Prop) (q : Qp),
              ghostVar γi 1 (x.str xid, d) ∗
              typedPointsto (swift.dfld d go!"seq") true (DFrac.own (1 : Qp).half) ∗
              swift.dfld d go!"msgs" ↦ m ∗
              isChanBag γmc m (fun v => iprop(g.mp xid v ∗ □ swift.incW g γi γsg)) ∗
              swift.dfld d go!"active" ↦ true ∗
              typedPointsto (swift.dfld d go!"seq") true (DFrac.own (1 : Qp).half) ∗
              swift.dfld d go!"stopChan" ↦ sc ∗ ghostMapElem x.γsh d (DFrac.own 1) q ∗
              swift.descRaw (x.dc γ γc γm rp) (swift.RCh γ γc γm rp) (fun v => iprop(g.mp xid v ∗ □ swift.incW g γi γsg))
                xid g.ev.b sqv g.ev.fq szS g.ev.szF memS g.ev.memF γmc d)))))
      $$ [desc seqD msgs Hst Hb HSa HSS Hfz HrunL seq]
    · iframe Hdm1
      iintro %ex %old %t %Ψ HR Htok HΨ
      cases ex
      · -- a new entry: newDesc, cntL, the spawn (round 27)
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases HR with %Hold
        rw [← Hgev]
        wp_auto_lc 2
        iapply fupd_wp
        imod swift.descInv_allocInc γ x.γd x.γn x.γout g (x.epN rp) (x.DR γ g.ev.b)
            (swift.descGo x.γn g x.str) x.str (x.str xid, (null : Loc)) _ (swift.liveOk_run g)
            $$ [Hst Hlc2]
          with ⟨Hst, %γi, Hγi, Hrj⟩
        · iframe HI; iframe
        imod (ghostVar_alloc (GF := netDistGF) true) with ⟨%γsg, Hsg⟩
        imodintro
        ihave #HDctx2 := HDctx
        iunfold swift.descDSCtx at HDctx2
        icases HDctx2 with ⟨#HcntL, #HdPool, #Hsh, #HMax, ⟨%sqv, %szS, %memS, #HSQ, #HqS, %-⟩, -⟩
        ihave ⟨#HqF, HFQ, HrunLw⟩ := swift.epRunL_fq γ γc γm rp x g.ev γp i g.Qd $$ HrunL
        wp_apply (wp_newDesc rp (fun v => iprop(g.mp xid v ∗ □ swift.incW g γi γsg))
            (swift.mpOk_ty x γ γc γm rp g Hmp xid _)
          (fun d sc wg => iprop(swift.stopMP g.γs γsg (x.str xid) d sc wg ∗ □ swift.incW g γi γsg))
          x.γsh xid g.ev.b x.dm x.γdl x.γn x.d sqv g.ev.fq szS g.ev.szF memS g.ev.memF (1 : Qp).half)
          $$ [HFQ] as %d ⟨Hnew, HFQ⟩
        · iframe HFQ HqF HSQ HqS HMax HcntL Hsh HdPool Hctx
        ihave HrunL := HrunLw $$ HFQ
        iapply fupd_wp
        imod ghostVar_update (x.str xid, d) γi _ $$ Hγi with Hγi
        imodintro
        ihave ⟨%s0, %γmc, %γsc, %m, %sc, %qsh, HmF, #Hmb, Ha, Hs, Hsc, #Hsb, Hshe, Hraw⟩ :=
          swift.descNew_split _ _ _ _ _ _ _ _ _ _ _ _ _ d $$ Hnew
        ihave ⟨Hraw, #Hmx⟩ := swift.descRaw_mutex _ _ _ _ _ _ _ _ _ _ _ _ _ $$ Hraw
        wp_apply sync.Mutex.wp_Lock $$ [$HcntL] as ⟨Hclk, HC⟩
        iunfold swift.cntLInvR at HC
        icases HC with ⟨%n, %cnt, %T, Hn, Hcnt, HG⟩
        cases sqb <;> cases s0 <;> wp_auto
        rotate_left 1
        · -- sequential: no goroutine
          wp_apply sync.Mutex.wp_Unlock $$ [$HcntL $Hclk Hn Hcnt HG]
          · iunfold swift.cntLInvR; iexists n, cnt, T; iframe
          ihave #HR : swift.descR x.γd (x.str xid)
              (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d) $$ []
          · iunfold swift.descR; iexists d; isplitr
            · ipureintro; rfl
            iexact Hmx
          icases (typedPointsto_half_split _ _ _).1 $$ Hs with ⟨Hs1, Hs2⟩
          iapply HΨ $$ HR Htok
          iexists d, m, sc, γi, γsg, γmc
          iframe desc msgs Hst Hb HSa Hfz HrunL HSS
          isplitr
          · ipureintro; rfl
          iright
          iframe seqD
          iexists sqv, szS, memS, qsh
          iframe Hγi Hs1 Hs2 HmF Ha Hsc Hshe Hraw Hmb
        · -- sequential: no goroutine
          wp_apply sync.Mutex.wp_Unlock $$ [$HcntL $Hclk Hn Hcnt HG]
          · iunfold swift.cntLInvR; iexists n, cnt, T; iframe
          ihave #HR : swift.descR x.γd (x.str xid)
              (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d) $$ []
          · iunfold swift.descR; iexists d; isplitr
            · ipureintro; rfl
            iexact Hmx
          icases (typedPointsto_half_split _ _ _).1 $$ Hs with ⟨Hs1, Hs2⟩
          iapply HΨ $$ HR Htok
          iexists d, m, sc, γi, γsg, γmc
          iframe desc msgs Hst Hb HSa Hfz HrunL HSS
          isplitr
          · ipureintro; rfl
          iright
          iframe seqD
          iexists sqv, szS, memS, qsh
          iframe Hγi Hs1 Hs2 HmF Ha Hsc Hshe Hraw Hmb
        · -- sequential: no goroutine
          wp_apply sync.Mutex.wp_Unlock $$ [$HcntL $Hclk Hn Hcnt HG]
          · iunfold swift.cntLInvR; iexists n, cnt, T; iframe
          ihave #HR : swift.descR x.γd (x.str xid)
              (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d) $$ []
          · iunfold swift.descR; iexists d; isplitr
            · ipureintro; rfl
            iexact Hmx
          icases (typedPointsto_half_split _ _ _).1 $$ Hs with ⟨Hs1, Hs2⟩
          iapply HΨ $$ HR Htok
          iexists d, m, sc, γi, γsg, γmc
          iframe desc msgs Hst Hb HSa Hfz HrunL HSS
          isplitr
          · ipureintro; rfl
          iright
          iframe seqD
          iexists sqv, szS, memS, qsh
          iframe Hγi Hs1 Hs2 HmF Ha Hsc Hshe Hraw Hmb
        -- neither: by `routineCount >= MaxDescRoutines`
        wp_if_destruct
        · -- sequential: no goroutine
          wp_apply sync.Mutex.wp_Unlock $$ [$HcntL $Hclk Hn Hcnt HG]
          · iunfold swift.cntLInvR; iexists n, cnt, T; iframe
          ihave #HR : swift.descR x.γd (x.str xid)
              (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d) $$ []
          · iunfold swift.descR; iexists d; isplitr
            · ipureintro; rfl
            iexact Hmx
          icases (typedPointsto_half_split _ _ _).1 $$ Hs with ⟨Hs1, Hs2⟩
          iapply HΨ $$ HR Htok
          iexists d, m, sc, γi, γsg, γmc
          iframe desc msgs Hst Hb HSa Hfz HrunL HSS
          isplitr
          · ipureintro; rfl
          iright
          iframe seqD
          iexists sqv, szS, memS, qsh
          iframe Hγi Hs1 Hs2 HmF Ha Hsc Hshe Hraw Hmb
        · -- a goroutine: its `cntL` slot, its loan, the spawn (`goPre`)
          have hc : sint.Z cnt < sint.Z x.d := by omega
          iapply fupd_wp
          imod swift.cntLGhost_spawn x.γn x.dm x.γdl x.d cnt T hc $$ [HG Hfz] with ⟨%j, HG, Hslot, Hfz⟩
          · iframe
          imodintro
          wp_apply sync.Mutex.wp_Unlock $$ [$HcntL $Hclk Hn Hcnt HG]
          · iunfold swift.cntLInvR; iexists n, (cnt + W64 1), (j :: T); iframe
          -- the goroutine's state and the entry's parts
          iunfold swift.descSlot at Hslot
          icases Hslot with ⟨%hj0, Hel, Hrdj⟩
          icases (ghostMapElem_halves x.γn j false).1 $$ Hel with ⟨Helg, Hel⟩
          icases (swift.elem_quarters x.γn j false).1 $$ Hel with ⟨Hele, Helr⟩
          iapply fupd_wp
          imod swift.descInv_spawnLoan γ x.γd x.γn x.γout g (x.epN rp) (x.DR γ g.ev.b)
              (swift.descGo x.γn g x.str) x.str j _ γi _ (1 : Qp).half.half $$ [Hst Helr Hlc1 Hrj]
            with ⟨Hst, %iL, %q, Hsh_, HX_, Hloan_, Hlr_, Hrj1, Hrj2⟩
          · iframe HI; iframe
          imod swift.shInv_update x.γsh ⊤ (by simp) d qsh q $$ [Hshe] with Hshe
          · iframe Hsh Hshe
          imodintro
          icases (typedPointsto_half_split _ _ _).1 $$ HmF with ⟨HmF1, HmF2⟩
          icases (typedPointsto_half_split _ _ _).1 $$ Ha with ⟨Ha1, Ha2⟩
          icases (typedPointsto_half_split _ _ _).1 $$ Hs with ⟨Hs1, Hs2⟩
          icases (typedPointsto_half_split _ _ _).1 $$ Hs2 with ⟨Hs2, Hs3⟩
          icases (typedPointsto_half_split _ _ _).1 $$ Hsc with ⟨Hsc1, Hsc2⟩
          icases (ghostVar_split_half γi _ _).1 $$ Hγi with ⟨Hγi1, Hγi2⟩
          icases (ghostVar_split_half γi _ _).1 $$ Hγi1 with ⟨Hγi1, Hγi3⟩
          -- round 45 (D54/D55 (1)): the epoch's reply channel object for `goPre`
          ihave ⟨HrunL, %γl, #HrcF⟩ := swift.epRunL_rc γ γc γm rp x g.ev γp i g.Qd $$ HrunL
          ihave #HRCe : swift.RCh γ γc γm rp g.ev.rcp g.ev.bw $$ []
          · icases HrcF with ⟨#HrcH, #Hfil⟩
            iapply (swift.RCh_of (x.dc γ γc γm rp) γl g.ev.bw g.ev.rcp)
            iframe Hctx HpB HrcH Hfil
          wp_apply wp_fork $$ [HmF1 Ha1 Hs3 Hsc1 Hshe Hraw Hsh_ HX_ Hloan_ Hlr_ Helg Hrdj Hγi1 Hrj1]
          · wp_apply (wp_hd rp g d xid γi γsg) $$ [HmF1 Ha1 Hs3 Hsc1 Hshe Hraw Hsh_ HX_ Hloan_ Hlr_ Helg Hrdj Hγi1 Hrj1]
            · iunfold swift.goPre
              iframe Hctx HDctx HI HSI
              isplitr
              · -- round 37b (table rev 8c, GAP-37b/37d): `descDSN`'s `runLoopCtx`
                iunfold swift.ownCtx
                iframe HDctx HpB Hhist HRCe Hcg
                ipureintro
                exact ⟨Hmp, Hsq, HsoK.2.2.1, HsoK.2.2.2.2.2,
                  fun d y => (HsoK.2.2.2.2.1 d y).trans (HsoK.2.2.2.1 d y)⟩
              isplitr
              · ipureintro; exact Hmp
              iexists m, sc, γmc, γsc, sqv, szS, memS, j, iL, q
              iframe HmF1 Ha1 Hs3 Hsc1 Hshe Hraw Hsh_ Hloan_ Hlr_ Helg Hrdj Hγi1 Hrj1 Hmb Hsb HRCe
              isplitl [HX_]
              · dsimp only [swift.RunX.epN]
                iexact HX_
              ipureintro; exact hj0
            ipureintro; exact isPanic_intoVal ()
          ihave #HR : swift.descR x.γd (x.str xid)
              (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d) $$ []
          · iunfold swift.descR; iexists d; isplitr
            · ipureintro; rfl
            iexact Hmx
          iapply HΨ $$ HR Htok
          iexists d, m, sc, γi, γsg, γmc
          iframe desc msgs Hst Hb HSa Hfz HrunL HSS
          isplitr
          · ipureintro; rfl
          ileft
          iframe seqD
          iexists j, γsc
          iframe Hγi2 Hγi3 Hrj2 Hs1 Hs2 Hele Ha2 HmF2 Hmb Hsb Hsc2
          iunfold swift.sgTok
          iexact Hsg

      simp only [↓reduceIte]
      iunfold swift.descR at HR
      icases HR with ⟨%d0, %Hd0, #Hmx⟩
      subst Hd0
      wp_auto_lc 4
      iapply fupd_wp
      -- round 38 (table rev 9a T5l): R's refuter `γs k ↦ false` (its round map is ∅ outside
      -- `stopDescs`), then the lock-lend of the entry's outer part
      imod ghost_map_insert (γ := g.γs) (x.str xid) false (GMap.lookup_empty _) $$ HSa
        with ⟨HSa, Href⟩
      rw [← swift.lendRef_run g (x.str xid)]
      imod swift.descInv_lockLend γ x.γd x.γn x.γout g (x.epN rp) (x.DR γ g.ev.b) x.str (x.str xid) _ t
          .run (ghostVar g.γst (1 : Qp).half false) (swift.liveOk_run g) $$ [Hst Htok Href Hlc1]
        with ⟨Hst, %d, %y, %s, %m, %Hv, Hs4, Hm8, #Hbag, Hw⟩
      · iframe HI; iframe
      imodintro
      have hd : d0 = d := swift.mkOk_desc_inj d0 d Hv.1
      subst hd
      have hy : y = xid := hinj Hv.2.symm
      subst hy
      cases s
      · -- at home or running: the loads (with the lent fractions), the return (T5r)
        iapply wp_fupd
        wp_auto
        imod swift.descInv_lockReturn γ x.γd x.γn x.γout g (x.epN rp) (x.DR γ g.ev.b) x.str (x.str y) _ t
            .run d0 false m (ghostVar g.γst (1 : Qp).half false) (swift.liveOk_run g) rfl
            $$ [Hst Hw Hs4 Hm8 Hlc2] with ⟨Hst, Htok, Href⟩
        · iframe HI; iframe
        rw [swift.lendRef_run g (x.str y)]
        imod ghost_map_delete (γ := g.γs) $$ HSa Href with HSa
        rw [GMap.delete_insert _ _ false (GMap.lookup_empty _)]
        imodintro
        ihave #HR : swift.descR x.γd (x.str y)
            (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d0) $$ []
        · iunfold swift.descR; iexists d0; isplitr
          · ipureintro; rfl
          iexact Hmx
        iapply HΨ $$ HR Htok
        simp only [↓reduceIte]
        isplitr
        · ipureintro; first | rfl | trivial
        iexists d0, m
        iframe
        isplitr
        · ipureintro; rfl
        ileft
        iframe
        iapply Hbag
        ipureintro; trivial
      · -- a sequential descriptor (G9): its owner state to the run loop's store while lent
        -- (round 38, gap 38-1: `descInv_seqTakeL`), the loads, the return
        iapply fupd_wp
        imod swift.descInv_seqTakeL γ x.γd x.γn x.γout g (x.epN rp) (x.DR γ g.ev.b) x.str hinj
            (x.dc γ γc γm rp) (swift.RCh γ γc γm rp) HsoK (x.str y) _ t .run d0 y
            (ghostVar g.γst (1 : Qp).half false) (swift.liveOk_run g) ⟨rfl, rfl⟩
            $$ [Hst Hw Hs4 HSS Hlc2 Hlc3] with ⟨Hst, Hw, Hs4, %S, %HSd, HSA, HSm, Hso⟩
        · iframe HI HSI; iframe
        imodintro
        iapply wp_fupd
        wp_auto
        imod swift.descInv_lockReturn γ x.γd x.γn x.γout g (x.epN rp) (x.DR γ g.ev.b) x.str (x.str y) _ t
            .run d0 true m (ghostVar g.γst (1 : Qp).half false) (swift.liveOk_run g) rfl
            $$ [Hst Hw Hs4 Hm8 Hlc4] with ⟨Hst, Htok, Href⟩
        · iframe HI; iframe
        rw [swift.lendRef_run g (x.str y)]
        imod ghost_map_delete (γ := g.γs) $$ HSa Href with HSa
        rw [GMap.delete_insert _ _ false (GMap.lookup_empty _)]
        imodintro
        ihave #HR : swift.descR x.γd (x.str y)
            (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d0) $$ []
        · iunfold swift.descR; iexists d0; isplitr
          · ipureintro; rfl
          iexact Hmx
        iapply HΨ $$ HR Htok
        simp only [↓reduceIte]
        isplitr
        · ipureintro; first | rfl | trivial
        iexists d0, m
        iframe
        isplitr
        · ipureintro; rfl
        iright
        iframe
        ipureintro; exact HSd

    -- the commit: both cases end in one state (`swift.commit_mono`), then one tail
    iintro %ex %old %res HQ
    iapply (swift.commit_mono (⊤ \ ↑github_com.orcaman.concurrent_map.cmapN)
      (fun M => github_com.orcaman.concurrent_map.cmapView g.γdc M)
      (fun M => github_com.orcaman.concurrent_map.cmapView g.γdc (<[x.str xid := res]> M))
      (fun M => M !! x.str xid = if ex then some old else none)
      iprop(∃ (d m : Loc), ⌜res = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d⌝ ∗
          desc_ptr ↦ d ∗ msgs_ptr ↦ m ∗
          ghostVar g.γst (1 : Qp).half false ∗ ghostVar g.γb 1 (none : Option github_com.orcaman.concurrent_map.PinD) ∗ ghostMapAuth g.γs 1 (∅ : GMap GoString Bool) ∗
          swift.cntFrozen x.γn false ∗ swift.epRunL γ γc γm rp x ev γp i g.Qd ∗
          ((seqD_ptr ↦ false ∗ swift.bagW m (g.mp xid) ∗ swift.seqStore g) ∨
           (seqD_ptr ↦ true ∗ ∃ S : GMap Loc swift.CommandId, ⌜S !! d = some xid⌝ ∗
             ghostMapAuth g.γS 1 S ∗
             ([∗map] d' ↦ y' ∈ S.delete d, g.so d' y' ∨ ghostMapElem g.γS d' (DFrac.own 1) y') ∗
             g.so d xid))))
    isplitl [HQ HlcC]
    rotate_left
    · iintro ⟨%d, %m, %Hres, Hdesc, Hmsgs, Hst, Hb, HSa, Hfz, HrunL, Hcase⟩
      -- the message is of the descriptors' epoch (`ballot`'s shares agree)
      ihave ⟨%Hbev, HrunL, Hbal⟩ := swift.epRunL_ballot γ γc γm rp x ev γp i g.Qd bw qb $$ [HrunL Hbal]
      · iframe
      have hb : b = g.ev.b := by rw [Hgev, ← Hbev, Hbw]
      ihave Hmsg : g.mp xid (GoInterface.ok mi) $$ [Hm]
      · iapply (hconv g Hmp hb.symm); iexact Hm
      icases Hcase with (⟨HseqD, #Hmb, HSS⟩ | ⟨HseqD, %S, %HSd, HSA, HSm, Hso⟩)
      · wp_auto
        -- the send on the goroutine's channel
        iunfold swift.bagW at Hmb
        icases Hmb with ⟨%γm', %W, #Hmb, #HW⟩
        wp_apply (wp_bag_send (t := go.InterfaceType []) γm' m (GoInterface.ok mi)
            (fun v => iprop(g.mp xid v ∗ □ W))) $$ [Hmsg]
        · iframe Hmb HW Hmsg
        try wp_auto
        iapply HΦ
        iframe Hbal Hrdr
        iunfold swift.descDSN
        iframe Hctx HpB Hhist
        isplitl [HrunL Hloan Hcd Hrd1 Hfz HSa Hst Hb HSS Hfp]
        · iunfold swift.descDS
          iexists g, ev, γp, i
          iframe HrunL Hloan HDctx Hcg Hfp HnIfp
          isplitl [Hcd Hrd1 Hfz HSa Hst Hb HSS]
          · iunfold swift.descStateR
            iexists dm1
            iframe
            iframe Hdm1 HI HSI
          ipureintro; exact ⟨Hgev, Hsq, Hmp, HsoK, HgO⟩
        ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      · -- a sequential descriptor: the run loop's inline `handleMsg` (`seqSpecD`)
        wp_auto_lc 4
        -- round 46 (D60, O1-b): the epoch's reply channel object for the inline owner's `ownCtx`
        ihave ⟨HrunL, %γl, #HrcF⟩ := swift.epRunL_rc γ γc γm rp x ev γp i g.Qd $$ HrunL
        ihave #HRCe : swift.RCh γ γc γm rp g.ev.rcp g.ev.bw $$ []
        · rw [Hgev]
          icases HrcF with ⟨#HrcH, #Hfil⟩
          iapply (swift.RCh_of (x.dc γ γc γm rp) γl ev.bw ev.rcp)
          iframe Hctx HpB HrcH Hfil
        wp_apply (wp_seq rp g ev γp i d xid (GoInterface.ok mi) bw qb) $$ [HrunL Hloan Hcd Hrd1 Hfz HSa Hst Hb Hrdr Hbal
            Hso Hmsg Hlc1 Hlc2 Hlc3 Hlc4] as %v ⟨HB, Hrdr, Hbal, Hres⟩
        · iframe Hctx Hrdr Hbal Hso Hmsg Hlc1 Hlc2 Hlc3 Hlc4
          isplitr
          · -- round 38 (table rev 9 R9-3): the inline owner's context, from `descDSN`
            iunfold swift.ownCtx
            iframe HDctx HpB Hhist HRCe Hcg
            ipureintro
            exact ⟨Hmp, Hsq, HsoK.2.2.1, HsoK.2.2.2.2.2,
              fun d y => (HsoK.2.2.2.2.1 d y).trans (HsoK.2.2.2.1 d y)⟩
          iunfold swift.descDSB
          iframe HrunL Hloan HDctx Hcg
          isplitl [Hcd Hrd1 Hfz HSa Hst Hb]
          · iunfold swift.descStateB
            iexists dm1
            iframe
            iframe Hdm1 HI HSI
          ipureintro; exact ⟨Hgev, Hsq, Hmp, HsoK, HgO⟩
        try wp_auto
        iapply HΦ
        iframe Hbal Hrdr
        iunfold swift.descDSN
        iframe Hctx HpB Hhist
        iunfold swift.descDSB at HB
        icases HB with ⟨HrunL, HSB, Hloan, -, -, -, -, -, -⟩
        iunfold swift.descStateB at HSB
        icases HSB with ⟨%dm2, Hcd, #Hdm2, Hrd1, #HI2, Hst, Hfz, HSa, Hb, #HSI2⟩
        isplitl [HrunL Hloan Hcd Hrd1 Hfz HSa Hst Hb HSA HSm Hres Hfp]
        · iunfold swift.descDS
          iexists g, ev, γp, i
          iframe HrunL Hloan HDctx Hcg Hfp HnIfp
          isplitl [Hcd Hrd1 Hfz HSa Hst Hb HSA HSm Hres]
          · iunfold swift.descStateR
            iexists dm2
            iframe Hcd Hrd1 Hfz HSa Hst Hb Hdm2 HI2 HSI2
            iunfold swift.seqStore
            iexists S
            iframe HSA
            iapply (BigSepM.bigSepM_delete HSd).2
            iframe HSm
            icases Hres with (Hres | Hres)
            · ileft; iexact Hres
            · iright
              iexact Hres
          ipureintro; exact ⟨Hgev, Hsq, Hmp, HsoK, HgO⟩
        ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    cases ex
    · -- a new entry (round 27): the entry and the incarnation committed with the view's insert
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases HQ with ⟨%d, %m, %sc, %γi, %γsg, %γmc, %Hres, Hdesc, Hmsgs, Hst, Hb, HSa, Hfz, HrunL, HSS,
        Hcase⟩
      inext
      imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.descN)
        swift.descN_sub) $$ HI with ⟨Hi, Hclose⟩
      imod lc_fupd_elim_later (E := (⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ ↑swift.descN)
        $$ HlcC Hi with Hi
      iunfold swift.descInv at Hi
      icases Hi with ⟨%st, Hst2, Hrest⟩
      icombine Hst Hst2 gives %Hc
      obtain ⟨-, Heq⟩ := Hc
      subst Heq
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hrest with ⟨%Mc, Hrest⟩
      icases Hrest with ⟨%q0, Hrest⟩
      icases Hrest with ⟨%L', Hrest⟩
      icases Hrest with ⟨%dm2, Hrest⟩
      icases Hrest with ⟨%W, Hview, HW, %HWd, Hents, HK, Hpool, Hrec, Hled, Hrca⟩
      imod (fupd_mask_subseteq (E1 := (⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ ↑swift.descN)
        (E2 := ∅) (by simp)) with Hback
      imodintro
      iexists Mc
      try dsimp only
      iframe Hview
      iintro %Hk Hview
      imod Hback with -
      subst Hres
      have hWk : W !! (x.str xid) = none := by
        cases h : W !! (x.str xid) with
        | none => rfl
        | some _ => exact absurd Hk (HWd _ (by rw [h]; simp))
      icases Hcase with (⟨HseqD, %j, %γsc, Hv, Hvq, Hrc, Hs2, Hs4, Hel, Ha, Hm, #Hmb, #Hsb, Hsg, Hsc⟩ |
        ⟨HseqD, %sqv, %szS, %memS, %q, Hv, Hs2, Hm, #Hmb, Ha, Hs, Hsc, Hsh, Hraw⟩)
      · -- a goroutine's entry (running, unsignalled)
        imod swift.descEnts_insertGo γ x.γd x.γn g (x.DR γ g.ev.b) x.str Mc (x.str xid) d xid
          γi γsg j m sc γmc γsc Hk rfl _ W hWk $$ [Hents HK Hv Hvq Hrc Hs2 Hs4 Hel Ha Hm Hsg Hsc]
          with ⟨Hents, HK, #Hw⟩
        · isplitl [Hents]
          · iexact Hents
          isplitl [HK]
          · iexact HK
          isplitl [Hv]
          · iexact Hv
          isplitl [Hvq]
          · iexact Hvq
          iframe; iframe Hmb Hsb
        imod Hclose $$ [Hst2 HW Hview Hents HK Hpool Hrec Hled Hrca] with -
        · inext
          iunfold swift.descInv
          iexists false
          simp only [Bool.false_eq_true, ↓reduceIte]
          iframe Hst2
          iexists _, q0, L', dm2, W
          iframe
          ipureintro
          intro k' hk'
          rw [GMap.lookup_insert_eq_iff]
          split
          · simp
          · exact HWd k' hk'
        imodintro
        iexists d, m
        iframe Hdesc Hmsgs Hst Hb HSa Hfz HrunL
        isplitr
        · ipureintro; rfl
        ileft
        iframe HseqD HSS
        iunfold swift.bagW
        iexists γmc, (swift.incW g γi γsg)
        iframe Hmb Hw
      · -- a sequential descriptor: its `γS` element in the run loop's store, its states created
        iunfold swift.seqStore at HSS
        icases HSS with ⟨%S, HSA, HSm⟩
        imod swift.seqStore_add γ (x.DR γ g.ev.b) g (x.dc γ γc γm rp) (swift.RCh γ γc γm rp) HsoK S d xid _ $$ [HSA HSm Ha]
          with ⟨%S', %HS', HSA, HSm, HeS, Ha⟩
        · iframe
        imod swift.descEnts_insertSeq γ x.γd x.γn g x.str (x.DR γ g.ev.b) (x.dc γ γc γm rp)
            (swift.RCh γ γc γm rp) HsoK rfl Mc (x.str xid) d xid γi γsg
            sqv g.ev.fq szS g.ev.szF memS g.ev.memF γmc m sc q Hk rfl _ g.γS (Or.inl rfl) W hWk
          $$ [Hents HK Hv Hs2 HeS Hm Ha Hs Hsc Hsh Hraw] with ⟨Hents, HK, Hso⟩
        · iframe; iframe Hmb
        ihave Hso := HsoK.2.2.2.2.1 d xid $$ Hso
        imod Hclose $$ [Hst2 HW Hview Hents HK Hpool Hrec Hled Hrca] with -
        · inext
          iunfold swift.descInv
          iexists false
          simp only [Bool.false_eq_true, ↓reduceIte]
          iframe Hst2
          iexists _, q0, L', dm2, W
          iframe
          ipureintro
          intro k' hk'
          rw [GMap.lookup_insert_eq_iff]
          split
          · simp
          · exact HWd k' hk'
        imodintro
        iexists d, m
        iframe Hdesc Hmsgs Hst Hb HSa Hfz HrunL
        isplitr
        · ipureintro; rfl
        iright
        iframe HseqD
        iexists S'
        iframe HSA HSm Hso
        ipureintro; exact HS'
    simp only [↓reduceIte]
    icases HQ with ⟨%Hres, %d, %m, %Hold, Hdesc, Hmsgs, Hst, Hb, HSa, Hfz, HrunL, Hcase⟩
    subst Hres
    inext
    imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.descN)
      swift.descN_sub) $$ HI with ⟨Hi, Hclose⟩
    iunfold swift.descInv at Hi
    icases Hi with ⟨%st, >Hst2, Hrest⟩
    icombine Hst Hst2 gives %Hc
    obtain ⟨-, Heq⟩ := Hc
    subst Heq
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hrest with ⟨%Mc, Hrest⟩
    icases Hrest with ⟨%q0, Hrest⟩
    icases Hrest with ⟨%L', Hrest⟩
    icases Hrest with ⟨%dm2, Hrest⟩
    icases Hrest with ⟨%W, >Hview, Hrest⟩
    imod (fupd_mask_subseteq (E1 := (⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ ↑swift.descN)
      (E2 := ∅) (by simp)) with Hback
    imodintro
    iexists Mc
    try dsimp only
    iframe Hview
    iintro %Hk Hview
    try simp only [↓reduceIte] at Hk
    rw [GMap.insert_id Mc _ _ Hk]
    imod Hback with -
    imod Hclose $$ [Hst2 Hview Hrest] with -
    · inext
      iunfold swift.descInv
      iexists false
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hst2
      iexists Mc, q0, L', dm2, W
      iframe
    imodintro
    iexists d, m
    iframe Hdesc Hmsgs Hst Hb HSa Hfz HrunL Hcase
    ipureintro; exact Hold
  · wp_auto
    iapply HΦ
    iframe Hbal Hrdr
    iunfold swift.descDSN
    iframe HDS Hctx HpB Hhist
    ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩

/-- **`getCmdDescWith` with a proposal** (`propSpecIN`; round 27: from `wp_coreD`). -/
theorem swift.Replica.getCmdDescWith.wp_proofDS (γ0 : sp.Names) (c_γc c_γm : GName) (x : swift.RunX)
    (wp_Str : swift.CommandId.String.specS x.str) (hinj : Function.Injective x.str)
    (wp_HasV : ∀ dm γdl, swift.cmapHasV.spec dm γdl)
    (wp_Upsert : github_com.orcaman.concurrent_map.ConcurrentMap.UpsertVL.spec (GF := netDistGF))
    (wp_seq : swift.Replica.handleMsg.seqSpecD γ0 c_γc c_γm x)
    (wp_newDesc : ∀ (rp : Loc) (MP : GoInterface → IProp netDistGF), swift.mpTy MP →
      swift.Replica.newDesc.specNc (x.dc γ0 c_γc c_γm rp) (swift.RCh γ0 c_γc c_γm rp) MP)
    (wp_hd : swift.Replica.handleDesc.specD γ0 c_γc c_γm x (swift.RCh γ0 c_γc c_γm)) :
    swift.Replica.getCmdDescWith.propSpecIN (swift.descDSNo γ0 c_γc c_γm x) := by
  intro γ γcl γdl rp pm gp xid c dep hs sq sqb N r b ld s B D P H bw qb
  iintro %Φ ⟨#Hpkg, HDS, Hrdr, Hm, Hnt, Hbal, %Hbw⟩ HΦ
  iunfold swift.descDSNo at HDS
  icases HDS with ⟨HDS, %hγcl⟩
  subst hγcl
  iunfold swift.descDSN at HDS
  icases HDS with ⟨HDS, %Hnames, #Hctx, #HpB, #Hhist⟩
  obtain ⟨hγ, hdl, hN, hr⟩ := Hnames
  subst hγ hdl hN hr
  have hconv : ∀ g : swift.DescG, swift.mpOk x γ c_γc c_γm rp g → g.ev.b = b →
      swift.propMsgR γ pm gp xid c dep hs sq x.N x.r b ld s B D P H ∗
        swift.claimTok x.γcl (b, toCmdId xid) .fresh ⊢
        g.mp xid (interface.mkOk (go.GoType.PointerType swift.proposeMsg.ty) #pm) := by
    intro g hmpOk hb
    have hmp : _ = _ := hmpOk
    rw [hmp]
    iintro ⟨Hm, Hnt⟩
    iunfold swift.descMP
    iright; ileft
    iexists pm, gp, c, dep, hs, sq, ld, s, B, D, P, H
    isplitr
    · ipureintro; rfl
    rw [hb]
    iframe Hm
    iexact Hnt
  iapply (swift.Replica.getCmdDescWith.wp_coreD γ c_γc c_γm x wp_Str hinj wp_HasV wp_Upsert wp_seq
    wp_newDesc wp_hd γ x.γdl rp xid (interface.mkOk (go.GoType.PointerType swift.proposeMsg.ty) #pm) sqb
    x.N x.r b iprop(swift.propMsgR γ pm gp xid c dep hs sq x.N x.r b ld s B D P H ∗
      swift.claimTok x.γcl (b, toCmdId xid) .fresh) bw qb
    (by simp [interface.mkOk]) hconv) $$ [HDS Hrdr Hm Hnt Hbal]
  rotate_left
  · iintro %d
    inext
    iintro ⟨HDS, Hrdr, Hbal⟩
    iapply HΦ
    iframe Hrdr Hbal
    iunfold swift.descDSNo; iframe HDS; ipureintro; rfl
  iframe Hrdr Hm Hnt Hbal
  isplitr [HDS]
  · iexact Hpkg
  isplitl [HDS]
  · iunfold swift.descDSN; iframe HDS Hctx HpB Hhist; ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
  ipureintro; exact Hbw

/-- `wp_proofDS` at the old binders (round 26; ServersLink's call): the sequential inline call's
spec is still OPEN on the descriptor side (task 3: `handleMsg.seqSpecD` from `handleMsg`'s cases
over the sequential state `g.so`, notes/prove-swift.md §32). -/
theorem swift.Replica.getCmdDescWith.wp_proofD (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (wp_Str : swift.CommandId.String.specS x.str) (hinj : Function.Injective x.str)
    (wp_HasV : ∀ dm γdl, swift.cmapHasV.spec dm γdl)
    (wp_Upsert : github_com.orcaman.concurrent_map.ConcurrentMap.UpsertVL.spec (GF := netDistGF))
    (wp_newDesc : ∀ (rp : Loc) (MP : GoInterface → IProp netDistGF), swift.mpTy MP →
      swift.Replica.newDesc.specNc (x.dc γ0 γc γm rp) (swift.RCh γ0 γc γm rp) MP)
    -- round 44 (D53 (1)): the linked specs (DescLink.lean), passed in by ServersLink
    (wp_seq : swift.Replica.handleMsg.seqSpecD γ0 γc γm x)
    (wp_hd : swift.Replica.handleDesc.specD γ0 γc γm x (swift.RCh γ0 γc γm)) :
    swift.Replica.getCmdDescWith.propSpecIN (swift.descDSNo γ0 γc γm x) :=
  swift.Replica.getCmdDescWith.wp_proofDS γ0 γc γm x wp_Str hinj wp_HasV wp_Upsert
    wp_seq
    -- round 39 (D43 (5)): `newDesc` at the replica's records, a hypothesis linked in ServersLink
    -- (`swift.Replica.newDesc.wp_linked`, NewDescLink.lean)
    wp_newDesc
    wp_hd

end proof


end Perennial.github_com.imdea_software.swiftpaxos
