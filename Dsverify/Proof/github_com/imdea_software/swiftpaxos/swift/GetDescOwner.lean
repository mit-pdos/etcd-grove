/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/GetDescOwner.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**`wp_coreO`: `r.getCmdDesc(y, nil, nil)` from an owner record** (round O1, sv-swa; D59 (3); plan
R8.2 (6); table §3R10.7 T14's nested lookup, §3R11.15 `depSpecR`): `depSpecR (x.dcK … rp g k)`
for both owner kinds, under the Löb bundle's hypothesis `□ ▷ handleDescR` (DescBundle.lean), which
the creation's `go r.handleDesc(desc, cmdId)` uses (`wp_fork`). `wp_coreD` (GetDescWith.lean) is
the template; the differences are the creator's resources:
- the not-stopped witness is the owner's loan token (`envK`), not the run loop's `γst` half;
- `r.cmdDescs` is loaded from `envK`'s `descX q` (R9-1);
- T5l/T5r lend with `ρ = own iL j0` (a quarter of the loan's receipt);
- T2's `FQ` is `shOwnR`'s share, agreed with `g.ev.fq` (`descInv_fqAgree`);
- T4n's registry share is the loan record's (`descInv_loanRecAcc`), T4l is `descInv_spawnLoanL`;
- T3'c puts the raw form in the inbox (`descEnts_insertSeqI`);
- `msg = nil`: no send, no inline call.
The ghost steps are in GetDescOwnerSteps.lean.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GetDescOwnerSteps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescBundle

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [github_com.orcaman.concurrent_map.Assumptions] [hook.Assumptions]

set_option goose.wp.extras true

/-- **`depSpecR` at an owner record** (round O1): see the file header. -/
theorem swift.Replica.getCmdDescWith.wp_coreO (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (wp_Str : swift.CommandId.String.specS x.str) (hinj : Function.Injective x.str)
    (wp_HasV : ∀ dm γdl, swift.cmapHasV.spec dm γdl)
    (wp_Upsert : github_com.orcaman.concurrent_map.ConcurrentMap.UpsertVL.spec (GF := netDistGF))
    (wp_newDesc : ∀ (rp : Loc) (MP : GoInterface → IProp netDistGF), swift.mpTy MP →
      swift.Replica.newDesc.specNc (x.dc γ0 γc γm rp) (swift.RCh γ0 γc γm rp) MP)
    (rp : Loc) (g : swift.DescG) (k : swift.OwnK) :
    ⊢ □ ▷ swift.handleDescR γ0 γc γm x (swift.RCh γ0 γc γm) -∗
      swift.depSpecR (x.dcK γ0 γc γm rp g k) := by
  iintro #IH
  iunfold swift.depSpecR
  imodintro
  iintro %d %q %b %bw %stp %rcp %xid
  imodintro
  iintro %Φ ⟨#Hpkg, #Hctx, HeR, Hsh⟩ HΦ
  -- the owner's fields
  iunfold swift.shOwnR at Hsh
  icases Hsh with ⟨Hstat, ⟨%fq, %szF, %memF, HFQ, #HqO, %HmO⟩, Hrdr, Henv, Hpin⟩
  ihave Henv := swift.envK_openK γ0 γc γm x rp g k d q $$ Henv
  icases Henv with ⟨%iL, %j0, Hloan, Hr, ⟨%dmX, HX⟩, #HE, Hback⟩
  iunfold swift.descX at HX
  icases HX with ⟨Hcd, #Hdm1⟩
  iunfold swift.epInvs at HE
  icases HE with ⟨#HI, #HSI, #HO⟩
  ihave #HO2 := HO
  iunfold swift.ownCtx at HO2
  icases HO2 with ⟨#HDctx, #HpB, #Hhist, #HoRC, %Hpure, -⟩
  obtain ⟨Hmp, Hsq, Hsr, Hshsr, HsrA⟩ := Hpure
  iunfold swift.ownRdr at Hrdr
  icases Hrdr with ⟨%dmR, #HdmR, HrdR⟩
  -- into `getCmdDescWith`
  wp_auto
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  simp only [swift.ctx_dcK, swift.dcK_rp, swift.dcK_γdl, swift.dcK_γe, swift.dcK_γxe, swift.dcK_rr]
  wp_apply wp_Str $$ [$cmdId] as cmdId
  wp_method_call
  wp_auto
  ihave #Hctx0 := Hctx
  ihave #Hctx2 := Hctx0
  iunfold swift.DC.ctx at Hctx2
  iunfold swift.descCtxE at Hctx2
  icases Hctx2 with ⟨%me, %fr, %l, %dm', %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, #Hrr, #Hrep,
    %Hids, #Hex, #Hdr, #Hoe, #Hinv, #Hcfg, #Hninv, #Hdm', #Hcm, #HdI, -⟩
  wp_apply (wp_HasV _ _ _ ((⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ (↑swift.delivN : CoPset))
      (fun _ => iprop(True))) $$ [$HrdR] as %dl ⟨HrdR, -⟩
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
  cases dl
  · wp_auto
    wp_method_call
    wp_auto_lc 3
    -- T2's `FQ` (round O1): the owner's share is the epoch's
    iapply fupd_wp
    imod swift.descInv_fqAgree γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b)
        (swift.descGo x.γn g x.str) x.str (swift.epochLoan g.γq iL q) (swift.liveOk_loan g iL q)
        rp rfl fq q $$ [Hlc1 Hloan HFQ] with ⟨Hloan, HFQ, %Hfq, #HqF⟩
    · iframe HI Hlc1 Hloan HFQ
    imodintro
    subst Hfq
    irename Hlc2 => HlcC
    irename Hlc3 => HlcD
    ipersist r
    ipersist cmdId
    wp_apply (wp_Upsert dmX g.γdc (swift.descR x.γd) (x.str xid) interface.nil _
        (fun ex old res => if ex then iprop(⌜res = old⌝ ∗ ∃ (dd m : Loc) (s : Bool),
          ⌜old = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #dd⌝ ∗
          desc_ptr ↦ dd ∗ msgs_ptr ↦ m ∗ seqD_ptr ↦ s ∗
          swift.epochLoan g.γq iL q ∗
          ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) (j0, (1 : Qp).half.half) ∗
          typedPointsto (swift.fld rp go!"FQ") g.ev.fq (DFrac.own q) ∗
          sync.isMutex (swift.dfld dd go!"successorsL") (swift.succInv dd))
          else iprop(∃ (dd m sc : Loc) (γi γsg : GName) (γmc : ChanNames),
          ⌜res = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #dd⌝ ∗
          desc_ptr ↦ dd ∗ msgs_ptr ↦ m ∗
          swift.epochLoan g.γq iL q ∗
          ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) (j0, (1 : Qp).half.half) ∗
          typedPointsto (swift.fld rp go!"FQ") g.ev.fq (DFrac.own q) ∗
          sync.isMutex (swift.dfld dd go!"successorsL") (swift.succInv dd) ∗
          ((seqD_ptr ↦ false ∗ ∃ (j : Nat) (γsc : ChanNames),
              ghostVar γi (1 : Qp).half (x.str xid, dd) ∗
              ghostVar γi (1 : Qp).half.half (x.str xid, dd) ∗
              ghostMapElem g.γj γi (DFrac.own (1 : Qp).half) (j, (1 : Qp).half.half) ∗
              typedPointsto (swift.dfld dd go!"seq") false (DFrac.own (1 : Qp).half) ∗
              typedPointsto (swift.dfld dd go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
              ghostMapElem x.γn j (DFrac.own (1 : Qp).half.half) false ∗
              typedPointsto (swift.dfld dd go!"active") true (DFrac.own (1 : Qp).half) ∗
              typedPointsto (swift.dfld dd go!"msgs") m (DFrac.own (1 : Qp).half) ∗
              isChanBag γmc m (fun v => iprop(g.mp xid v ∗ □ swift.incW g γi γsg)) ∗
              isChanBag γsc sc (fun wg => iprop(swift.stopMP g.γs γsg (x.str xid) dd sc wg ∗
                □ swift.incW g γi γsg)) ∗
              swift.sgTok γsg ∗ typedPointsto (swift.dfld dd go!"stopChan") sc (DFrac.own (1 : Qp).half)) ∨
           (seqD_ptr ↦ true ∗ ∃ (sqv : GoInterface) (szS : Nat) (memS : w32 → Prop) (qsh : Qp),
              ghostVar γi 1 (x.str xid, dd) ∗
              typedPointsto (swift.dfld dd go!"seq") true (DFrac.own (1 : Qp).half) ∗
              swift.dfld dd go!"msgs" ↦ m ∗
              isChanBag γmc m (fun v => iprop(g.mp xid v ∗ □ swift.incW g γi γsg)) ∗
              swift.dfld dd go!"active" ↦ true ∗
              typedPointsto (swift.dfld dd go!"seq") true (DFrac.own (1 : Qp).half) ∗
              swift.dfld dd go!"stopChan" ↦ sc ∗ ghostMapElem x.γsh dd (DFrac.own 1) qsh ∗
              swift.descRaw (x.dc γ0 γc γm rp) (swift.RCh γ0 γc γm rp)
                (fun v => iprop(g.mp xid v ∗ □ swift.incW g γi γsg))
                xid g.ev.b sqv g.ev.fq szS g.ev.szF memS g.ev.memF γmc dd)))))
      $$ [desc seqD msgs seq Hloan Hr HFQ]
    · iframe Hdm1
      iintro %ex %old %t %Ψ HR Htok HΨ
      cases ex
      · -- a new entry (T2', T2, T4n/T4l/T4 or T3'): newDesc, cntL, the spawn
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases HR with %Hold
        wp_auto_lc 3
        iapply fupd_wp
        imod swift.descInv_allocIncL γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b)
            (swift.descGo x.γn g x.str) x.str (x.str xid, (null : Loc)) iL q $$ [Hloan Hlc1]
          with ⟨Hloan, %γi, Hγi, Hrj⟩
        · iframe HI Hloan Hlc1
        imod (ghostVar_alloc (GF := netDistGF) true) with ⟨%γsg, Hsg⟩
        imodintro
        ihave #HDctx2 := HDctx
        iunfold swift.descDSCtx at HDctx2
        icases HDctx2 with ⟨#HcntL, #HdPool, #Hsh, #HMax, ⟨%sqv, %szS, %memS, #HSQ, #HqS, %-⟩, -⟩
        wp_apply (wp_newDesc rp (fun v => iprop(g.mp xid v ∗ □ swift.incW g γi γsg))
            (swift.mpOk_ty x γ0 γc γm rp g Hmp xid _)
          (fun d sc wg => iprop(swift.stopMP g.γs γsg (x.str xid) d sc wg ∗ □ swift.incW g γi γsg))
          x.γsh xid g.ev.b x.dm x.γdl x.γn x.d sqv g.ev.fq szS g.ev.szF memS g.ev.memF q)
          $$ [HFQ] as %dd ⟨Hnew, HFQ⟩
        · iframe HqF HSQ HqS HMax HcntL Hsh HdPool Hctx0
          iexact HFQ
        ihave HFQ : typedPointsto (swift.fld rp go!"FQ") g.ev.fq (DFrac.own q) $$ [HFQ]
        · iexact HFQ
        iapply fupd_wp
        imod ghostVar_update (x.str xid, dd) γi _ $$ Hγi with Hγi
        imodintro
        ihave ⟨%s0, %γmc, %γsc, %m, %sc, %qsh, HmF, #Hmb, Ha, Hs, Hsc, #Hsb, Hshe, Hraw⟩ :=
          swift.descNew_split _ _ _ _ _ _ _ _ _ _ _ _ _ dd $$ Hnew
        ihave ⟨Hraw, #Hmx⟩ := swift.descRaw_mutex _ _ _ _ _ _ _ _ _ _ _ _ _ $$ Hraw
        wp_apply sync.Mutex.wp_Lock $$ [$HcntL] as ⟨Hclk, HC⟩
        iunfold swift.cntLInvR at HC
        icases HC with ⟨%n, %cnt, %T, Hn, Hcnt, HG⟩
        cases s0 <;> wp_auto
        · -- neither: by `routineCount >= MaxDescRoutines`
          wp_if_destruct
          · -- sequential: no goroutine (T3')
            wp_apply sync.Mutex.wp_Unlock $$ [$HcntL $Hclk Hn Hcnt HG]
            · iunfold swift.cntLInvR; iexists n, cnt, T; iframe
            ihave #HR : swift.descR x.γd (x.str xid)
                (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #dd) $$ []
            · iunfold swift.descR; iexists dd; isplitr
              · ipureintro; rfl
              iexact Hmx
            icases (typedPointsto_half_split _ _ _).1 $$ Hs with ⟨Hs1, Hs2⟩
            iapply HΨ $$ HR Htok
            iexists dd, m, sc, γi, γsg, γmc
            iframe desc msgs Hloan Hr HFQ Hmx
            isplitr
            · ipureintro; rfl
            iright
            iframe seqD
            iexists sqv, szS, memS, qsh
            iframe Hγi Hs1 Hs2 HmF Ha Hsc Hshe Hraw Hmb
          · -- a goroutine: its `cntL` slot (T4n), its loan (T4l), the spawn (T4, `goPre`)
            have hc : sint.Z cnt < sint.Z x.d := by omega
            iapply fupd_wp
            imod swift.descInv_loanRecAcc γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b)
                (swift.descGo x.γn g x.str) x.str iL j0 q (1 : Qp).half.half
                (swift.cntLGhost x.γn x.dm x.γdl x.d cnt T)
                iprop(∃ i, swift.cntLGhost x.γn x.dm x.γdl x.d (cnt + W64 1) (i :: T) ∗
                  swift.descSlot x.γn x.dm x.γdl i)
                (swift.cntLGhost_spawn_hup x.γn x.dm x.γdl x.d cnt T j0 (1 : Qp).half.half hc)
                $$ [Hlc2 Hloan Hr HG] with ⟨Hloan, Hr, %j, HG, Hslot⟩
            · iframe HI Hlc2 Hloan Hr HG
            imodintro
            wp_apply sync.Mutex.wp_Unlock $$ [$HcntL $Hclk Hn Hcnt HG]
            · iunfold swift.cntLInvR; iexists n, (cnt + W64 1), (j :: T); iframe
            iunfold swift.descSlot at Hslot
            icases Hslot with ⟨%hj0, Hel, Hrdj⟩
            icases (ghostMapElem_halves x.γn j false).1 $$ Hel with ⟨Helg, Hel⟩
            icases (swift.elem_quarters x.γn j false).1 $$ Hel with ⟨Hele, Helr⟩
            iapply fupd_wp
            imod swift.descInv_spawnLoanL γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b)
                (swift.descGo x.γn g x.str) x.str j _ (swift.epochLoan g.γq iL q)
                (swift.liveOk_loan g iL q) γi _ (1 : Qp).half.half $$ [Hlc3 Hloan Helr Hrj]
              with ⟨Hloan, %iL', %q', Hsh_, HX_, Hloan_, Hlr_, Hrj1, Hrj2⟩
            · iframe HI Hlc3 Hloan Helr Hrj
            imod swift.shInv_update x.γsh ⊤ (by simp) dd qsh q' $$ [Hshe] with Hshe
            · iframe Hsh Hshe
            imodintro
            icases (typedPointsto_half_split _ _ _).1 $$ HmF with ⟨HmF1, HmF2⟩
            icases (typedPointsto_half_split _ _ _).1 $$ Ha with ⟨Ha1, Ha2⟩
            icases (typedPointsto_half_split _ _ _).1 $$ Hs with ⟨Hs1, Hs2⟩
            icases (typedPointsto_half_split _ _ _).1 $$ Hs2 with ⟨Hs2, Hs3⟩
            icases (typedPointsto_half_split _ _ _).1 $$ Hsc with ⟨Hsc1, Hsc2⟩
            icases (ghostVar_split_half γi _ _).1 $$ Hγi with ⟨Hγi1, Hγi2⟩
            icases (ghostVar_split_half γi _ _).1 $$ Hγi1 with ⟨Hγi1, Hγi3⟩
            -- `goPre`'s reply channel object at the epoch (D54/D55 (1))
            ihave #HRCe : swift.RCh γ0 γc γm rp g.ev.rcp g.ev.bw $$ []
            · -- round 46 (D60, O1-b): `ownCtx` carries it
              iexact HoRC
            ihave #IH2 := IH
            iunfold swift.handleDescR at IH2
            ispecialize IH2 $$ %rp %g %dd %xid %γi %γsg
            wp_apply wp_fork $$ [HmF1 Ha1 Hs3 Hsc1 Hshe Hraw Hsh_ HX_ Hloan_ Hlr_ Helg Hrdj Hγi1 Hrj1]
            · iapply IH2 $$ [HmF1 Ha1 Hs3 Hsc1 Hshe Hraw Hsh_ HX_ Hloan_ Hlr_ Helg Hrdj Hγi1 Hrj1]
              · iframe Hpkg
                iunfold swift.goPre
                iframe Hctx0 HDctx HI HSI HO
                isplitr
                · ipureintro; exact Hmp
                iexists m, sc, γmc, γsc, sqv, szS, memS, j, iL', q'
                iframe HmF1 Ha1 Hs3 Hsc1 Hshe Hraw Hsh_ Hloan_ Hlr_ Helg Hrdj Hγi1 Hrj1 Hmb Hsb HRCe
                isplitl [HX_]
                · dsimp only [swift.RunX.epN]
                  iexact HX_
                ipureintro; exact hj0
              inext
              iintro -
              ipureintro; exact isPanic_intoVal ()
            ihave #HR : swift.descR x.γd (x.str xid)
                (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #dd) $$ []
            · iunfold swift.descR; iexists dd; isplitr
              · ipureintro; rfl
              iexact Hmx
            iapply HΨ $$ HR Htok
            iexists dd, m, sc, γi, γsg, γmc
            iframe desc msgs Hloan Hr HFQ Hmx
            isplitr
            · ipureintro; rfl
            ileft
            iframe seqD
            iexists j, γsc
            iframe Hγi2 Hγi3 Hrj2 Hs1 Hs2 Hele Ha2 HmF2 Hmb Hsb Hsc2
            iunfold swift.sgTok
            iexact Hsg
        · -- sequential: no goroutine (T3')
          wp_apply sync.Mutex.wp_Unlock $$ [$HcntL $Hclk Hn Hcnt HG]
          · iunfold swift.cntLInvR; iexists n, cnt, T; iframe
          ihave #HR : swift.descR x.γd (x.str xid)
              (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #dd) $$ []
          · iunfold swift.descR; iexists dd; isplitr
            · ipureintro; rfl
            iexact Hmx
          icases (typedPointsto_half_split _ _ _).1 $$ Hs with ⟨Hs1, Hs2⟩
          iapply HΨ $$ HR Htok
          iexists dd, m, sc, γi, γsg, γmc
          iframe desc msgs Hloan Hr HFQ Hmx
          isplitr
          · ipureintro; rfl
          iright
          iframe seqD
          iexists sqv, szS, memS, qsh
          iframe Hγi Hs1 Hs2 HmF Ha Hsc Hshe Hraw Hmb
      -- an existing entry (T5l, the loads, T5r): the lend with the loan token and `own iL j0`
      simp only [↓reduceIte]
      iunfold swift.descR at HR
      icases HR with ⟨%d0, %Hd0, #Hmx⟩
      subst Hd0
      wp_auto_lc 2
      iapply fupd_wp
      icases (swift.lrcpt_quarters g.γlj iL (j0, (1 : Qp).half.half)).1 $$ Hr with ⟨Hr1, Hr2⟩
      imod swift.descInv_lockLend γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b) x.str (x.str xid) _ t
          (.own iL j0) (swift.epochLoan g.γq iL q) (swift.liveOk_loan g iL q)
          $$ [Hloan Htok Hr2 Hlc1] with ⟨Hloan, %d', %y, %s, %m, %Hv, Hs4, Hm8, #Hbag, Hw⟩
      · rw [swift.lendRef_own]
        iframe HI Hlc1 Hloan Htok Hr2
      imodintro
      have hd : d0 = d' := swift.mkOk_desc_inj d0 d' Hv.1
      subst hd
      have hy : y = xid := hinj Hv.2.symm
      subst hy
      iapply wp_fupd
      wp_auto
      imod swift.descInv_lockReturn γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b) x.str (x.str y) _ t
          (.own iL j0) d0 s m (swift.epochLoan g.γq iL q) (swift.liveOk_loan g iL q) rfl
          $$ [Hloan Hw Hs4 Hm8 Hlc2] with ⟨Hloan, Htok, Href⟩
      · iframe HI Hlc2 Hloan Hw Hs4 Hm8
      rw [swift.lendRef_own]
      ihave Hr : ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) (j0, (1 : Qp).half.half) $$ [Hr1 Href]
      · iapply (swift.lrcpt_quarters g.γlj iL (j0, (1 : Qp).half.half)).2
        iframe Hr1
        iexact Href
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
      iexists d0, m, s
      iframe desc msgs seqD Hloan Hr HFQ
      isplitr
      · ipureintro; rfl
      -- round 46 (D60, O1-a): the cmap's `descR` carries it
      iexact Hmx
    -- the commit: both cases end in one state (`swift.commit_mono`), then one tail
    iintro %ex %old %res HQ
    iapply (swift.commit_mono (⊤ \ ↑github_com.orcaman.concurrent_map.cmapN)
      (fun M => github_com.orcaman.concurrent_map.cmapView g.γdc M)
      (fun M => github_com.orcaman.concurrent_map.cmapView g.γdc (<[x.str xid := res]> M))
      (fun M => M !! x.str xid = if ex then some old else none)
      iprop(∃ dd : Loc, ⌜res = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #dd⌝ ∗
          desc_ptr ↦ dd ∗ (∃ m : Loc, msgs_ptr ↦ m) ∗ (∃ s : Bool, seqD_ptr ↦ s) ∗
          swift.epochLoan g.γq iL q ∗
          ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) (j0, (1 : Qp).half.half) ∗
          typedPointsto (swift.fld rp go!"FQ") g.ev.fq (DFrac.own q) ∗
          sync.isMutex (swift.dfld dd go!"successorsL") (swift.succInv dd)))
    isplitl [HQ HlcC HlcD]
    rotate_left
    · iintro ⟨%dd, %Hres, Hdesc, ⟨%m, Hmsgs⟩, ⟨%s, HseqD⟩, Hloan, Hr, HFQ, #Hmx⟩
      wp_auto
      iapply HΦ
      iframe HeR
      isplitl [Hstat HFQ HrdR Hpin Hloan Hr Hcd Hback]
      · iunfold swift.shOwnR
        simp only [swift.dcK_rp, swift.dcK_γdl, swift.dcK_γxp, swift.dcK_N]
        iframe Hstat Hpin
        isplitl [HFQ]
        · iexists g.ev.fq, szF, memF
          iframe HqO
          isplitl [HFQ]
          · iexact HFQ
          ipureintro; exact HmO
        isplitl [HrdR]
        · iunfold swift.ownRdr; iexists dmR; iframe HdmR HrdR
        iapply Hback $$ Hloan Hr [Hcd]
        iexists dmX
        iunfold swift.descX
        iframe Hcd Hdm1
      iright
      iexact Hmx
    cases ex
    · -- a new entry: the entry and the incarnation committed with the view's insert (T4c, T3'c)
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases HQ with ⟨%dd, %m, %sc, %γi, %γsg, %γmc, %Hres, Hdesc, Hmsgs, Hloan, Hr, HFQ, #Hmx,
        Hcase⟩
      inext
      imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.descN)
        swift.descN_sub) $$ HI with ⟨Hi, Hclose⟩
      imod lc_fupd_elim_later (E := (⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ ↑swift.descN)
        $$ HlcC Hi with Hi
      iunfold swift.descInv at Hi
      icases Hi with ⟨%st, Hst2, Hrest⟩
      cases st
      rotate_left
      · simp only [↓reduceIte]
        iexfalso
        have hl := swift.liveOk_loan g iL q
        unfold swift.liveOk at hl
        iapply hl $$ [Hloan Hst2 Hrest]
        iframe
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hrest with ⟨%Mc, Hrest⟩
      icases Hrest with ⟨%q0, Hrest⟩
      icases Hrest with ⟨%L', Hrest⟩
      icases Hrest with ⟨%dm2, Hrest⟩
      icases Hrest with ⟨%W, Hview, HW, %HWd, Hents, HK, Hpool, Hrec, Hled, Hrca⟩
      imod (fupd_mask_subseteq (E1 := (⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ ↑swift.descN)
        (E2 := ∅) (by simp)) with Hback'
      imodintro
      iexists Mc
      try dsimp only
      iframe Hview
      iintro %Hk Hview
      imod Hback' with -
      subst Hres
      have hWk : W !! (x.str xid) = none := by
        cases h : W !! (x.str xid) with
        | none => rfl
        | some _ => exact absurd Hk (HWd _ (by rw [h]; simp))
      icases Hcase with (⟨HseqD, %j, %γsc, Hv, Hvq, Hrc, Hs2, Hs4, Hel, Ha, Hm, #Hmb, #Hsb, Hsg, Hsc⟩ |
        ⟨HseqD, %sqv, %szS, %memS, %qsh, Hv, Hs2, Hm, #Hmb, Ha, Hs, Hsc, Hsh, Hraw⟩)
      · -- a goroutine's entry (running, unsignalled; T4c)
        imod swift.descEnts_insertGo γ0 x.γd x.γn g (x.DR γ0 g.ev.b) x.str Mc (x.str xid) dd xid
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
        iexists dd
        iframe Hdesc Hloan Hr HFQ Hmx
        isplitr
        · ipureintro; rfl
        isplitl [Hmsgs]
        · iexists m; iexact Hmsgs
        iexists false; iexact HseqD
      · -- a sequential descriptor: its raw form into the inbox (T3'c)
        imod swift.descEnts_insertSeqI γ0 x.γd x.γn g x.str (x.DR γ0 g.ev.b) (x.dc γ0 γc γm rp)
            (swift.RCh γ0 γc γm rp) Hsr HsrA rfl Mc (x.str xid) dd xid γi γsg
            sqv g.ev.fq szS g.ev.szF memS g.ev.memF γmc m sc qsh Hk rfl _ swift.seqN_sub3 W hWk
          $$ [HlcD Hents HK Hv Hs2 Hm Ha Hs Hsc Hsh Hraw] with ⟨Hents, HK⟩
        · iframe HSI HlcD; iframe; iframe Hmb
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
        iexists dd
        iframe Hdesc Hloan Hr HFQ Hmx
        isplitr
        · ipureintro; rfl
        isplitl [Hmsgs]
        · iexists m; iexact Hmsgs
        iexists true; iexact HseqD
    -- an existing entry: the view unchanged
    simp only [↓reduceIte]
    icases HQ with ⟨%Hres, %dd, %m, %s, %Hold, Hdesc, Hmsgs, HseqD, Hloan, Hr, HFQ, #Hmx⟩
    subst Hres
    inext
    imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.descN)
      swift.descN_sub) $$ HI with ⟨Hi, Hclose⟩
    imod lc_fupd_elim_later (E := (⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ ↑swift.descN)
      $$ HlcC Hi with Hi
    iunfold swift.descInv at Hi
    icases Hi with ⟨%st, Hst2, Hrest⟩
    cases st
    rotate_left
    · simp only [↓reduceIte]
      iexfalso
      have hl := swift.liveOk_loan g iL q
      unfold swift.liveOk at hl
      iapply hl $$ [Hloan Hst2 Hrest]
      iframe
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hrest with ⟨%Mc, Hrest⟩
    icases Hrest with ⟨%q0, Hrest⟩
    icases Hrest with ⟨%L', Hrest⟩
    icases Hrest with ⟨%dm2, Hrest⟩
    icases Hrest with ⟨%W, Hview, Hrest⟩
    imod (fupd_mask_subseteq (E1 := (⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ ↑swift.descN)
      (E2 := ∅) (by simp)) with Hback'
    imodintro
    iexists Mc
    try dsimp only
    iframe Hview
    iintro %Hk Hview
    try simp only [↓reduceIte] at Hk
    rw [GMap.insert_id Mc _ _ Hk]
    imod Hback' with -
    imod Hclose $$ [Hst2 Hview Hrest] with -
    · inext
      iunfold swift.descInv
      iexists false
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hst2
      iexists Mc, q0, L', dm2, W
      iframe
    imodintro
    iexists dd
    iframe Hdesc Hloan Hr HFQ Hmx
    isplitr
    · ipureintro; exact Hold
    isplitl [Hmsgs]
    · iexists m; iexact Hmsgs
    iexists s; iexact HseqD
  · -- `delivered` has the key (T26): nil
    wp_auto
    iapply HΦ
    iframe HeR
    isplitl [Hstat HFQ HrdR Hpin Hloan Hr Hcd Hback]
    · iunfold swift.shOwnR
      simp only [swift.dcK_rp, swift.dcK_γdl, swift.dcK_γxp, swift.dcK_N]
      iframe Hstat Hpin
      isplitl [HFQ]
      · iexists fq, szF, memF
        iframe HqO
        isplitl [HFQ]
        · iexact HFQ
        ipureintro; exact HmO
      isplitl [HrdR]
      · iunfold swift.ownRdr; iexists dmR; iframe HdmR HrdR
      iapply Hback $$ Hloan Hr [Hcd]
      iexists dmX
      iunfold swift.descX
      iframe Hcd Hdm1
    ileft
    ipureintro; rfl

/-- **`depAll` under the bundle's hypothesis** (round O1): `wp_coreO` at every owner record. -/
theorem swift.depAll_of_coreO (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (wp_Str : swift.CommandId.String.specS x.str) (hinj : Function.Injective x.str)
    (wp_HasV : ∀ dm γdl, swift.cmapHasV.spec dm γdl)
    (wp_Upsert : github_com.orcaman.concurrent_map.ConcurrentMap.UpsertVL.spec (GF := netDistGF))
    (wp_newDesc : ∀ (rp : Loc) (MP : GoInterface → IProp netDistGF), swift.mpTy MP →
      swift.Replica.newDesc.specNc (x.dc γ0 γc γm rp) (swift.RCh γ0 γc γm rp) MP) :
    ⊢ □ ▷ swift.handleDescR γ0 γc γm x (swift.RCh γ0 γc γm) -∗ swift.depAll γ0 γc γm x := by
  iintro #IH
  iunfold swift.depAll
  imodintro
  iintro %rp %g %k
  iapply (swift.Replica.getCmdDescWith.wp_coreO γ0 γc γm x wp_Str hinj wp_HasV wp_Upsert wp_newDesc
    rp g k)
  iexact IH

end proof

end Perennial.github_com.imdea_software.swiftpaxos
