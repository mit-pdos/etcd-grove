/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SeqSpecProof.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The run loop's inline `handleMsg` on a sequential descriptor, `seqSpecD`, end to end, top-down**
(round 43, sv-swb; D52 (2); table §3R11 T7s.l/T7s.o/T7s.u, the cases at the inline record `cI`,
T7e/T7r; plan R11.4 (4) 6).

`seqSpecD`'s program is the one call `r.handleMsg(m, desc, cmdId)`; everything around it is ghost:
* `swift.seq_open` (round Q2: proved from SeqOpen.lean's steps): T7s.l (an inline loan from the sub-pool), T7s.o (`g.so` opened by `gO_so`:
  raw, parked tokenless or parked with its token in the store), T7s.u (unpark at the loan's `q`:
  `descOwnFP_sh`, `shOwnR` with the loan's pin, D51 (c)); it returns the owner state at
  `cI = x.dcK … g (.seq γi)` and the closing wand for T7e (park, `descInv_returnLoanO`) / T7r
  (retired: the loan back, `γS` element to the store).
* `swift.Replica.handleMsg.specS`: `handleMsg` at `cI` from the case specs (`wp_proofS`), the slot
  case by `slotSpecS` with `descOwnF_slotS` (TD).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleDescProofDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ReplyDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SeqOpen

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

/-- **`r.handleMsg(m, desc, cmdId)` by the inline owner** at `cI = x.dcK … g (.seq γi)`: the owner
state back, or retired (the slot case: `descDone`). -/
abbrev swift.Replica.handleMsg.specS (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (RC : Loc → Loc → w32 → IProp netDistGF) : Prop :=
  ∀ (rp : Loc) (g : swift.DescG) (γi γsg : GName) (γmc : ChanNames) (d : Loc)
    (y : swift.CommandId) (m : GoInterface),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.ownCtx γ0 γc γm x rp g ∗
      (x.dcK γ0 γc γm rp g (.seq γi)).ctx ∗ □ swift.proposeCtx (x.dcK γ0 γc γm rp g (.seq γi)) ∗
      swift.depSpecR (x.dcK γ0 γc γm rp g (.seq γi)) ∗
      swift.descOwnF (x.dcK γ0 γc γm rp g (.seq γi)) (RC rp) (swift.MPi g y γi γsg) γmc d y g.ev.b
        iprop(swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
          (x.dcK γ0 γc γm rp g (.seq γi)).kf d y) ∗
      swift.MPi g y γi γsg m }}
    (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleMsg"))
      (Val #m)) (Val #d)) (Val #y))
  {{ (v : Bool), RET #v;
      swift.descOwnF (x.dcK γ0 γc γm rp g (.seq γi)) (RC rp) (swift.MPi g y γi γsg) γmc d y g.ev.b
          iprop(swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
            (x.dcK γ0 γc γm rp g (.seq γi)).kf d y) ∨
      swift.descDone (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d }}

end specs

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

/-- **T7s.l/T7s.o/T7s.u and, as the closing wand, T7e/T7r** (see the file header; round Q2:
proved from SeqOpen.lean's steps). R's `cntFrozen` half is split ¼ (the loan's record), ⅛ (the
inline record's free slot), ⅛ (kept in the closing wand). `g.so` is opened at `gO`'s first stage
(`gO_facts`): raw (`seq_raw`, which lends first), or parked (`seq_unparkO`: the loan, then free or
token out). The closing wand parks (`seq_park`) or takes the retirement (`descGone`), returns the
loan (`seq_return`) and refolds `descDSB`. Round Q2 (D59 (2), 45-a): takes `wp_slotS` and
`isPkgInit`, for the inline record's slot capability (`slotCap_ofS`). -/
theorem swift.seq_open (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (wp_slotS : swift.Replica.handleMsg.slotSpecS γ0 γc γm x) (rp : Loc) (g : swift.DescG)
    (ev : swift.EpV) (γp : GName) (i : Nat) (d : Loc) (y : swift.CommandId) (bw : w32) (qb : Qp) :
    isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      (x.dc γ0 γc γm rp).ctx ∗ swift.ownCtx γ0 γc γm x rp g ∗ swift.depAll γ0 γc γm x ∗
      swift.descDSB γ0 γc γm x rp g ev γp i ∗ swift.runReader rp x.γdl ∗
      typedPointsto (swift.fld rp go!"ballot") bw (DFrac.own qb) ∗ g.so d y ∗
      £ 1 ∗ £ 1 ∗ £ 1 ∗ £ 1 ⊢
    |={⊤}=> ∃ (γi γsg : GName) (γmc : ChanNames),
      (x.dcK γ0 γc γm rp g (.seq γi)).ctx ∗ □ swift.proposeCtx (x.dcK γ0 γc γm rp g (.seq γi)) ∗
      swift.depSpecR (x.dcK γ0 γc γm rp g (.seq γi)) ∗
      swift.descOwnF (x.dcK γ0 γc γm rp g (.seq γi)) (swift.RCh γ0 γc γm rp) (swift.MPi g y γi γsg) γmc d y
        g.ev.b iprop(swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
          (x.dcK γ0 γc γm rp g (.seq γi)).kf d y) ∗
      (∀ m : GoInterface, g.mp y m -∗ swift.MPi g y γi γsg m) ∗
      ((swift.descOwnF (x.dcK γ0 γc γm rp g (.seq γi)) (swift.RCh γ0 γc γm rp) (swift.MPi g y γi γsg) γmc d y
          g.ev.b iprop(swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
            (x.dcK γ0 γc γm rp g (.seq γi)).kf d y) ∨
        swift.descDone (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d) ={⊤}=∗
        swift.descDSB γ0 γc γm x rp g ev γp i ∗ swift.runReader rp x.γdl ∗
        typedPointsto (swift.fld rp go!"ballot") bw (DFrac.own qb) ∗
        (g.so d y ∨ ghostMapElem g.γS d (DFrac.own 1) y)) := by
  iintro ⟨#Hpkg, #Hctx, #HoC, #Hdep, HDSB, Hrdr, Hbal, Hso, Hlc1, Hlc2, Hlc3, -⟩
  ihave ⟨#HI, #HSI, Hst, Hfz, %Hgo, Hback⟩ := swift.descDSB_take γ0 γc γm x rp g ev γp i $$ HDSB
  obtain ⟨g00, hg⟩ := Hgo
  obtain ⟨g0, hso, hsr, hd, hev, hmp, hk, hev0, hmp0, hk0⟩ :=
    swift.gO_facts γ0 γc γm x rp g g00 hg
  icases (swift.frozen_parts x.γn 0 false).1 $$ Hfz with ⟨Hn1, Hn2, Hn3⟩
  ihave Hso : swift.soO γ0 γc γm x rp (swift.RCh γ0 γc γm rp) g0 d y $$ [Hso]
  · rw [← hso]; iexact Hso
  iunfold swift.soO at Hso
  ihave Hown : |={⊤}=> ghostVar g.γst (1 : Qp).half false ∗ ∃ (γi γsg : GName) (γmc : ChanNames),
      □ swift.incW g γi γsg ∗
      swift.descOwnF (x.dcK γ0 γc γm rp g (.seq γi)) (swift.RCh γ0 γc γm rp) (swift.MPi g y γi γsg) γmc d y
        g.ev.b iprop(swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
          (x.dcK γ0 γc γm rp g (.seq γi)).kf d y) $$ [Hso Hlc1 Hst Hn1 Hrdr Hn2]
  · icases Hso with (Hraw | HO)
    · iapply swift.seq_raw γ0 γc γm x wp_slotS rp g g00 hev0 hmp0 hk0 d y
      iframe Hpkg HoC Hctx Hdep HI HSI Hlc1 Hst Hn1 Hrdr Hn2
      rw [← hsr]; iexact Hraw
    · iapply swift.seq_unparkO γ0 γc γm x rp g g0 hd hev hmp hk d y
      isplitr
      · iexact HoC
      isplitr
      · iexact Hctx
      isplitr
      · iexact HI
      isplitr
      · iexact HSI
      iframe Hlc1 Hst Hn1 Hrdr Hn2
      iexact HO
  imod Hown with ⟨Hst, %γi, %γsg, %γmc, #Hw, Hown⟩
  ihave #HoC2 := HoC
  iunfold swift.ownCtx at HoC2
  icases HoC2 with ⟨-, #HpB, -, -, -, #Hcg⟩
  imodintro
  iexists γi, γsg, γmc
  isplitr
  · iExactEq Hctx; rfl
  isplitr
  · imodintro
    iapply swift.proposeCtx_ofB
    isplitr
    · iExactEq HpB; rfl
    iapply swift.takeLaw_dcK
    iExactEq Hctx; rfl
  isplitr
  · iunfold swift.depAll at Hdep
    iapply Hdep
  iframe Hown
  isplitr
  · iintro %m Hm
    isplitl [Hm]
    · iexact Hm
    iexact Hw
  iintro Hres
  imod swift.seq_close γ0 γc γm x rp g g0 hso hd hev hmp hk γi γsg γmc d y
      $$ [Hlc2 Hlc3 Hn3 Hres] with ⟨Hfz, Hrdr, Hso⟩
  · iframe Hctx Hw Hcg Hlc2 Hlc3 Hn3 Hres
  imodintro
  ihave HDSB := Hback $$ Hst Hfz
  iframe HDSB Hrdr Hbal Hso

/-- **The owner state opened for the slot case by the inline owner** (`slotSpecS`'s pre), with the
wand that rebuilds `descGone`'s epoch part from the loan environment `slotSpecS` returns. -/
theorem swift.descOwnF_slotS (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (RC : Loc → w32 → IProp netDistGF) (g : swift.DescG) (γi γsg : GName) (γmc : ChanNames)
    (d : Loc) (y : swift.CommandId) :
    swift.descOwnF (x.dcK γ0 γc γm rp g (.seq γi)) RC (swift.MPi g y γi γsg) γmc d y g.ev.b
        iprop(swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
          (x.dcK γ0 γc γm rp g (.seq γi)).kf d y) ⊢
      ∃ (dv : swift.DescV) (rv : swift.RowV) (q : Qp) (sl fa cf : Loc) (cond : GoFunc)
        (fs : List GoFunc) (v : Bool),
        ⌜dv.seq = true⌝ ∗ swift.descF d γmc (swift.MPi g y γi γsg) dv ∗
        swift.rowTokO (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y dv rv ∗
        ghostMapElem x.γsh d (DFrac.own (1 : Qp).half) q ∗
        swift.dfld d go!"slowPathH" ↦ sl ∗ swift.dfld d go!"fastPathH" ↦ fa ∗
        swift.msetF sl ∗ swift.msetF fa ∗ swift.ocfRes d cf cond fs v ∗
        swift.descCore (x.dcK γ0 γc γm rp g (.seq γi)) d y g.ev.b ∗
        swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
        (x.dcK γ0 γc γm rp g (.seq γi)).kf d y ∗ (x.dcK γ0 γc γm rp g (.seq γi)).env d q ∗
        ((x.dcK γ0 γc γm rp g (.seq γi)).env d q -∗
          ∃ (q' : Qp) (bw : w32) (stp rcp : Loc),
            swift.epochRd x.γe x.γxe rp x.rr q' g.ev.b bw stp rcp ∗
            swift.shOwnR (x.dcK γ0 γc γm rp g (.seq γi)) d g.ev.b q') := by
  iintro H
  iunfold swift.descOwnF at H
  icases H with ⟨Ho, Hocf⟩
  iunfold swift.descOwn at Ho
  icases Ho with ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, -, -, HdS, HR⟩
  iunfold swift.setR at HR
  iunfold swift.descSt at HR
  icases HR with ⟨%q, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, -, Hd, Htok, -, -, -, -, -, %Hrp, -,
    ⟨HsF, HfF, HdF, Hcore, Hrest, Hkf⟩⟩
  iunfold swift.shOwn at Hsh
  icases Hsh with ⟨Hshe, HshR⟩
  iunfold swift.descOcf at Hocf
  icases Hocf with ⟨%cf, %cond, %fs, %v, Hocf, -, -, -⟩
  ihave Hms := swift.msetF_of _ _ _ _ _ _ _ _ $$ HdS
  ihave Hmf : swift.msetF f $$ [HdF]
  · iapply swift.msetF_of; iExactEq HdF; rfl
  iunfold swift.shOwnR at HshR
  icases HshR with ⟨Hst, HFQ, Hrdr, Henv, Hpin⟩
  ihave Hshe : ghostMapElem x.γsh d (DFrac.own (1 : Qp).half) q $$ [Hshe]
  · iExactEq Hshe; rfl
  iexists dv, rv, q, s, f, cf, cond, fs, v
  iframe Hd Htok Hshe HsF HfF Hms Hmf Hocf Hcore Hrest Hkf Henv
  isplitr
  · ipureintro; exact Hrp.2
  iintro Henv
  iexists q, bw, stp, rcp
  isplitl [Hrd]
  · iExactEq Hrd; rfl
  iunfold swift.shOwnR
  iframe

end lemmas

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

/-- **`handleMsg.specS`** from the case specs (as `wp_proofG`; the slot case by `slotSpecS`). -/
theorem swift.Replica.handleMsg.wp_proofS (γ0 : sp.Names) (γc γm : GName) (xs : swift.RunX)
    (RC : Loc → Loc → w32 → IProp netDistGF)
    (wp_ack : ∀ MP, swift.mpTy MP → ∀ c : swift.DC, c.str = xs.str → c.γ = γ0 → c.γc = γc → c.γm = γm →
      swift.Replica.handleMsg.ackSpecIc (RC c.rp) MP swift.ackCtx c)
    (wp_prop : ∀ MP, swift.mpTy MP → ∀ c : swift.DC, c.str = xs.str → c.γ = γ0 → c.γc = γc → c.γm = γm →
      swift.Replica.handleMsg.propSpecIc (RC c.rp) MP swift.proposeCtx c)
    (wp_sync : ∀ MP, swift.mpTy MP → ∀ c : swift.DC, c.str = xs.str → c.γ = γ0 → c.γc = γc → c.γm = γm →
      swift.Replica.handleMsg.syncSpecIc (RC c.rp) MP c)
    (wp_slot : swift.Replica.handleMsg.slotSpecS γ0 γc γm xs) :
    swift.Replica.handleMsg.specS γ0 γc γm xs RC := by
  intro rp g γi γsg γmc d y m
  iintro %Φ ⟨#Hpkg, #HoC, #Hc, #Hpc, #Hdr, Hown, ⟨Hm, #Hw⟩⟩ HΦ
  ihave #HoC2 := HoC
  iunfold swift.ownCtx at HoC2
  icases HoC2 with ⟨-, -, -, -, %Hpure, -⟩
  have Hmp := Hpure.1
  have hrp : (xs.dcK γ0 γc γm rp g (.seq γi)).rp = rp := rfl
  ihave Hm := swift.mp_dcK xs γ0 γc γm rp g (.seq γi) y m Hmp $$ Hm
  iunfold swift.descMP at Hm
  icases Hm with (#Ha | ⟨%pm, %gp, %cc, %dep, %hs, %sq, %ld, %s, %B, %D, %P, %H, %Hpm, Hpr, Hcl⟩ | #Hs | Hse)
  · -- an ack or a string
    ihave #Hpc2 := Hpc
    iunfold swift.proposeCtx at Hpc2
    icases Hpc2 with ⟨#Hack, -⟩
    have h := wp_ack (swift.MPi g y γi γsg) (swift.mpOk_ty xs γ0 γc γm rp g Hmp y _) (xs.dcK γ0 γc γm rp g (.seq γi)) rfl rfl rfl rfl γmc d y g.ev.b
      iprop(swift.descRest (xs.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
        (xs.dcK γ0 γc γm rp g (.seq γi)).kf d y) m
    rw [hrp] at h
    iapply h $$ [Hown]
    · iframe Hpkg Hc Hack Hown Ha
    inext
    iintro Hres
    iapply HΦ; iexact Hres
  · -- a proposal
    subst Hpm
    have h := wp_prop (swift.MPi g y γi γsg) (swift.mpOk_ty xs γ0 γc γm rp g Hmp y _) (xs.dcK γ0 γc γm rp g (.seq γi)) rfl rfl rfl rfl γmc d y g.ev.b
      ((xs.dcK γ0 γc γm rp g (.seq γi)).kf d y) pm gp cc dep hs sq ld s B D P H
    rw [hrp] at h
    iapply h $$ [Hown Hpr Hcl]
    · iframe Hpkg Hc Hpc Hown Hpr Hcl
    inext
    iintro Hres
    iapply HΦ; iexact Hres
  · -- a history slot (T16aI, T16c)
    ihave #Hs2 := Hs
    iunfold swift.slotMP at Hs
    icases Hs with ⟨%s, ⟨%Hm, %Hin⟩, #Hex⟩
    subst Hm
    ihave ⟨%dv, %rv, %q, %sl, %fa, %cf, %cond, %fs, %v, %Hsq, Hd, Htok, Hshe, HsF, HfF,
      Hms, Hmf, Hocf, Hcore, Hrest, Hkf, Henv, Hgb⟩ :=
      swift.descOwnF_slotS γ0 γc γm xs rp (RC rp) g γi γsg γmc d y $$ Hown
    ihave HmS : swift.MPi g y γi γsg (interface.mkOk go.int #s) $$ []
    · isplitr
      · iapply swift.mp_of_slot xs γ0 γc γm rp g y _ Hmp $$ Hs2
      · iexact Hw
    iapply (wp_slot rp g γi γsg γmc d y dv rv s q sl fa cf cond fs v)
      $$ [HmS Hd Htok Hshe HsF HfF Hms Hmf Hocf Hcore Hrest Hkf Henv]
    · iframe Hpkg Hc HmS Hex Hd Htok Hshe HsF HfF Hms Hmf Hocf Hcore Hrest Hkf Henv
      ipureintro; exact Hsq
    inext
    iintro ⟨Hret, Henv⟩
    ihave Hg := Hgb $$ Henv
    iapply HΦ
    iright
    iunfold swift.descDone
    iunfold swift.descGone
    isplitr
    · ipureintro; rfl
    isplitr
    · iExactEq Hex; rfl
    iframe Hret
    iExactEq Hg; rfl
  · -- a sync entry (T24)
    ihave Hse : swift.syncMP (xs.dcK γ0 γc γm rp g (.seq γi)).γ (xs.dcK γ0 γc γm rp g (.seq γi)).γcl
        (xs.dcK γ0 γc γm rp g (.seq γi)).r
        (sp.leaderOf (xs.dcK γ0 γc γm rp g (.seq γi)).N g.ev.b) g.ev.b y m $$ [Hse]
    · iExactEq Hse; rfl
    have h := wp_sync (swift.MPi g y γi γsg) (swift.mpOk_ty xs γ0 γc γm rp g Hmp y _) (xs.dcK γ0 γc γm rp g (.seq γi)) rfl rfl rfl rfl γmc d y g.ev.b
      ((xs.dcK γ0 γc γm rp g (.seq γi)).kf d y) m
    rw [hrp] at h
    iapply h $$ [Hown Hse]
    · iframe Hpkg Hc Hpc Hdr Hown Hse
    inext
    iintro Hres
    iapply HΦ; iexact Hres

/-- **`seqSpecD`** from `handleMsg.specS` (see the file header). -/
theorem swift.Replica.handleMsg.seqSpecD.wp_proofT (γ0 : sp.Names) (γc γm : GName) (xs : swift.RunX)
    (wp_hmS : swift.Replica.handleMsg.specS γ0 γc γm xs (swift.RCh γ0 γc γm))
    (wp_slotS : swift.Replica.handleMsg.slotSpecS γ0 γc γm xs)
    (hdep : ⊢ swift.depAll γ0 γc γm xs) :
    swift.Replica.handleMsg.seqSpecD γ0 γc γm xs := by
  intro rp g ev γp i d y m bw qb
  iintro %Φ ⟨#Hpkg, #Hctx, #HoC, HDSB, Hrdr, Hbal, Hso, Hm, Hlc1, Hlc2, Hlc3, Hlc4⟩ HΦ
  ihave #Hdep := hdep
  iapply fupd_wp
  imod swift.seq_open γ0 γc γm xs wp_slotS rp g ev γp i d y bw qb
      $$ [HDSB Hrdr Hbal Hso Hlc1 Hlc2 Hlc3 Hlc4]
    with ⟨%γi, %γsg, %γmc, #Hc, #Hpc, #Hdr, Hown, Hmw, Hclose⟩
  · iframe Hpkg Hctx HoC Hdep HDSB Hrdr Hbal Hso Hlc1 Hlc2 Hlc3 Hlc4
  ihave Hm := Hmw $$ Hm
  imodintro
  iapply wp_fupd
  iapply (wp_hmS rp g γi γsg γmc d y m) $$ [Hown Hm]
  · iframe Hpkg HoC Hc Hpc Hdr Hown Hm
  inext
  iintro %v Hres
  imod Hclose $$ Hres with ⟨HDSB, Hrdr, Hbal, Hso⟩
  imodintro
  iapply HΦ
  iframe

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
