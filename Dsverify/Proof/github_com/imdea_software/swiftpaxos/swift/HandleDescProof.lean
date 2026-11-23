/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HandleDescProof.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**`go r.handleDesc(desc, cmdId)` end to end, top-down** (round 43, sv-swb; D52 (2): every Go statement
with a wp step, every missing callee and ghost step a named `sorry -- TD: …`; table §3R11 T8,
T9-T17, T19a-T19x; plan R11.4 (4) 5 with `hdInv`, HdInv.lean).

* `swift.Replica.handleMsg.specG`: `handleMsg` by a goroutine on a message of its bag (`MPi`): the
  owner state back (`false`), or the slot case's tail `tailG` (`true`). Its proof is the dispatch over
  the case specs (`ackSpecI`, `propSpecI`, `syncSpecI`, `slotSpecG`): TD.
* The step lemmas `swift.hd_open` (the loop's fields, and the stop arm's capability `hdStopW`),
  `swift.hd_stopRaw`/`swift.hd_stopOwn` (T19a.g-T19x by form) and `swift.hd_toOwn` (T8): proved
  (round 44). `depAll` (`depSpecR` at the owner records) comes from the Löb bundle (DescBundle.lean).
* `swift.Replica.handleDesc.wp_proofT`: `handleDesc.specD` from `handleMsg.specG`, `drainStops.specT`
  and `freeDesc.specI`, over the loop invariant `goPreP ∗ hdInv ∗ £ 2`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HdInv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DrainStopsDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescInit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleDescProofDefs

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

end specs

section stopDefs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

end stopDefs

section specsD
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

end specsD

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

end lemmas

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

set_option goose.wp.extras true

theorem swift.Replica.handleDesc.wp_proofT (γ0 : sp.Names) (γc γm : GName) (xs : swift.RunX)
    (RC : Loc → Loc → w32 → IProp netDistGF)
    (wp_hm : swift.Replica.handleMsg.specG γ0 γc γm xs RC)
    (wp_drain : swift.Replica.drainStops.specT)
    (wp_freeDesc : swift.Replica.freeDesc.specI (swift.descDFA xs.γsh)) :
    swift.Replica.handleDesc.specDD γ0 γc γm xs RC := by
  intro rp g d y γi γsg
  wp_start as ⟨Hpre, #Hdep⟩
  ihave ⟨#HP, Hinv⟩ := swift.hdInv_init γ0 γc γm xs rp (RC rp) g d y γi γsg $$ Hpre
  wp_auto_lc 2
  ihave HL : (∃ _u : Unit, "Hinv" ∷ swift.hdInv γ0 γc γm xs rp (RC rp) g d y γi γsg ∗
      "Hlc1" ∷ £ 1 ∗ "Hlc2" ∷ £ 1 : IProp netDistGF) $$ [Hinv Hlc1 Hlc2]
  · iexists (); iframe
  wp_for HL
  ihave ⟨%sc, %m, %γsc, %γmc, %γsg', %W, Ha, Hsc, Hm, #Hbm, #Hbs, Hback⟩ :=
    swift.hd_open γ0 γc γm xs rp (RC rp) g d y γi γsg $$ [Hinv]
  · iframe HP Hinv
  ihave #HP2 := HP
  iunfold swift.goPreP at HP2
  icases HP2 with ⟨#Hctx, #Hdsc, #Hown, #HI, %Hmp⟩
  ihave #Hdsc2 := Hdsc
  iunfold swift.descDSCtx at Hdsc2
  icases Hdsc2 with ⟨#HcntL, #Hpool, #Hsh, #HMax, #HSQ, #Hdel⟩
  ihave #HpoolF : swift.descPoolCtxF (swift.descDFA xs.γsh) rp $$ []
  · iunfold swift.descPoolCtxF
    iexists (swift.descDFA xs.γsh)
    iframe Hpool
    imodintro
    iintro %d' H
    imodintro; iexact H
  wp_auto
  isimp only [decide_true, ↓reduceIte]
  wp_auto
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- T19: a stop request
    iapply swift.bag_clauseT $$ Hlc1 Hlc2 Hbs
    inext
    iintro %wg ⟨Hreq, #HW⟩
    icases Hback with ⟨-, Hstop⟩
    iunfold swift.hdStopW at Hstop
    wp_auto_lc 4
    iapply fupd_wp
    imod Hstop $$ %wg Hlc1 Hreq HW Ha with ⟨Ha, Htok, Hdone, Hel, Hfin⟩
    imodintro
    try wp_auto
    -- P6: the queued messages are dropped
    ihave #Hch := is_bag_is_chan γmc m _ $$ Hbm
    ihave HL2 : (∃ _u : Unit, "Hm" ∷ typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half) :
        IProp netDistGF) $$ [Hm]
    · iexists (); iframe
    wp_for HL2
    wp_func_call
    wp_call
    wp_apply (wp_Len (V := GoInterface) (t := go.InterfaceType []) m γmc) $$ [$Hch] as %l %Hl
    wp_if_destruct
    · wp_apply (wp_bag_receive (t := go.InterfaceType []) γmc m _) $$ [$Hbm] as %v' ⟨-, -⟩
      try wp_auto
      wp_for_post
      iframe
      iexists (); iframe
    rw [if_pos (by cases hd : decide (l = W64 0) <;> simp_all)]
    try wp_auto
    wp_apply (wp_drain rp d sc γsc g.γs γsg' (xs.str y) (1 : Qp).half) $$ [Hsc Htok] as Hsc
    · iframe Hsc
      isplitr
      · iunfold swift.stopBag; iexists W; iframe Hbs HW
      ileft; iexact Htok
    iapply fupd_wp
    imod Hfin $$ Hlc2 Hlc3 Hlc4 Ha Hsc Hm Hel with ⟨Hel, %j, Hnj, Hrdj⟩
    imodintro
    wp_apply sync.Mutex.wp_Lock $$ [$HcntL] as ⟨Hlk, HC⟩
    iunfold swift.cntLInvR at HC
    icases HC with ⟨%n, %c, %T, Hsn, Hrc, HG⟩
    try wp_auto
    ihave ⟨HG, Hnj, %Hj0⟩ := swift.cntLGhost_ne0 xs.γn xs.dm xs.γdl xs.d c T j $$ [HG Hnj]
    · iframe
    ihave Hslot : swift.descSlot xs.γn xs.dm xs.γdl j $$ [Hnj Hrdj]
    · iunfold swift.descSlot
      iframe
      ipureintro; exact Hj0
    iapply fupd_wp
    imod swift.cntLGhost_exit xs.γn xs.dm xs.γdl xs.d c T j $$ [HG Hslot] with ⟨%Hc1, HG⟩
    · iframe
    imodintro
    wp_apply sync.Mutex.wp_Unlock $$ [$HcntL $Hlk Hsn Hrc HG]
    · iunfold swift.cntLInvR; iexists n, (c - W64 1), (T.erase j); iframe
    try wp_auto
    wp_apply (sync.join.WaitGroup.wp_Done (ghostMapElem g.γs (xs.str y) (DFrac.own 1) true) wg)
      $$ [Hdone Hel]
    · iframe
    try wp_auto
    wp_for_post
    iapply HΦ; itrivial
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a message
    iapply swift.bag_clauseT $$ Hlc1 Hlc2 Hbm
    inext
    iintro %v Hv
    wp_auto_lc 2
    icases Hback with ⟨Hback, -⟩
    ihave Hinv := Hback $$ Ha Hsc Hm
    iapply fupd_wp
    imod swift.hd_toOwn γ0 γc γm xs rp (RC rp) g d y γi γsg v $$ [HP Hinv Hv]
      with ⟨Hv, %j, %iL, %γmc', #Hc, #Hpc, #Hdr, Hown⟩
    · iframe HP Hdep Hinv Hv
    imodintro
    wp_apply (wp_hm rp g j iL γi γsg γmc' d y v) $$ [Hown Hv] as %b Hres
    · iframe HP Hc Hpc Hdr Hown Hv
    icases Hres with (⟨%Hb, Hown⟩ | ⟨%Hb, Htail⟩)
    · subst Hb
      try wp_auto
      wp_for_post
      iframe
      iexists ()
      iframe Hlc1 Hlc2
      iunfold swift.hdInv; iright
      iexists j, iL, γmc'
      iframe Hc Hpc Hdr
      iExactEq Hown; rfl
    · subst Hb
      try wp_auto
      iunfold swift.tailG at Htail
      icases Htail with ⟨%m', %sl, %fa, %sc', %γsc', %γsg'', Hmsgs, HsF, HfF, Hms, Hmf, HDF, Hsc', #HsB',
        Htok'⟩
      wp_apply (wp_drain rp d sc' γsc' g.γs γsg'' (xs.str y) (1 : Qp)) $$ [Hsc' HsB' Htok'] as Hsc'
      · iframe Hsc' HsB' Htok'
      try wp_auto
      wp_apply (wp_freeDesc rp d) $$ [Hmsgs HsF HfF Hms Hmf HDF Hsc']
      · iframe HpoolF
        iunfold swift.descPooled
        iexists m', sc', sl, fa
        iframe
      try wp_auto
      wp_for_post
      iapply HΦ; itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

/-- **`handleMsg.specG`** from the case specs (`handleMsg`'s own specs per message kind): the
message's predicate is `descMP` (`mpOk`); a retirement (`descDone`) is refuted at the goroutine
record (`c.sq = false`). -/
theorem swift.Replica.handleMsg.wp_proofG (γ0 : sp.Names) (γc γm : GName) (xs : swift.RunX)
    (RC : Loc → Loc → w32 → IProp netDistGF)
    (wp_ack : ∀ MP, swift.mpTy MP → ∀ c : swift.DC, c.str = xs.str → c.γ = γ0 → c.γc = γc → c.γm = γm →
      swift.Replica.handleMsg.ackSpecIc (RC c.rp) MP swift.ackCtx c)
    (wp_prop : ∀ MP, swift.mpTy MP → ∀ c : swift.DC, c.str = xs.str → c.γ = γ0 → c.γc = γc → c.γm = γm →
      swift.Replica.handleMsg.propSpecIc (RC c.rp) MP swift.proposeCtx c)
    (wp_sync : ∀ MP, swift.mpTy MP → ∀ c : swift.DC, c.str = xs.str → c.γ = γ0 → c.γc = γc → c.γm = γm →
      swift.Replica.handleMsg.syncSpecIc (RC c.rp) MP c)
    (wp_slot : swift.Replica.handleMsg.slotSpecG γ0 γc γm xs) :
    swift.Replica.handleMsg.specG γ0 γc γm xs RC := by
  intro rp g j iL γi γsg γmc d y m
  iintro %Φ ⟨#Hpkg, #HP, #Hc, #Hpc, #Hdr, Hown, ⟨Hm, #Hw⟩⟩ HΦ
  ihave #HP2 := HP
  iunfold swift.goPreP at HP2
  icases HP2 with ⟨-, -, -, -, %Hmp⟩
  have hrp : (xs.dcK γ0 γc γm rp g (.go j iL γi)).rp = rp := rfl
  ihave Hm := swift.mp_dcK xs γ0 γc γm rp g (.go j iL γi) y m Hmp $$ Hm
  iunfold swift.descMP at Hm
  icases Hm with (#Ha | ⟨%pm, %gp, %cc, %dep, %hs, %sq, %ld, %s, %B, %D, %P, %H, %Hpm, Hpr, Hcl⟩ | #Hs | Hse)
  · -- an ack or a string
    ihave #Hpc2 := Hpc
    iunfold swift.proposeCtx at Hpc2
    icases Hpc2 with ⟨#Hack, -⟩
    have h := wp_ack (swift.MPi g y γi γsg) (swift.mpOk_ty xs γ0 γc γm rp g Hmp y _) (xs.dcK γ0 γc γm rp g (.go j iL γi)) rfl rfl rfl rfl γmc d y g.ev.b
      iprop(swift.descRest (xs.dcK γ0 γc γm rp g (.go j iL γi)) g.ev.b y d ∗ (xs.dcK γ0 γc γm rp g (.go j iL γi)).kf d y) m
    rw [hrp] at h
    iapply h $$ [Hown]
    · iframe Hpkg Hc Hack Hown Ha
    inext
    iintro Hres
    iapply HΦ
    icases Hres with (Hown | Hdone)
    · ileft; iframe Hown; ipureintro; rfl
    · iexfalso; iunfold swift.descDone at Hdone; iunfold swift.descGone at Hdone
      icases Hdone with ⟨%Hsq, -⟩; cases Hsq
  · -- a proposal
    subst Hpm
    ihave Hown : swift.descOwnF (xs.dcK γ0 γc γm rp g (.go j iL γi)) (RC rp) (swift.MPi g y γi γsg) γmc d y
        g.ev.b iprop(swift.descRest (xs.dcK γ0 γc γm rp g (.go j iL γi)) g.ev.b y d ∗
          (xs.dcK γ0 γc γm rp g (.go j iL γi)).kf d y) $$ [Hown]
    · iexact Hown
    have h := wp_prop (swift.MPi g y γi γsg) (swift.mpOk_ty xs γ0 γc γm rp g Hmp y _) (xs.dcK γ0 γc γm rp g (.go j iL γi)) rfl rfl rfl rfl γmc d y g.ev.b
        ((xs.dcK γ0 γc γm rp g (.go j iL γi)).kf d y)
        pm gp cc dep hs sq ld s B D P H
    rw [hrp] at h
    iapply h $$ [Hown Hpr Hcl]
    · iframe Hpkg Hc Hpc Hown Hpr Hcl
    inext
    iintro Hres
    iapply HΦ
    icases Hres with (Hown | Hdone)
    · ileft; iframe Hown; ipureintro; rfl
    · iexfalso; iunfold swift.descDone at Hdone; iunfold swift.descGone at Hdone
      icases Hdone with ⟨%Hsq, -⟩; cases Hsq
  · -- a history slot (T16aG)
    ihave #Hs2 := Hs
    iunfold swift.slotMP at Hs
    icases Hs with ⟨%s, ⟨%Hm, %Hin⟩, #Hex⟩
    subst Hm
    ihave ⟨%dv, %rv, %q, %sl, %fa, %cf, %cond, %fs, %v, %bw, %stp, %rcp, %Hsq, Hd, Htok, Hshe, HsF, HfF,
      Hms, Hmf, Hcore, Hrest, Hocf, Hkf, Hrd, HshR⟩ :=
      swift.descOwnF_slotG γ0 γc γm xs rp (RC rp) g j iL γi γsg γmc d y $$ Hown
    ihave HmS : swift.MPi g y γi γsg (interface.mkOk go.int #s) $$ []
    · isplitr
      · iapply swift.mp_of_slot xs γ0 γc γm rp g y _ Hmp $$ Hs2
      · iexact Hw
    iapply (wp_slot rp g j iL γi γsg γmc d y dv rv s q sl fa cf cond fs v bw stp rcp)
      $$ [HmS Hd Htok Hshe HsF HfF Hms Hmf Hcore Hrest Hocf Hkf Hrd HshR]
    · iframe Hpkg Hc HmS Hd Htok Hshe HsF HfF Hms Hmf Hcore Hrest Hocf Hkf Hrd HshR
      ipureintro; exact Hsq
    inext
    iintro Hres
    iapply HΦ
    iright; iframe Hres; ipureintro; rfl
  · -- a sync entry (T24)
    ihave Hse : swift.syncMP (xs.dcK γ0 γc γm rp g (.go j iL γi)).γ (xs.dcK γ0 γc γm rp g (.go j iL γi)).γcl
        (xs.dcK γ0 γc γm rp g (.go j iL γi)).r
        (sp.leaderOf (xs.dcK γ0 γc γm rp g (.go j iL γi)).N g.ev.b) g.ev.b y m $$ [Hse]
    · iExactEq Hse; rfl
    have h := wp_sync (swift.MPi g y γi γsg) (swift.mpOk_ty xs γ0 γc γm rp g Hmp y _) (xs.dcK γ0 γc γm rp g (.go j iL γi)) rfl rfl rfl rfl γmc d y g.ev.b ((xs.dcK γ0 γc γm rp g (.go j iL γi)).kf d y) m
    rw [hrp] at h
    iapply h $$ [Hown Hse]
    · iframe Hpkg Hc Hpc Hdr Hown Hse
    inext
    iintro Hres
    iapply HΦ
    icases Hres with (Hown | Hdone)
    · ileft; iframe Hown; ipureintro; rfl
    · iexfalso; iunfold swift.descDone at Hdone; iunfold swift.descGone at Hdone
      icases Hdone with ⟨%Hsq, -⟩; cases Hsq

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
