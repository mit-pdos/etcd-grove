/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/StopHome.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The stop arm's ghost steps** (round 40, sv-swb; table rev 10 §3R10.7 T19a.g/T19Ra and T19h/T19Rh,
rev 10a §3R10.21; plan "Revision 10a" R10a.3; notes/prove-swift.md §48): a goroutine's own entry,
taken through one `descN` opening, whatever its lock-lend state (P1: the stop steps touch `entI`
only, inside `entS` or `entL`).

* `swift.incInv_live`: a live incarnation (a quarter of `γi` with its commit witness) names its
  entry: `Mc !! k = d`.
* `swift.descEnt_goStep`: a step on a goroutine's own entry: read-lent refuted by the request's
  half of the round's element (`true`), a sequential state by `seq` (the caller's quarter `false`),
  home by a caller-supplied refutation (its `active` share); the running state (`descGo`) handed to
  the step, which gives back any `entI` state at `seq = false`.
* `swift.descInv_stopTake` (T19a.g, T19Ra): signalled → stopping (`descGo_stop`), with the caller's
  loan token as the not-stopped witness.
* `swift.descInv_stopHome` (T19h, T19Rh): stopping → home (`descGo_takeStop`), the home's rest
  `DR d` made by a caller-supplied update over the ledger and `γi`'s half (the token path:
  `swift.stopHome_restTok`, `store_putRD` in the same opening; the raw path: tokenless `descRestA`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Retire
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.StopRound
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescFresh

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- A live incarnation names its entry (see the file header). -/
theorem swift.incInv_live (g : swift.DescG) (Mc : GMap GoString GoInterface) (k : GoString)
    (d : Loc) (γi γsg : GName) :
    swift.incInv g Mc ∗ swift.incW g γi γsg ∗ ghostVar γi (1 : Qp).half.half (k, d) ⊢
    swift.incInv g Mc ∗ ghostVar γi (1 : Qp).half.half (k, d) ∗
      ⌜Mc !! k = some (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d)⌝ := by
  iintro ⟨HI, #Hw, Hv⟩
  iunfold swift.incInv at HI
  icases HI with ⟨%I, %R, Ha, Hm, %Hu⟩
  iunfold swift.incW at Hw
  ihave %Hl := ghost_map_lookup $$ Ha Hw
  ihave ⟨Hs, Hback⟩ := (BigSepM.bigSepM_lookup_acc (Φ := fun j _ => swift.incSt j Mc (R j))
    (show Iris.Std.PartialMap.get? I γi = some γsg from Hl)).1 $$ Hm
  ihave ⟨Hs, Hv, %H1⟩ := swift.incSt_live γi Mc (R γi) k d $$ [Hs Hv]
  · iframe
  ihave %Hmc : ⌜Mc !! k = some (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d)⌝
    $$ [Hs]
  · iunfold swift.incSt at Hs
    rw [H1.1]
    simp only [↓reduceIte]
    icases Hs with ⟨-, %Hmc⟩
    ipureintro
    rw [← H1.2.1, ← H1.2.2]; exact Hmc
  ihave Hm := Hback $$ Hs
  iframe Hv
  isplitl
  · iunfold swift.incInv
    iexists I, R
    iframe Ha Hm
    ipureintro; exact Hu
  ipureintro; exact Hmc

/-- **A step on a goroutine's own entry** (see the file header). -/
theorem swift.descEnt_goStep (γ : sp.Names) (γd γn : GName) (g : swift.DescG)
    (DR : Loc → IProp netDistGF) (str : swift.CommandId → GoString)
    (o : Option (github_com.orcaman.concurrent_map.CmapLock × swift.LendK × GoInterface))
    (k : GoString) (d : Loc) (y : swift.CommandId) (hk : k = str y) (P Q : IProp netDistGF)
    (E : CoPset)
    (hhome : ∀ (y' : swift.CommandId) (s : Bool),
      swift.descHomeS γ DR (g.mp y') d y' s ∗ P ⊢ (False : IProp netDistGF))
    (hstep : ∀ y' : swift.CommandId, str y' = str y →
      swift.descGo γn g str d y' ∗ typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
        P ⊢ |={E}=> swift.entI γ DR (swift.descGo γn g str) (swift.sqE g) g.mp d y' false ∗ Q) :
    swift.descEnt γ γd g DR (swift.descGo γn g str) str o k
        (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d) ∗
      typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
      ghostMapElem g.γs k (DFrac.own (1 : Qp).half) true ∗ P ⊢
    |={E}=> swift.descEnt γ γd g DR (swift.descGo γn g str) str o k
        (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d) ∗
      ghostMapElem g.γs k (DFrac.own (1 : Qp).half) true ∗ Q := by
  iintro ⟨He, Hseq, Hel, HP⟩
  iunfold swift.descEnt at He
  icases He with ⟨%d', %y', %Hv, He⟩
  obtain ⟨hv, hky'⟩ := Hv
  have hdd : d = d' := swift.mkOk_desc_inj d d' hv
  subst hdd
  have hy : str y' = str y := hky'.symm.trans hk
  cases o with
  | none =>
    simp only [swift.entW]
    icases He with (HS | ⟨%π, -, -, Hel2⟩)
    rotate_left
    · -- read-lent: the round's element whole at `false`
      iexfalso
      icombine Hel2 Hel gives %Hc
      exfalso; have := DFrac.valid_own_op Hc.1; simp at this
    iunfold swift.entS at HS
    icases HS with ⟨%s, %m, Hs, Hm, Hi⟩
    iunfold swift.entI at Hi
    icases Hi with (⟨%Hs0, Hh⟩ | ⟨%Hs0, Hr⟩ | ⟨%Hs0, -⟩)
    · iexfalso; iapply hhome y' s $$ [Hh HP]; iframe
    · subst Hs0
      imod hstep y' hy $$ [Hr Hseq HP] with ⟨Hi, HQ⟩
      · iframe
      imodintro
      iframe Hel HQ
      iunfold swift.descEnt
      iexists d, y'
      isplitr
      · ipureintro; exact ⟨hv, hky'⟩
      simp only [swift.entW]
      ileft
      iunfold swift.entS
      iexists false, m
      iframe Hs Hm Hi
    · subst Hs0
      iexfalso
      icombine Hs Hseq gives %Hc
      cases Hc
  | some w =>
    obtain ⟨t, ρ, v'⟩ := w
    simp only [swift.entW]
    icases He with ⟨%Hv', HL⟩
    iunfold swift.entL at HL
    icases HL with ⟨%s, %m, Hs, Hm, Hw, Hlk, Href, Hi⟩
    iunfold swift.entI at Hi
    icases Hi with (⟨%Hs0, Hh⟩ | ⟨%Hs0, Hr⟩ | ⟨%Hs0, -⟩)
    · iexfalso; iapply hhome y' s $$ [Hh HP]; iframe
    · subst Hs0
      imod hstep y' hy $$ [Hr Hseq HP] with ⟨Hi, HQ⟩
      · iframe
      imodintro
      iframe Hel HQ
      iunfold swift.descEnt
      iexists d, y'
      isplitr
      · ipureintro; exact ⟨hv, hky'⟩
      simp only [swift.entW]
      isplitr
      · ipureintro; exact Hv'
      iunfold swift.entL
      iexists false, m
      iframe Hs Hm Hw Hlk Href Hi
    · subst Hs0
      iexfalso
      icombine Hs Hseq gives %Hc
      cases Hc

/-- **The stop arm's ghost take** (T19a.g, T19Ra; see the file header). -/
theorem swift.descInv_stopTake (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (str : swift.CommandId → GoString) (iL : Nat) (q : Qp)
    (d : Loc) (y : swift.CommandId) (γi γsg : GName) (j : Nat) :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR (swift.descGo γn g str) str) ∗ £ 1 ∗
      swift.epochLoan g.γq iL q ∗ swift.incW g γi γsg ∗ ghostVar γi (1 : Qp).half.half (str y, d) ∗
      ghostMapElem g.γj γi (DFrac.own (1 : Qp).half) (j, (1 : Qp).half.half) ∗
      typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
      typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) ∗
      swift.sgTok γsg ∗ ghostMapElem g.γs (str y) (DFrac.own (1 : Qp).half) true ⊢
    |={⊤}=> swift.epochLoan g.γq iL q ∗ ghostVar γi (1 : Qp).half.half (str y, d) ∗
      ghostMapElem g.γj γi (DFrac.own (1 : Qp).half.half) (j, (1 : Qp).half.half) ∗
      typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
      swift.dfld d go!"active" ↦ true ∗ swift.sgTok γsg ∗
      ghostMapElem g.γs (str y) (DFrac.own (1 : Qp).half) true := by
  iintro ⟨#HI, Hlc, Hloan, #Hw, Hv, Hr, Hseq, Ha, Hsg, Hel⟩
  iinv HI with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑swift.descN) $$ Hlc Hi with Hi
  iunfold swift.descInv at Hi
  icases Hi with ⟨%st, Hst2, Hrest⟩
  cases st
  rotate_left
  · simp only [↓reduceIte]
    iexfalso
    iapply swift.loan_not_stopped g.γq iL q $$ [Hrest Hloan]
    iframe
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hrest with ⟨%Mc, Hrest⟩
  icases Hrest with ⟨%q0, Hrest⟩
  icases Hrest with ⟨%L, Hrest⟩
  icases Hrest with ⟨%dm1, Hrest⟩
  icases Hrest with ⟨%W, Hview, HW, HWd, Hents, HK, Hpool, Hrec, Hled, Hrca⟩
  ihave ⟨HK, Hv, %Hmc⟩ := swift.incInv_live g Mc (str y) d γi γsg $$ [HK Hv]
  · iframe HK Hw Hv
  ihave ⟨He, Hback⟩ := (BigSepM.bigSepM_lookup_acc (Φ := fun k v =>
    swift.descEnt γ γd g DR (swift.descGo γn g str) str (W !! k) k v)
    (show Iris.Std.PartialMap.get? Mc (str y) = some _ from Hmc)).1 $$ Hents
  have hhome : ∀ (y' : swift.CommandId) (s : Bool),
      swift.descHomeS γ DR (g.mp y') d y' s ∗
        iprop(swift.incW g γi γsg ∗ swift.incInv g Mc ∗ ghostVar γi (1 : Qp).half.half (str y, d) ∗
          ghostMapElem g.γj γi (DFrac.own (1 : Qp).half) (j, (1 : Qp).half.half) ∗
          typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) ∗ swift.sgTok γsg) ⊢
      (False : IProp netDistGF) := by
    intro y' s
    iintro ⟨Hh, -, -, -, -, Ha, -⟩
    iunfold swift.descHomeS at Hh
    icases Hh with ⟨%m, %sc, %sl, %fa, %a, -, -, -, -, -, -, -, Ha2, -⟩
    iapply swift.bool_pt_excl _ a true (1 : Qp).half $$ [Ha2 Ha]
    iframe
  have hstep : ∀ y' : swift.CommandId, str y' = str y →
      swift.descGo γn g str d y' ∗
        typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
        iprop(swift.incW g γi γsg ∗ swift.incInv g Mc ∗ ghostVar γi (1 : Qp).half.half (str y, d) ∗
          ghostMapElem g.γj γi (DFrac.own (1 : Qp).half) (j, (1 : Qp).half.half) ∗
          typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) ∗ swift.sgTok γsg) ⊢
      |={⊤ \ ↑swift.descN}=> swift.entI γ DR (swift.descGo γn g str) (swift.sqE g) g.mp d y' false ∗
        iprop(swift.incInv g Mc ∗ ghostVar γi (1 : Qp).half.half (str y, d) ∗
          ghostMapElem g.γj γi (DFrac.own (1 : Qp).half.half) (j, (1 : Qp).half.half) ∗
          typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
          swift.dfld d go!"active" ↦ true ∗ swift.sgTok γsg) := by
    intro y' hy
    iintro ⟨Hg, Hseq, #Hw, HK, Hv, Hr, Ha, Hsg⟩
    ihave Hv' : ghostVar γi (1 : Qp).half.half (str y', d) $$ [Hv]
    · rw [hy]; iexact Hv
    imod swift.descGo_stop γn g str d y' Mc γi γsg j _ $$ [Hg HK Hv' Hr Ha Hsg]
      with ⟨Hg, HK, Hv', Hr, Ha, Hsg⟩
    · iframe Hg HK Hw Hv' Hr Ha Hsg
    imodintro
    iframe HK Hr Hseq Ha Hsg
    isplitr [Hv']
    · iunfold swift.entI
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexact Hg
    rw [← hy]; iexact Hv'
  imod swift.descEnt_goStep γ γd γn g DR str (W !! str y) (str y) d y rfl _ _ _ hhome hstep
    $$ [He Hseq Hel HK Hv Hr Ha Hsg] with ⟨He, Hel, HK, Hv, Hr, Hseq, Ha, Hsg⟩
  · iframe; iexact Hw
  ihave Hents := Hback $$ He
  imod Hclose $$ [Hst2 HW HWd Hview Hents HK Hpool Hrec Hled Hrca] with -
  · inext
    iunfold swift.descInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hst2
    iexists Mc, q0, L, dm1, W
    iframe
  imodintro
  iframe

/-- **The home step** (T19h, T19Rh; see the file header): from stopping, the entry goes home
(`descHomeS`: `msgs` ¾ = the owner's ½ + `descGo`'s ¼, `seq` ½ = ¼ + ¼, `stopChan` whole = ½ + ½,
`active` whole at `false`, the sets free, the rest `DR d` made by `hDR` from the ledger and `γi`'s
half in the same opening); `descGo`'s registry quarter and the element's half come out. -/
theorem swift.descInv_stopHome (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (str : swift.CommandId → GoString) (iL : Nat) (q : Qp)
    (d : Loc) (y : swift.CommandId) (γi γsg : GName) (j : Nat) (m0 sc0 sl fa : Loc)
    (R R' : IProp netDistGF)
    (hDR : swift.ledgerD γn γout ∗ ghostVar γi (1 : Qp).half (str y, d) ∗ R ⊢
      |={⊤ \ ↑swift.descN}=> swift.ledgerD γn γout ∗ DR d ∗ R') :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR (swift.descGo γn g str) str) ∗ £ 1 ∗
      swift.epochLoan g.γq iL q ∗ swift.incW g γi γsg ∗ ghostVar γi (1 : Qp).half.half (str y, d) ∗
      ghostMapElem g.γj γi (DFrac.own (1 : Qp).half.half) (j, (1 : Qp).half.half) ∗
      ghostMapElem g.γs (str y) (DFrac.own (1 : Qp).half) true ∗
      typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
      typedPointsto (swift.dfld d go!"msgs") m0 (DFrac.own (1 : Qp).half) ∗
      typedPointsto (swift.dfld d go!"stopChan") sc0 (DFrac.own (1 : Qp).half) ∗
      swift.dfld d go!"active" ↦ false ∗
      swift.dfld d go!"slowPathH" ↦ sl ∗ swift.dfld d go!"fastPathH" ↦ fa ∗
      swift.msgSetFree sl ∗ swift.msgSetFree fa ∗ R ⊢
    |={⊤}=> swift.epochLoan g.γq iL q ∗ ghostMapElem γn j (DFrac.own (1 : Qp).half.half) false ∗
      ghostMapElem g.γs (str y) (DFrac.own (1 : Qp).half) true ∗
      ghostMapElem g.γs (str y) (DFrac.own (1 : Qp).half) true ∗ R' := by
  iintro ⟨#HI, Hlc, Hloan, #Hw, Hv, Hr, Hel, Hseq, Hm0, Hsc0, Ha, Hsl, Hfa, Hfs, Hff, HR⟩
  iinv HI with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑swift.descN) $$ Hlc Hi with Hi
  iunfold swift.descInv at Hi
  icases Hi with ⟨%st, Hst2, Hrest⟩
  cases st
  rotate_left
  · simp only [↓reduceIte]
    iexfalso
    iapply swift.loan_not_stopped g.γq iL q $$ [Hrest Hloan]
    iframe
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hrest with ⟨%Mc, Hrest⟩
  icases Hrest with ⟨%q0, Hrest⟩
  icases Hrest with ⟨%L, Hrest⟩
  icases Hrest with ⟨%dm1, Hrest⟩
  icases Hrest with ⟨%W, Hview, HW, HWd, Hents, HK, Hpool, Hrec, Hled, Hrca⟩
  iunfold swift.rcptAuth at Hrca
  icases Hrca with ⟨%LJ, HLJ, %Hrc, %J, HJ⟩
  ihave ⟨HK, Hv, %Hmc⟩ := swift.incInv_live g Mc (str y) d γi γsg $$ [HK Hv]
  · iframe HK Hw Hv
  ihave ⟨He, Hback⟩ := (BigSepM.bigSepM_lookup_acc (Φ := fun k v =>
    swift.descEnt γ γd g DR (swift.descGo γn g str) str (W !! k) k v)
    (show Iris.Std.PartialMap.get? Mc (str y) = some _ from Hmc)).1 $$ Hents
  have hhome : ∀ (y' : swift.CommandId) (s : Bool),
      swift.descHomeS γ DR (g.mp y') d y' s ∗
        iprop(swift.incW g γi γsg ∗ swift.incInv g Mc ∗ ghostMapAuth g.γj 1 J ∗ swift.ledgerD γn γout ∗
          ghostVar γi (1 : Qp).half.half (str y, d) ∗
          ghostMapElem g.γj γi (DFrac.own (1 : Qp).half.half) (j, (1 : Qp).half.half) ∗
          typedPointsto (swift.dfld d go!"msgs") m0 (DFrac.own (1 : Qp).half) ∗
          typedPointsto (swift.dfld d go!"stopChan") sc0 (DFrac.own (1 : Qp).half) ∗
          swift.dfld d go!"active" ↦ false ∗
          swift.dfld d go!"slowPathH" ↦ sl ∗ swift.dfld d go!"fastPathH" ↦ fa ∗
          swift.msgSetFree sl ∗ swift.msgSetFree fa ∗ R) ⊢
      (False : IProp netDistGF) := by
    intro y' s
    iintro ⟨Hh, -, -, -, -, -, -, -, -, Ha, -⟩
    iunfold swift.descHomeS at Hh
    icases Hh with ⟨%m, %sc, %sl', %fa', %a, -, -, -, -, -, -, -, Ha2, -⟩
    iapply swift.bool_pt_excl _ false a (1 : Qp) $$ [Ha Ha2]
    iframe
  have hstep : ∀ y' : swift.CommandId, str y' = str y →
      swift.descGo γn g str d y' ∗
        typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
        iprop(swift.incW g γi γsg ∗ swift.incInv g Mc ∗ ghostMapAuth g.γj 1 J ∗ swift.ledgerD γn γout ∗
          ghostVar γi (1 : Qp).half.half (str y, d) ∗
          ghostMapElem g.γj γi (DFrac.own (1 : Qp).half.half) (j, (1 : Qp).half.half) ∗
          typedPointsto (swift.dfld d go!"msgs") m0 (DFrac.own (1 : Qp).half) ∗
          typedPointsto (swift.dfld d go!"stopChan") sc0 (DFrac.own (1 : Qp).half) ∗
          swift.dfld d go!"active" ↦ false ∗
          swift.dfld d go!"slowPathH" ↦ sl ∗ swift.dfld d go!"fastPathH" ↦ fa ∗
          swift.msgSetFree sl ∗ swift.msgSetFree fa ∗ R) ⊢
      |={⊤ \ ↑swift.descN}=> swift.entI γ DR (swift.descGo γn g str) (swift.sqE g) g.mp d y' false ∗
        iprop(swift.incInv g Mc ∗ ghostMapAuth g.γj 1 (J.delete γi) ∗ swift.ledgerD γn γout ∗
          ghostMapElem γn j (DFrac.own (1 : Qp).half.half) false ∗
          ghostMapElem g.γs (str y) (DFrac.own (1 : Qp).half) true ∗ R') := by
    intro y' hy
    iintro ⟨Hg, Hseq, #Hw, HK, HJ, Hled, Hv, Hr, Hm0, Hsc0, Ha, Hsl, Hfa, Hfs, Hff, HR⟩
    ihave Hv' : ghostVar γi (1 : Qp).half.half (str y', d) $$ [Hv]
    · rw [hy]; iexact Hv
    imod swift.descGo_takeStop γn g str d y' Mc J γi γsg j false _ $$ [Hg HK HJ Hv' Hr Ha]
      with ⟨HK, HJ, Hvh, Hgn, Ha, %sc, %γc, %m, Hs, Hm, #Hmb, -, Hel2, Hsc⟩
    · iframe Hg HK HJ Hw Hv' Hr Ha
    ihave Hvh' : ghostVar γi (1 : Qp).half (str y, d) $$ [Hvh]
    · rw [← hy]; iexact Hvh
    imod hDR $$ [Hled Hvh' HR] with ⟨Hled, HDR, HR'⟩
    · iframe
    ihave ⟨%Hmm, Hm⟩ := swift.pt_14_12 _ m m0 $$ [Hm Hm0]
    · iframe
    subst Hmm
    ihave ⟨-, Hs⟩ := typedPointsto_half_combine _ false false (1 : Qp).half $$ [Hseq Hs]
    · iframe
    ihave ⟨-, Hsc⟩ := typedPointsto_half_combine _ sc0 sc (1 : Qp) $$ [Hsc0 Hsc]
    · iframe
    ihave Hel3 : ghostMapElem g.γs (str y) (DFrac.own (1 : Qp).half) true $$ [Hel2]
    · rw [← hy]; iexact Hel2
    imodintro
    iframe HK HJ Hled Hgn Hel3 HR'
    iunfold swift.entI
    ileft
    isplitr
    · ipureintro; rfl
    iunfold swift.descHomeS
    iexists m, sc, sl, fa, false
    iframe Hm Hmb Hsc Hsl Hfa Hfs Hff Ha Hs HDR
    ipureintro; intro h; cases h
  imod swift.descEnt_goStep γ γd γn g DR str (W !! str y) (str y) d y rfl _ _ _ hhome hstep
    $$ [He Hseq Hel HK HJ Hled Hv Hr Hm0 Hsc0 Ha Hsl Hfa Hfs Hff HR]
    with ⟨He, Hel, HK, HJ, Hled, Hgn, Hel2, HR'⟩
  · iframe; iexact Hw
  ihave Hents := Hback $$ He
  imod Hclose $$ [Hst2 HW HWd Hview Hents HK Hpool Hrec Hled HLJ HJ] with -
  · inext
    iunfold swift.descInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hst2
    iexists Mc, q0, L, dm1, W
    iframe HW HWd Hview Hents HK Hpool Hrec Hled
    iunfold swift.rcptAuth
    iexists LJ
    iframe HLJ
    isplitr
    · ipureintro; exact Hrc
    iexists _
    iexact HJ
  imodintro
  iframe

/-- **A raw descriptor's rest, tokenless** (round 40; T19Rh): `descRaw` with the share map's element
whole gives the sets (free) and `descRestA` (from `soOk_O`'s raw case, DescFresh). -/
theorem swift.descRaw_home (γ : sp.Names) (sn : swift.StN) (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (y : swift.CommandId) (b : Nat) (sqv fqv : GoInterface)
    (szS szF : Nat) (memS memF : w32 → Prop) (γm : ChanNames) (d : Loc) (q : Qp) (bh : Nat) :
    swift.descRaw c RC MP y b sqv fqv szS szF memS memF γm d ∗ ghostMapElem c.γsh d (DFrac.own 1) q ⊢
    ∃ sl fa : Loc, swift.dfld d go!"slowPathH" ↦ sl ∗ swift.dfld d go!"fastPathH" ↦ fa ∗
      swift.msgSetFree sl ∗ swift.msgSetFree fa ∗ swift.descRestT γ sn c.γsh bh d := by
  iintro ⟨Hraw, Hsh⟩
  iunfold swift.descRaw at Hraw
  icases Hraw with ⟨%cf, %sl, %fa, %cond, %df, %hd, %cc, %vs, %sn', #Hmx, Hcmd, #Hvs, %Hop, Hdep,
    Hhs, Hsn, Hph, Hslw, Hdf, -, Hsb, Hp, Hpd, Hwa, Hap, Hocf, -, Hsl, Hfa, Hsls, Hfas, -⟩
  iexists sl, fa
  iframe Hsl Hfa
  isplitl [Hsls]
  · iapply swift.ownD_free $$ Hsls
  isplitl [Hfas]
  · iapply swift.ownD_free $$ Hfas
  ihave Hoa : swift.ocfAny cf $$ [Hocf]
  · iunfold swift.ocfAny
    iright
    iunfold hook.ocf.ownOcf at Hocf
    icases Hocf with ⟨%osl, %oL, Hocf⟩
    iexists cond, [], osl, oL
    iexact Hocf
  iapply swift.descRestT_raw γ sn c.γsh bh d q (W64 0) sn' cc vs slice.nil slice.nil cf null false df Hop
  iframe Hsh Hmx Hph Hcmd Hvs Hdep Hhs Hsn Hp Hpd Hap Hoa Hslw Hdf Hwa Hsb

/-- **The home step of a raw goroutine** (T19Rh; table rev 10a §3R10.21 C3): `descInv_stopHome`
with the tokenless rest (`descRestA` from `descRaw`, `descRaw_home`). -/
theorem swift.descInv_stopHomeR (γ : sp.Names) (γv γe γo : GName) (sn : swift.StN) (k : Nat)
    (γsh : GName) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (str : swift.CommandId → GoString) (iL : Nat) (q : Qp)
    (d : Loc) (y : swift.CommandId) (γi γsg : GName) (j : Nat) (m0 sc0 : Loc)
    (c : swift.DC) (hc : c.γsh = γsh) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (b : Nat) (sqv fqv : GoInterface)
    (szS szF : Nat) (memS memF : w32 → Prop) (γm : ChanNames) (qs : Qp) :
    inv swift.descN (swift.descInv γ γd γn γout g ep (swift.descRestS γ γv γe γo sn k γsh g.ev.b)
        (swift.descGo γn g str) str) ∗ £ 1 ∗
      swift.epochLoan g.γq iL q ∗ swift.incW g γi γsg ∗ ghostVar γi (1 : Qp).half.half (str y, d) ∗
      ghostMapElem g.γj γi (DFrac.own (1 : Qp).half.half) (j, (1 : Qp).half.half) ∗
      ghostMapElem g.γs (str y) (DFrac.own (1 : Qp).half) true ∗
      typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
      typedPointsto (swift.dfld d go!"msgs") m0 (DFrac.own (1 : Qp).half) ∗
      typedPointsto (swift.dfld d go!"stopChan") sc0 (DFrac.own (1 : Qp).half) ∗
      swift.dfld d go!"active" ↦ false ∗
      swift.descRaw c RC MP y b sqv fqv szS szF memS memF γm d ∗ ghostMapElem c.γsh d (DFrac.own 1) qs ⊢
    |={⊤}=> swift.epochLoan g.γq iL q ∗ ghostMapElem γn j (DFrac.own (1 : Qp).half.half) false ∗
      ghostMapElem g.γs (str y) (DFrac.own (1 : Qp).half) true ∗
      ghostMapElem g.γs (str y) (DFrac.own (1 : Qp).half) true := by
  iintro ⟨#HI, Hlc, Hloan, #Hw, Hv, Hr, Hel, Hseq, Hm0, Hsc0, Ha, Hraw, Hsh⟩
  ihave ⟨%sl, %fa, Hsl, Hfa, Hfs, Hff, HRA⟩ := swift.descRaw_home γ sn c RC MP y b sqv fqv szS szF memS
    memF γm d qs g.ev.b $$ [Hraw Hsh]
  · iframe
  rw [hc]
  have hDR : swift.ledgerD γn γout ∗ ghostVar γi (1 : Qp).half (str y, d) ∗ swift.descRestT γ sn γsh g.ev.b d ⊢
      |={⊤ \ ↑swift.descN}=> swift.ledgerD γn γout ∗ swift.descRestS γ γv γe γo sn k γsh g.ev.b d ∗
        iprop(True) := by
    iintro ⟨Hled, -, HRA⟩
    imodintro
    iframe Hled
    isplitl [HRA]
    · iapply swift.descRestT_S $$ HRA
    itrivial
  imod swift.descInv_stopHome γ γd γn γout g ep (swift.descRestS γ γv γe γo sn k γsh g.ev.b) str iL q d y
      γi γsg j m0 sc0 sl fa (swift.descRestT γ sn γsh g.ev.b d) iprop(True) hDR
    $$ [Hlc Hloan Hv Hr Hel Hseq Hm0 Hsc0 Ha Hsl Hfa Hfs Hff HRA] with ⟨Hloan, Hgn, Hel1, Hel2, -⟩
  · iframe HI Hlc Hloan Hw Hv Hr Hel Hseq Hm0 Hsc0 Ha Hsl Hfa Hfs Hff HRA
  imodintro; iframe

/-- **The token path's rest** (T19h; table rev 10 §3R10.9, LS #6): `store_putRD` in `descInv_stopHome`'s
opening: the token goes back with its rest record (`rest d γi`, `γi`'s half), the ledger's `Out K`
is deleted (its registry share back, `slot none`), and the claim goes into the home's rest
(`descRestS`'s stored disjunct with `descRestH`). -/
theorem swift.stopHome_restTok (γ : sp.Names) (γv γe γo : GName) (sn : swift.StN) (k : Nat)
    (γsh γn : GName) (d : Loc) (y : swift.CommandId) (γi : GName) (K : Nat × sp.CmdId)
    (rv : swift.RowV) (jq : Nat × Qp) (b : Nat) :
    swift.ledgerD γn sn.γout ∗ ghostVar γi (1 : Qp).half (sn.str y, d) ∗
      iprop(inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗ swift.rowTok γo K.1 K.2 rv ∗
        swift.tixOr sn.γxu sn.γxm K ∗ swift.outRcpt sn.γout K jq ∗
        (ghostVar γi (1 : Qp).half (sn.str y, d) -∗
          swift.retWhy γ sn.γxm sn.γcg sn.str sn.N sn.r K rv (swift.recOf (.rest d γi))) ∗
        swift.descRestH γ sn γsh b K d) ⊢
    |={⊤ \ ↑swift.descN}=> swift.ledgerD γn sn.γout ∗ swift.descRestS γ γv γe γo sn k γsh b d ∗
      ghostMapElem γn jq.1 (DFrac.own jq.2) false := by
  iintro ⟨Hled, Hv, #HN, Htok, Htx, Hrc, Hw, HH⟩
  ihave Hwhy := Hw $$ Hv
  imod swift.store_putRD γ γv γe γo sn k γn K (.rest d γi) rv jq _ swift.nodeN_desc_sub
    $$ [Hled Htok Hwhy Htx Hrc] with ⟨Hled, Hj, Hcl⟩
  · iframe HN Hled Htok Hwhy Htx Hrc
  imodintro
  iframe Hled Hj
  iunfold swift.descRestS
  iright
  iframe HN
  iexists K, γi
  iframe Hcl HH

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
