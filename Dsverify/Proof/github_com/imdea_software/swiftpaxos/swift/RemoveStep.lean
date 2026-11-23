/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RemoveStep.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The history slot's `Remove`, ghost part** (round 40, sv-swb; table rev 10 §3R10.7 T16aG/T16aI,
R10-1, P39-1, P39-2; rev 10a §3R10.21; plan "Revision 10a" R10a.3, "T16a step lemmas"): inside
`RemoveL`'s locked step (one `descN` opening, at `⊤`), the owner's entry leaves the map.

* `swift.incInv_retire`: a live incarnation whose owner gives back its half is retired (its key
  leaves the view).
* `swift.descInv_removeG` (T16aG): a goroutine's entry. Lock-lent refuted by the lock token
  (`cmapLocked_excl`), read-lent by the pin (`cmapLocked_pin_false`), **home by `active`** (the
  goroutine's `kfK` half and home's whole), **a sequential state by `seq`** (`descF`'s quarter at
  `false`) (R10-1), stopping by the receipt's shares (`descGo_take`, P39-1); the running state's
  parts, the outer part and the registry quarter come back.
* `swift.descInv_removeI` (T16aI): the inline owner's entry. **Home and every running state by
  `seq`** (`descF`'s quarter at `true`) (R10-1); the sequential state's element moved to the run
  loop's store (`sqE_toSI`, with `ownCtx`'s `shSr`: P39-2, rev 10a C4/40-2).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.StopHome
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GetDescWithEnts

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

/-- An incarnation retired (see the file header). -/
theorem swift.incInv_retire (g : swift.DescG) (Mc : GMap GoString GoInterface) (k : GoString)
    (d : Loc) (γi γsg : GName) :
    swift.incInv g Mc ∗ swift.incW g γi γsg ∗ ghostVar γi (1 : Qp).half (k, d) ⊢
    |==> swift.incInv g (GMap.delete k Mc) := by
  iintro ⟨HI, #Hw, Hv⟩
  iunfold swift.incInv at HI
  icases HI with ⟨%I, %R, Ha, Hm, %Hu⟩
  iunfold swift.incW at Hw
  ihave %Hl := ghost_map_lookup $$ Ha Hw
  have hl : Iris.Std.PartialMap.get? I γi = some γsg := Hl
  icases (BigSepM.bigSepM_delete hl).1 $$ Hm with ⟨Hs, Hm⟩
  have hQ : ¬ ((1 : Qp).half + 1 ≤ 1) := by rw [Qp.le_iff]; simp; grind
  -- `γi` is live at `(k, d)`
  iunfold swift.incSt at Hs
  cases hlive : (R γi).2.2
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iexfalso
    icombine Hv Hs gives %Hc
    exfalso; exact hQ Hc.1
  simp only [↓reduceIte]
  icases Hs with ⟨Hs, %Hmc⟩
  icombine Hv Hs gives %Hc
  obtain ⟨-, Heq⟩ := Hc
  have hk : (R γi).1 = k := (congrArg Prod.fst Heq).symm
  have hd : (R γi).2.1 = d := (congrArg Prod.snd Heq).symm
  ihave Hv1 := (ghostVar_split_half γi (1 : Qp) (k, d)).2 $$ [Hv Hs]
  · rw [← hk, ← hd]; iframe
  -- every other live incarnation's key is not `k`
  have hother : ∀ j, j ≠ γi → I !! j ≠ none → (R j).2.2 = true → (R j).1 ≠ k := by
    intro j hj hjI hjl hjk
    have hγI : I !! γi ≠ none := by
      rw [show I !! γi = Iris.Std.PartialMap.get? I γi from rfl, hl]; simp
    exact hj (Hu j γi hjI hγI hjl hlive (by rw [hjk, hk]))
  imodintro
  iunfold swift.incInv
  iexists I, (fun j => if j = γi then (k, d, false) else R j)
  iframe Ha
  isplitl [Hm Hv1]
  · iapply (BigSepM.bigSepM_delete (Φ := fun j _ => swift.incSt j (GMap.delete k Mc)
      (if j = γi then (k, d, false) else R j)) hl).2
    isplitl [Hv1]
    · simp only [↓reduceIte]
      iunfold swift.incSt
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexact Hv1
    iapply (BigSepM.bigSepM_mono (Φ := fun j _ => swift.incSt j Mc (R j))) $$ Hm
    intro j b hj
    obtain ⟨hne', hj'⟩ := Iris.Std.LawfulPartialMap.get?_delete_some_iff.1 hj
    have hne : j ≠ γi := fun h => hne' h.symm
    have hjI : I !! j ≠ none := by
      rw [show I !! j = Iris.Std.PartialMap.get? I j from rfl, hj']; simp
    simp only [hne, ↓reduceIte]
    iintro Hs
    iunfold swift.incSt at Hs
    iunfold swift.incSt
    cases hl2 : (R j).2.2
    · simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hs
    · simp only [↓reduceIte]
      icases Hs with ⟨Hs, %Hmc2⟩
      iframe Hs
      ipureintro
      rw [GMap.lookup_delete_ne _ (Ne.symm (hother j hne hjI hl2))]; exact Hmc2
  ipureintro
  intro i j hi hj hli hlj hij
  by_cases ei : i = γi
  · subst ei; simp at hli
  by_cases ej : j = γi
  · subst ej; simp at hlj
  simp only [ei, ej, ↓reduceIte] at hli hlj hij
  exact Hu i j hi hj hli hlj hij

/-- **A goroutine's `Remove`, ghost part** (T16aG; see the file header). -/
theorem swift.descInv_removeG (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (str : swift.CommandId → GoString) (iL : Nat) (q : Qp)
    (d : Loc) (y : swift.CommandId) (γi γsg : GName) (j : Nat) (o : Option GoInterface)
    (t : github_com.orcaman.concurrent_map.CmapLock) :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR (swift.descGo γn g str) str) ∗ £ 1 ∗
      swift.epochLoan g.γq iL q ∗ github_com.orcaman.concurrent_map.cmapLocked g.γdc (str y) o t ∗
      swift.incW g γi γsg ∗ ghostVar γi (1 : Qp).half.half (str y, d) ∗
      ghostMapElem g.γj γi (DFrac.own (1 : Qp).half) (j, (1 : Qp).half.half) ∗
      typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
      typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) ⊢
    |={⊤}=> swift.epochLoan g.γq iL q ∗
      github_com.orcaman.concurrent_map.cmapLocked g.γdc (str y) none (t.del (str y)) ∗
      typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
      swift.dfld d go!"active" ↦ true ∗ ghostMapElem γn j (DFrac.own (1 : Qp).half.half) false ∗
      ∃ (sc : Loc) (γc : ChanNames) (m : Loc) (y' : swift.CommandId), ⌜str y' = str y⌝ ∗
        typedPointsto (swift.dfld d go!"seq") false ((DFrac.own (1 : Qp).half)) ∗
        typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
        typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half) ∗ swift.bagW m (g.mp y') ∗
        swift.stopBag γc sc (swift.stopMP g.γs γsg (str y) d sc) ∗
        (swift.sgTok γsg ∨ ghostMapElem g.γs (str y) (DFrac.own (1 : Qp).half) true) ∗
        typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own (1 : Qp).half) := by
  iintro ⟨#HI, Hlc, Hloan, Hlk, #Hw, Hv, Hr, Hseq, Ha⟩
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
  icases Hrest with ⟨%W, Hview, HW, %HWd, Hents, HK, Hpool, Hrec, Hled, Hrca⟩
  iunfold swift.rcptAuth at Hrca
  icases Hrca with ⟨%LJ, HLJ, %Hrc, %J, HJ⟩
  ihave ⟨HK, Hv, %Hmc⟩ := swift.incInv_live g Mc (str y) d γi γsg $$ [HK Hv]
  · iframe HK Hw Hv
  imod github_com.orcaman.concurrent_map.cmapLocked_lookup (⊤ \ ↑swift.descN) swift.descN_cmap_sub
    g.γdc (str y) o t Mc $$ [Hlk Hview] with ⟨Hlk, Hview, %Hk⟩
  · iframe
  rw [Hmc] at Hk
  subst Hk
  icases (BigSepM.bigSepM_delete (show Iris.Std.PartialMap.get? Mc (str y) = some _ from Hmc)).1
    $$ Hents with ⟨He, Hents⟩
  iunfold swift.descEnt at He
  icases He with ⟨%d', %y', %Hv', He⟩
  obtain ⟨hv, hky'⟩ := Hv'
  have hdd : d = d' := swift.mkOk_desc_inj d d' hv
  subst hdd
  have hy : str y' = str y := hky'.symm
  cases hW : W !! str y with
  | some w =>
    obtain ⟨t', ρ', v'⟩ := w
    unfold swift.entW
    icases He with ⟨-, He⟩
    iunfold swift.entL at He
    icases He with ⟨%s, %m, -, -, -, Hlk2, -, -⟩
    iapply swift.fupd_false_elim
    iapply github_com.orcaman.concurrent_map.cmapLocked_excl (⊤ \ ↑swift.descN) swift.descN_cmap_sub
      g.γdc (str y) _ _ t t' Mc $$ [Hlk Hlk2 Hview]
    iframe
  | none =>
  unfold swift.entW
  icases He with (He | ⟨%π, -, Hpin, -⟩)
  rotate_left
  · iapply swift.fupd_false_elim
    iapply github_com.orcaman.concurrent_map.cmapLocked_pin_false (⊤ \ ↑swift.descN)
      swift.descN_cmap_sub g.γdc (str y) _ t _ π.half Mc $$ [Hlk Hpin Hview]
    iframe
  iunfold swift.entS at He
  icases He with ⟨%s, %mo, Hso, Hmo, Hin⟩
  iunfold swift.entI at Hin
  icases Hin with (⟨%Hs0, Hh⟩ | ⟨%Hs0, Hg⟩ | ⟨%Hs0, -⟩)
  · -- home (R10-1): its `active` whole against the goroutine's half
    iexfalso
    iunfold swift.descHomeS at Hh
    icases Hh with ⟨%m, %sc, %sl, %fa, %a, -, -, -, -, -, -, -, Ha2, -⟩
    iapply swift.bool_pt_excl _ a true (1 : Qp).half $$ [Ha2 Ha]
    iframe
  rotate_left
  · -- a sequential state (R10-1): `seq`'s agreement
    subst Hs0
    iexfalso
    icombine Hso Hseq gives %Hc
    cases Hc
  subst Hs0
  ihave Hv' : ghostVar γi (1 : Qp).half.half (str y', d) $$ [Hv]
  · rw [hy]; iexact Hv
  imod swift.descGo_take γn g str d y' Mc J γi γsg j _ $$ [Hg HK HJ Hv' Hr]
    with ⟨HK, HJ, Hvh, Hgn, %a, %sc, %γc, %m, Ha2, Hs2, Hm2, #Hmb, #Hsb, Hst⟩
  · iframe Hg HK HJ Hw Hv' Hr
  ihave Hvh' : ghostVar γi (1 : Qp).half (str y, d) $$ [Hvh]
  · rw [← hy]; iexact Hvh
  imod swift.incInv_retire g Mc (str y) d γi γsg $$ [HK Hvh'] with HK
  · iframe HK Hw Hvh'
  imod github_com.orcaman.concurrent_map.cmapLocked_delete (⊤ \ ↑swift.descN) swift.descN_cmap_sub
    g.γdc (str y) _ t Mc $$ [Hlk Hview] with ⟨Hlk, Hview, -⟩
  · iframe
  -- `a = false` refuted by the goroutine's half (R10-3)
  cases a
  · iexfalso
    ihave ⟨%Hc, -⟩ := typedPointsto_half_combine _ true false (1 : Qp) $$ [Ha Ha2]
    · iframe
    cases Hc
  simp only [↓reduceIte]
  icases Hst with ⟨Hsig, Hsc⟩
  ihave ⟨-, Haw⟩ := typedPointsto_half_combine _ true true (1 : Qp) $$ [Ha Ha2]
  · iframe
  ihave ⟨%Hmm, Hmw⟩ := typedPointsto_half_combine _ mo m (1 : Qp).half $$ [Hmo Hm2]
  · iframe
  imod Hclose $$ [Hst2 HW Hview Hents HK Hpool Hrec Hled HLJ HJ] with -
  · inext
    iunfold swift.descInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hst2
    iexists (GMap.delete (str y) Mc), q0, L, dm1, W
    iframe Hview HW Hents HK Hpool Hrec Hled
    isplitr
    · ipureintro
      intro k' hk'
      by_cases e : str y = k'
      · subst e; exact absurd hW hk'
      · rw [GMap.lookup_delete_ne _ e]; exact HWd k' hk'
    iunfold swift.rcptAuth
    iexists LJ
    iframe HLJ
    isplitr
    · ipureintro; exact Hrc
    iexists _
    iexact HJ
  ihave Hrest : swift.stopBag γc sc (swift.stopMP g.γs γsg (str y) d sc) ∗
      (swift.sgTok γsg ∨ ghostMapElem g.γs (str y) (DFrac.own (1 : Qp).half) true) $$ [Hsig]
  · rw [← hy]; iframe Hsb Hsig
  icases Hrest with ⟨#Hsb', Hsig'⟩
  imodintro
  iframe Hloan Hlk Hseq Haw Hgn
  iexists sc, γc, m, y'
  iframe Hso Hs2 Hmw Hmb Hsb' Hsig' Hsc
  ipureintro; exact hy

/-- **The inline owner's `Remove`, ghost part** (T16aI; see the file header). -/
theorem swift.descInv_removeI (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (str : swift.CommandId → GoString) (hinj : Function.Injective str)
    (γsh : GName)
    (hsh : ∀ (d : Loc) (y : swift.CommandId) (q : Qp),
      g.sr d y ∗ ghostMapElem γsh d (DFrac.own (1 : Qp).half) q ⊢ (False : IProp netDistGF))
    (iL : Nat) (q : Qp) (d : Loc) (y : swift.CommandId) (γi γsg : GName) (o : Option GoInterface)
    (t : github_com.orcaman.concurrent_map.CmapLock) (qs : Qp) :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR (swift.descGo γn g str) str) ∗
      inv swift.seqN (swift.seqInbox g) ∗ £ 1 ∗ £ 1 ∗
      swift.epochLoan g.γq iL q ∗ github_com.orcaman.concurrent_map.cmapLocked g.γdc (str y) o t ∗
      swift.incW g γi γsg ∗ ghostVar γi (1 : Qp).half (str y, d) ∗
      typedPointsto (swift.dfld d go!"seq") true (DFrac.own (1 : Qp).half.half) ∗
      ghostMapElem γsh d (DFrac.own (1 : Qp).half) qs ⊢
    |={⊤}=> swift.epochLoan g.γq iL q ∗
      github_com.orcaman.concurrent_map.cmapLocked g.γdc (str y) none (t.del (str y)) ∗
      typedPointsto (swift.dfld d go!"seq") true (DFrac.own (1 : Qp).half.half) ∗
      ghostMapElem γsh d (DFrac.own (1 : Qp).half) qs ∗
      ghostMapElem g.γS d (DFrac.own 1) y ∗ swift.sqC d y ∗
      ∃ m : Loc, typedPointsto (swift.dfld d go!"seq") true (DFrac.own (1 : Qp).half) ∗
        typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half.half) := by
  iintro ⟨#HI, #HSI, Hlc, Hlc2, Hloan, Hlk, #Hw, Hv, Hseq, Hsh⟩
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
  icases Hrest with ⟨%W, Hview, HW, %HWd, Hents, HK, Hpool, Hrec, Hled, Hrca⟩
  icases (ghostVar_split_half γi (1 : Qp).half (str y, d)).1 $$ Hv with ⟨Hv1, Hv2⟩
  ihave ⟨HK, Hv1, %Hmc⟩ := swift.incInv_live g Mc (str y) d γi γsg $$ [HK Hv1]
  · iframe HK Hw Hv1
  ihave Hv := (ghostVar_split_half γi (1 : Qp).half (str y, d)).2 $$ [Hv1 Hv2]
  · iframe
  imod github_com.orcaman.concurrent_map.cmapLocked_lookup (⊤ \ ↑swift.descN) swift.descN_cmap_sub
    g.γdc (str y) o t Mc $$ [Hlk Hview] with ⟨Hlk, Hview, %Hk⟩
  · iframe
  rw [Hmc] at Hk
  subst Hk
  icases (BigSepM.bigSepM_delete (show Iris.Std.PartialMap.get? Mc (str y) = some _ from Hmc)).1
    $$ Hents with ⟨He, Hents⟩
  iunfold swift.descEnt at He
  icases He with ⟨%d', %y', %Hv', He⟩
  obtain ⟨hv, hky'⟩ := Hv'
  have hdd : d = d' := swift.mkOk_desc_inj d d' hv
  subst hdd
  have hyy : y = y' := hinj hky'
  subst hyy
  cases hW : W !! str y with
  | some w =>
    obtain ⟨t', ρ', v'⟩ := w
    unfold swift.entW
    icases He with ⟨-, He⟩
    iunfold swift.entL at He
    icases He with ⟨%s, %m, -, -, -, Hlk2, -, -⟩
    iapply swift.fupd_false_elim
    iapply github_com.orcaman.concurrent_map.cmapLocked_excl (⊤ \ ↑swift.descN) swift.descN_cmap_sub
      g.γdc (str y) _ _ t t' Mc $$ [Hlk Hlk2 Hview]
    iframe
  | none =>
  unfold swift.entW
  icases He with (He | ⟨%π, -, Hpin, -⟩)
  rotate_left
  · iapply swift.fupd_false_elim
    iapply github_com.orcaman.concurrent_map.cmapLocked_pin_false (⊤ \ ↑swift.descN)
      swift.descN_cmap_sub g.γdc (str y) _ t _ π.half Mc $$ [Hlk Hpin Hview]
    iframe
  iunfold swift.entS at He
  icases He with ⟨%s, %mo, Hso, Hmo, Hin⟩
  iunfold swift.entI at Hin
  icases Hin with (⟨%Hs0, -⟩ | ⟨%Hs0, -⟩ | ⟨%Hs0, Hq⟩)
  · -- home (R10-1): `seq`'s agreement
    subst Hs0
    iexfalso
    icombine Hso Hseq gives %Hc
    cases Hc
  · -- a running goroutine's state (R10-1): `seq`'s agreement
    subst Hs0
    iexfalso
    icombine Hso Hseq gives %Hc
    cases Hc
  subst Hs0
  imod swift.sqE_toSI g γsh hsh d y qs (⊤ \ ↑swift.descN) swift.seqN_desc_sub $$ [Hlc2 Hq Hsh]
    with ⟨HeS, Hq, Hsh⟩
  · iframe HSI Hlc2 Hq Hsh
  imod swift.incInv_retire g Mc (str y) d γi γsg $$ [HK Hv] with HK
  · iframe HK Hw Hv
  imod github_com.orcaman.concurrent_map.cmapLocked_delete (⊤ \ ↑swift.descN) swift.descN_cmap_sub
    g.γdc (str y) _ t Mc $$ [Hlk Hview] with ⟨Hlk, Hview, -⟩
  · iframe
  imod Hclose $$ [Hst2 HW Hview Hents HK Hpool Hrec Hled Hrca] with -
  · inext
    iunfold swift.descInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hst2
    iexists (GMap.delete (str y) Mc), q0, L, dm1, W
    iframe Hview HW Hents HK Hpool Hrec Hled Hrca
    ipureintro
    intro k' hk'
    by_cases e : str y = k'
    · subst e; exact absurd hW hk'
    · rw [GMap.lookup_delete_ne _ e]; exact HWd k' hk'
  imodintro
  iframe Hloan Hlk Hseq Hsh HeS Hq
  iexists mo
  iframe Hso Hmo

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
