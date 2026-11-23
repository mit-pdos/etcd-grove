/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/GetDescWithLoan.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**GetDescWithLoan** (round 43, D52 (4)): GetDescWith's lemmas on the epoch, the incarnations,
the loans and the sequential stores (`descInv_spawnLoan(L)`, `descInv_returnLoan(O)`, `seqTake`, …).
-/
module


public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GetDescWithDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

instance swift.descR_persistentL (γd : GName) (k : GoString) (v : GoInterface) :
    Persistent (swift.descR γd k v) := by
  unfold swift.descR; infer_instance

/-- The running epoch's ballot: a share of `ballot` agrees with `epRunL`'s (round 24: ties a
proposal's ballot to the descriptors' epoch). -/
theorem swift.epRunL_ballot (γ : sp.Names) (γc γm : GName) (rp : Loc) (x : swift.RunX)
    (ev : swift.EpV) (γp : GName) (i : Nat) (Qd : Qp) (bw : w32) (qb : Qp) :
    swift.epRunL γ γc γm rp x ev γp i Qd ∗
      typedPointsto (swift.fld rp go!"ballot") bw (DFrac.own qb) ⊢
    ⌜sp.bal bw = ev.b⌝ ∗ swift.epRunL γ γc γm rp x ev γp i Qd ∗
      typedPointsto (swift.fld rp go!"ballot") bw (DFrac.own qb) := by
  have hrp : (x.epN rp).rp = rp := rfl
  iintro ⟨Hr, Hb⟩
  iunfold swift.epRunL at Hr
  icases Hr with ⟨%γl, %q0, Hpool, Hrest⟩
  iunfold swift.epochPool at Hpool
  icases Hpool with ⟨Ha, Hsh, Hw⟩
  iunfold swift.epochShare at Hsh
  icases Hsh with ⟨Hrd, Hsh⟩
  iunfold swift.epochRd at Hrd
  simp only [hrp]
  icases Hrd with ⟨Hb0, Hs, Hrc, He, Hx, %Hbal⟩
  icombine Hb0 Hb gives %Hag
  subst Hag
  iframe Hb
  isplitr
  · ipureintro; exact Hbal.1
  iunfold swift.epRunL
  iexists γl, q0
  iframe Hrest
  iunfold swift.epochPool
  iframe Ha Hw
  iunfold swift.epochShare
  iunfold swift.epochRd
  simp only [hrp]
  iframe
  ipureintro; exact Hbal

/-- A key not in a finite map of naturals (round 27: the spawn's loan id). -/
theorem swift.gmap_fresh {V : Type} (L : GMap Nat V) : ∃ i, L !! i = none := by
  obtain ⟨l, hl⟩ := L.finite
  refine ⟨l.foldr max 0 + 1, ?_⟩
  cases h : L !! (l.foldr max 0 + 1) with
  | none => rfl
  | some v => exact absurd (hl _ (by simp [h])) (swift.fresh_not_mem l)

/-- **An incarnation's commit** (round 27, D23 G8; at Upsert's commit of a new entry `k ↦ d`):
`γi` (owner's fraction `fr`: the goroutine kept the other half, `live`; or a sequential
descriptor's, whole, retired at once) joins the committed incarnations; its witness. -/
theorem swift.incInv_commit (g : swift.DescG) (Mc : GMap GoString GoInterface) (k : GoString)
    (d : Loc) (γi γsg : GName) (live : Bool) (hk : Mc !! k = none) (E : CoPset) :
    swift.incInv g Mc ∗ ghostVar γi (if live then (1 : Qp).half else 1) (k, d) ⊢
    |={E}=> swift.incInv g (<[k := interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d]> Mc) ∗
      swift.incW g γi γsg := by
  iintro ⟨HI, Hv⟩
  iunfold swift.incInv at HI
  icases HI with ⟨%I, %R, Ha, Hm, %Hu⟩
  -- every live incarnation's key is in the view (so not `k`)
  ihave Hm2 : [∗map] j ↦ _b ∈ I, iprop(swift.incSt j Mc (R j) ∗
      ⌜(R j).2.2 = true → (R j).1 ≠ k⌝) $$ [Hm]
  · iapply (BigSepM.bigSepM_mono (Φ := fun j _ => swift.incSt j Mc (R j))) $$ Hm
    intro j b _
    iintro Hs
    iunfold swift.incSt at Hs
    iunfold swift.incSt
    cases hl : (R j).2.2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hs; ipureintro; intro h; cases h
    · simp only [↓reduceIte]
      icases Hs with ⟨Hs, %Hmc⟩
      iframe Hs
      isplitr
      · ipureintro; exact Hmc
      ipureintro; intro _ he
      rw [he, hk] at Hmc; cases Hmc
  ihave ⟨Hm, Hm3⟩ := (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1 $$ Hm2
  ihave %Hall := (BigSepM.bigSepM_pure (PROP := IProp netDistGF)).1 $$ Hm3
  have Hlive : ∀ j, I !! j ≠ none → (R j).2.2 = true → (R j).1 ≠ k := by
    intro j hj hl
    cases hI : I !! j with
    | none => exact absurd hI hj
    | some b => exact Hall j b hI hl
  -- `γi` is fresh: an incarnation of `I` holds a half (live, then its key is in the view) or all of it
  have hQ1 : ¬ ((1 : Qp) + 1 ≤ 1) := by rw [Qp.le_iff]; simp; grind
  have hQ2 : ¬ ((1 : Qp).half + 1 ≤ 1) := by rw [Qp.le_iff]; simp; grind
  have hQ3 : ¬ ((1 : Qp) + (1 : Qp).half ≤ 1) := by rw [Qp.le_iff]; simp; grind
  cases hfresh : I !! γi
  case some b =>
    iexfalso
    ihave ⟨Hs, -⟩ := (BigSepM.bigSepM_lookup_acc (Φ := fun j _ => swift.incSt j Mc (R j))
      (show Iris.Std.PartialMap.get? I γi = some b from hfresh)).1 $$ Hm
    iunfold swift.incSt at Hs
    cases hl : (R γi).2.2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icombine Hv Hs gives %Hc
      obtain ⟨Hq, -⟩ := Hc
      exfalso; cases live
      · exact hQ1 Hq
      · exact hQ2 Hq
    · simp only [↓reduceIte]
      icases Hs with ⟨Hs, %Hmc⟩
      icombine Hv Hs gives %Hc
      obtain ⟨Hq, Heq⟩ := Hc
      cases live
      · exfalso; exact hQ3 Hq
      · have h1 : (R γi).1 = k := (congrArg Prod.fst Heq).symm
        rw [h1, hk] at Hmc; cases Hmc
  imod ghost_map_insert_persist _ γsg hfresh $$ Ha with ⟨Ha, #Hw⟩
  imodintro
  isplitl [Ha Hm Hv]
  · iunfold swift.incInv
    iexists (I.insert γi γsg), (fun j => if j = γi then (k, d, live) else R j)
    iframe Ha
    isplitl [Hm Hv]
    · iapply (BigSepM.bigSepM_insert (Φ := fun j _ => swift.incSt j
        (<[k := interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d]> Mc)
        (if j = γi then (k, d, live) else R j)) (show Iris.Std.PartialMap.get? I γi = none from hfresh)).2
      isplitl [Hv]
      · simp only [↓reduceIte]
        iunfold swift.incSt
        cases live
        · simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hv
        · simp only [↓reduceIte]
          iframe Hv
          ipureintro; exact GMap.lookup_insert _ _ _
      iapply (BigSepM.bigSepM_mono (Φ := fun j _ => swift.incSt j Mc (R j))) $$ Hm
      intro j b hj
      have hne : j ≠ γi := by
        intro h; subst h; rw [show Iris.Std.PartialMap.get? I j = I !! j from rfl, hfresh] at hj
        cases hj
      simp only [hne, ↓reduceIte]
      iintro Hs
      iunfold swift.incSt at Hs
      iunfold swift.incSt
      cases hl : (R j).2.2
      · simp only [hl, Bool.false_eq_true, ↓reduceIte]; iexact Hs
      · simp only [hl, ↓reduceIte]
        icases Hs with ⟨Hs, %Hmc⟩
        iframe Hs
        ipureintro
        have hk' : (R j).1 ≠ k := Hlive j (by
          rw [show I !! j = Iris.Std.PartialMap.get? I j from rfl, hj]; simp) hl
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hk')]; exact Hmc
    ipureintro
    intro i j hi hj hli hlj hij
    have hI' : ∀ l, (I.insert γi γsg) !! l ≠ none → l = γi ∨ (l ≠ γi ∧ I !! l ≠ none) := by
      intro l hl
      by_cases e : l = γi
      · exact Or.inl e
      · right; refine ⟨e, ?_⟩
        rwa [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl
    rcases hI' i hi with rfl | ⟨ei, hi'⟩ <;> rcases hI' j hj with rfl | ⟨ej, hj'⟩
    · rfl
    · simp only [↓reduceIte, ej] at hli hlj hij
      exact absurd hij.symm (Hlive j hj' hlj)
    · simp only [↓reduceIte, ei] at hli hlj hij
      exact absurd hij (Hlive i hi' hli)
    · simp only [ei, ej, ↓reduceIte] at hli hlj hij
      exact Hu i j hi' hj' hli hlj hij
  iunfold swift.incW
  iexact Hw

/-- **The spawn's loan** (round 27): a share of the descriptors' sub-pool (`descInv`'s, while the
epoch runs) lent to a new goroutine, recorded (`loanRec`) with a share of its `cntL` element. -/
theorem swift.descInv_spawnLoan (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (Run : Loc → swift.CommandId → IProp netDistGF)
    (str : swift.CommandId → GoString) (j : Nat) (qj : Qp) (γi : GName) (v0 : Nat × Qp) (qe : Qp) :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR Run str) ∗
      ghostVar g.γst (1 : Qp).half false ∗ ghostMapElem γn j (DFrac.own qj) false ∗ £ 1 ∗
      ghostMapElem g.γj γi (DFrac.own 1) v0 ⊢
    |={⊤}=> ghostVar g.γst (1 : Qp).half false ∗
      ∃ (iL : Nat) (q : Qp), swift.epochShare ep g.ev q ∗ (∃ dm : GoSlice, swift.descX ep.rp γd g dm q) ∗
        swift.epochLoan g.γq iL q ∗
        ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) (j, qj) ∗
        ghostMapElem g.γj γi (DFrac.own (1 : Qp).half) (j, qe) ∗
        ghostMapElem g.γj γi (DFrac.own (1 : Qp).half) (j, qe) := by
  iintro ⟨#HI, Hst, Hj, Hlc, Hrj⟩
  iinv HI with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑swift.descN) $$ Hlc Hi with Hi
  iunfold swift.descInv at Hi
  icases Hi with ⟨%st, Hst2, Hrest⟩
  icombine Hst Hst2 gives %Hc
  obtain ⟨-, Heq⟩ := Hc
  subst Heq
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hrest with ⟨%Mc, Hrest⟩
  icases Hrest with ⟨%q0, Hrest⟩
  icases Hrest with ⟨%L, Hrest⟩
  icases Hrest with ⟨%dm1, Hrest⟩
  icases Hrest with ⟨%W, Hview, HW, HWd, Hents, HK, Hpool, Hrec, Hled, Hrca⟩
  obtain ⟨iL, hiL⟩ := swift.gmap_fresh L
  iunfold swift.rcptAuth at Hrca
  icases Hrca with ⟨%LJ, HLJ, %Hrc, %J, HJ⟩
  imod ghost_map_update (j, qe) $$ HJ Hrj with ⟨HJ, Hrj⟩
  icases (ghostMapElem_halves g.γj γi (j, qe)).1 $$ Hrj with ⟨Hrj1, Hrj2⟩
  have hLJ : LJ.lookup iL = none := by
    cases e : LJ.lookup iL with
    | none => rfl
    | some v => exact absurd hiL (Hrc iL (by rw [e]; simp))
  imod ghost_map_insert iL (j, qj) hLJ $$ HLJ with ⟨HLJ, Hel⟩
  icases (ghostMapElem_halves g.γlj iL (j, qj)).1 $$ Hel with ⟨Hel1, Hel2⟩
  imod swift.poolS_lend _ (swift.epochShareDX_split ep g.ev ep.rp γd g dm1) g.Qd g.γq q0 L iL hiL
    $$ Hpool with ⟨Hpool, Hsh, Hloan⟩
  iunfold swift.epochShareX at Hsh
  icases Hsh with ⟨Hsh, HX⟩
  imod Hclose $$ [Hst2 HW HWd Hview Hents HK Hpool Hrec Hj Hled HLJ Hel1 HJ] with -
  · inext
    iunfold swift.descInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hst2
    iexists Mc, q0.half, (L.insert iL q0.half), dm1, W
    iframe HW HWd Hview Hents HK Hpool Hled
    isplitl [Hrec Hj Hel1]
    · iunfold swift.loanRec
      iunfold swift.loanRec at Hrec
      iapply (BigSepM.bigSepM_insert (Φ := fun i _ => iprop(∃ (j : Nat) (qj : Qp),
        ghostMapElem γn j (DFrac.own qj) false ∗
        ghostMapElem g.γlj i (DFrac.own (1 : Qp).half) (j, qj)))
        (show Iris.Std.PartialMap.get? L iL = none from hiL)).2
      iframe Hrec
      iexists j, qj
      iframe Hj Hel1
    iunfold swift.rcptAuth
    iexists LJ.insert iL (j, qj)
    iframe HLJ
    isplitr
    · ipureintro
      intro i hi
      rw [GMap.lookup_insert_eq_iff] at hi ⊢
      by_cases e : iL = i
      · rw [if_pos e]; simp
      · rw [if_neg e] at hi ⊢; exact Hrc i hi
    iexists _
    iexact HJ
  imodintro
  iframe Hst
  iexists iL, q0.half
  iframe Hsh Hloan Hel2 Hrj1 Hrj2
  iexists dm1
  iexact HX

/-- **A not-stopped witness** (round 38, table rev 9a C2): `Wt` refutes `descInv`'s stopped branch
(R: its `γst` half at `false`; G/I: a loan token of the sub-pool, `loan_not_stopped`). -/
def swift.liveOk (g : swift.DescG) (Wt : IProp netDistGF) : Prop :=
  Wt ∗ ghostVar g.γst (1 : Qp).half true ∗ ghostMapAuth g.γq 1 (∅ : GMap Nat Qp) ⊢
    (False : IProp netDistGF)

theorem swift.liveOk_run (g : swift.DescG) :
    swift.liveOk g (ghostVar g.γst (1 : Qp).half false) := by
  unfold swift.liveOk
  iintro ⟨H1, H2, -⟩
  icombine H1 H2 gives %Hc
  obtain ⟨-, Heq⟩ := Hc
  cases Heq

theorem swift.liveOk_loan (g : swift.DescG) (iL : Nat) (q : Qp) :
    swift.liveOk g (swift.epochLoan g.γq iL q) := by
  unfold swift.liveOk
  iintro ⟨H1, -, H2⟩
  iapply swift.loan_not_stopped g.γq iL q $$ [H2 H1]
  iframe

theorem swift.lendRef_run (g : swift.DescG) (k : GoString) :
    swift.lendRef g k .run = ghostMapElem g.γs k (DFrac.own 1) false := rfl

/-- **A loan out of the sub-pool for a loan holder or the inline owner** (round 38, plan R9.1 (4):
`descInv_spawnLoanL` (T4 by G/I: the creator's loan token is the witness, G-crt) and
`descInv_lendInline` (T7s: R's `γst` ½; the record's share is ¼ of R's `cntFrozen` ½, key `0`)):
a share `epochShareX q` of the sub-pool (`cmdDescs`' fraction included, R9-1), its token, and the
holder's half of the receipt; the record keeps the registry share `γn j ↦{qj}`. -/
theorem swift.descInv_loanOut (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (Run : Loc → swift.CommandId → IProp netDistGF)
    (str : swift.CommandId → GoString) (j : Nat) (qj : Qp) (Wt : IProp netDistGF)
    (hWt : swift.liveOk g Wt) :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR Run str) ∗ £ 1 ∗ Wt ∗
      ghostMapElem γn j (DFrac.own qj) false ⊢
    |={⊤}=> Wt ∗ ∃ (iL : Nat) (q : Qp), swift.epochShare ep g.ev q ∗
      (∃ dm : GoSlice, swift.descX ep.rp γd g dm q) ∗ swift.epochLoan g.γq iL q ∗
      ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) (j, qj) := by
  iintro ⟨#HI, Hlc, HWt, Hj⟩
  iinv HI with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑swift.descN) $$ Hlc Hi with Hi
  iunfold swift.descInv at Hi
  icases Hi with ⟨%st, Hst2, Hrest⟩
  cases st
  rotate_left
  · simp only [↓reduceIte]
    iexfalso
    have hWt' := hWt
    unfold swift.liveOk at hWt'
    iapply hWt' $$ [HWt Hst2 Hrest]
    iframe
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hrest with ⟨%Mc, Hrest⟩
  icases Hrest with ⟨%q0, Hrest⟩
  icases Hrest with ⟨%L, Hrest⟩
  icases Hrest with ⟨%dm1, Hrest⟩
  icases Hrest with ⟨%W, Hview, HW, HWd, Hents, HK, Hpool, Hrec, Hled, Hrca⟩
  obtain ⟨iL, hiL⟩ := swift.gmap_fresh L
  iunfold swift.rcptAuth at Hrca
  icases Hrca with ⟨%LJ, HLJ, %Hrc, %J, HJ⟩
  have hLJ : LJ.lookup iL = none := by
    cases e : LJ.lookup iL with
    | none => rfl
    | some v => exact absurd hiL (Hrc iL (by rw [e]; simp))
  imod ghost_map_insert iL (j, qj) hLJ $$ HLJ with ⟨HLJ, Hel⟩
  icases (ghostMapElem_halves g.γlj iL (j, qj)).1 $$ Hel with ⟨Hel1, Hel2⟩
  imod swift.poolS_lend _ (swift.epochShareDX_split ep g.ev ep.rp γd g dm1) g.Qd g.γq q0 L iL hiL
    $$ Hpool with ⟨Hpool, Hsh, Hloan⟩
  iunfold swift.epochShareX at Hsh
  icases Hsh with ⟨Hsh, HX⟩
  imod Hclose $$ [Hst2 HW HWd Hview Hents HK Hpool Hrec Hj Hled HLJ Hel1 HJ] with -
  · inext
    iunfold swift.descInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hst2
    iexists Mc, q0.half, (L.insert iL q0.half), dm1, W
    iframe HW HWd Hview Hents HK Hpool Hled
    isplitl [Hrec Hj Hel1]
    · iunfold swift.loanRec
      iunfold swift.loanRec at Hrec
      iapply (BigSepM.bigSepM_insert (Φ := fun i _ => iprop(∃ (j : Nat) (qj : Qp),
        ghostMapElem γn j (DFrac.own qj) false ∗
        ghostMapElem g.γlj i (DFrac.own (1 : Qp).half) (j, qj)))
        (show Iris.Std.PartialMap.get? L iL = none from hiL)).2
      iframe Hrec
      iexists j, qj
      iframe Hj Hel1
    iunfold swift.rcptAuth
    iexists LJ.insert iL (j, qj)
    iframe HLJ
    isplitr
    · ipureintro
      intro i hi
      rw [GMap.lookup_insert_eq_iff] at hi ⊢
      by_cases e : iL = i
      · rw [if_pos e]; simp
      · rw [if_neg e] at hi ⊢; exact Hrc i hi
    iexists _
    iexact HJ
  imodintro
  iframe HWt
  iexists iL, q0.half
  iframe Hsh Hloan Hel2
  iexists dm1
  iexact HX

/-- **A goroutine's or the inline owner's spawn loan** (round 40; table rev 10 T4l (G/I), §3R10.16
#2, plan R10.3 `descInv_spawnLoanL`): `descInv_loanOut` with the creator's loan token as the
not-stopped witness, and in the same opening the new incarnation's receipt `γj γi` set from its
placeholder to the spawn's `(j, qe)`, split in halves (the entry's `descGo` and the goroutine). -/
theorem swift.descInv_spawnLoanL (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (Run : Loc → swift.CommandId → IProp netDistGF)
    (str : swift.CommandId → GoString) (j : Nat) (qj : Qp) (Wt : IProp netDistGF)
    (hWt : swift.liveOk g Wt) (γi : GName) (v0 : Nat × Qp) (qe : Qp) :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR Run str) ∗ £ 1 ∗ Wt ∗
      ghostMapElem γn j (DFrac.own qj) false ∗ ghostMapElem g.γj γi (DFrac.own 1) v0 ⊢
    |={⊤}=> Wt ∗ ∃ (iL : Nat) (q : Qp), swift.epochShare ep g.ev q ∗
      (∃ dm : GoSlice, swift.descX ep.rp γd g dm q) ∗ swift.epochLoan g.γq iL q ∗
      ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) (j, qj) ∗
      ghostMapElem g.γj γi (DFrac.own (1 : Qp).half) (j, qe) ∗
      ghostMapElem g.γj γi (DFrac.own (1 : Qp).half) (j, qe) := by
  iintro ⟨#HI, Hlc, HWt, Hj, Hrj⟩
  iinv HI with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑swift.descN) $$ Hlc Hi with Hi
  iunfold swift.descInv at Hi
  icases Hi with ⟨%st, Hst2, Hrest⟩
  cases st
  rotate_left
  · simp only [↓reduceIte]
    iexfalso
    have hWt' := hWt
    unfold swift.liveOk at hWt'
    iapply hWt' $$ [HWt Hst2 Hrest]
    iframe
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hrest with ⟨%Mc, Hrest⟩
  icases Hrest with ⟨%q0, Hrest⟩
  icases Hrest with ⟨%L, Hrest⟩
  icases Hrest with ⟨%dm1, Hrest⟩
  icases Hrest with ⟨%W, Hview, HW, HWd, Hents, HK, Hpool, Hrec, Hled, Hrca⟩
  obtain ⟨iL, hiL⟩ := swift.gmap_fresh L
  iunfold swift.rcptAuth at Hrca
  icases Hrca with ⟨%LJ, HLJ, %Hrc, %J, HJ⟩
  imod ghost_map_update (j, qe) $$ HJ Hrj with ⟨HJ, Hrj⟩
  icases (ghostMapElem_halves g.γj γi (j, qe)).1 $$ Hrj with ⟨Hrj1, Hrj2⟩
  have hLJ : LJ.lookup iL = none := by
    cases e : LJ.lookup iL with
    | none => rfl
    | some v => exact absurd hiL (Hrc iL (by rw [e]; simp))
  imod ghost_map_insert iL (j, qj) hLJ $$ HLJ with ⟨HLJ, Hel⟩
  icases (ghostMapElem_halves g.γlj iL (j, qj)).1 $$ Hel with ⟨Hel1, Hel2⟩
  imod swift.poolS_lend _ (swift.epochShareDX_split ep g.ev ep.rp γd g dm1) g.Qd g.γq q0 L iL hiL
    $$ Hpool with ⟨Hpool, Hsh, Hloan⟩
  iunfold swift.epochShareX at Hsh
  icases Hsh with ⟨Hsh, HX⟩
  imod Hclose $$ [Hst2 HW HWd Hview Hents HK Hpool Hrec Hj Hled HLJ Hel1 HJ] with -
  · inext
    iunfold swift.descInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hst2
    iexists Mc, q0.half, (L.insert iL q0.half), dm1, W
    iframe HW HWd Hview Hents HK Hpool Hled
    isplitl [Hrec Hj Hel1]
    · iunfold swift.loanRec
      iunfold swift.loanRec at Hrec
      iapply (BigSepM.bigSepM_insert (Φ := fun i _ => iprop(∃ (j : Nat) (qj : Qp),
        ghostMapElem γn j (DFrac.own qj) false ∗
        ghostMapElem g.γlj i (DFrac.own (1 : Qp).half) (j, qj)))
        (show Iris.Std.PartialMap.get? L iL = none from hiL)).2
      iframe Hrec
      iexists j, qj
      iframe Hj Hel1
    iunfold swift.rcptAuth
    iexists LJ.insert iL (j, qj)
    iframe HLJ
    isplitr
    · ipureintro
      intro i hi
      rw [GMap.lookup_insert_eq_iff] at hi ⊢
      by_cases e : iL = i
      · rw [if_pos e]; simp
      · rw [if_neg e] at hi ⊢; exact Hrc i hi
    iexists _
    iexact HJ
  imodintro
  iframe HWt
  iexists iL, q0.half
  iframe Hsh Hloan Hel2 Hrj1 Hrj2
  iexists dm1
  iexact HX

/-- **The registry share of a loan's record, lent to an update** (round 40; table rev 10 T4n by I,
§3R10.16 #3, plan R10.3 `descInv_loanRecAcc`): with the loan's token and receipt half, one
`descN` opening finds the loan's record (`loanRec`, by the receipt) and lends its registry share
`γn j ↦{qj}` to a ghost update (the inline owner's `cntLGhost_spawn_frac`, key `0`). -/
theorem swift.descInv_loanRecAcc (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (Run : Loc → swift.CommandId → IProp netDistGF)
    (str : swift.CommandId → GoString) (iL j : Nat) (q qj : Qp) (R Q : IProp netDistGF)
    (hup : R ∗ ghostMapElem γn j (DFrac.own qj) false ⊢
      |={⊤ \ ↑swift.descN}=> Q ∗ ghostMapElem γn j (DFrac.own qj) false) :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR Run str) ∗ £ 1 ∗ swift.epochLoan g.γq iL q ∗
      ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) (j, qj) ∗ R ⊢
    |={⊤}=> swift.epochLoan g.γq iL q ∗ ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) (j, qj) ∗ Q := by
  iintro ⟨#HI, Hlc, Hloan, Hr, HR⟩
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
  ihave %HrJ := ghost_map_lookup $$ HLJ Hr
  obtain ⟨ql, hql⟩ : ∃ ql, L.lookup iL = some ql := by
    cases e : L.lookup iL with
    | none => exact absurd e (Hrc iL (by rw [HrJ]; simp))
    | some ql => exact ⟨ql, rfl⟩
  iunfold swift.loanRec at Hrec
  icases (BigSepM.bigSepM_delete (show Iris.Std.PartialMap.get? L iL = some ql from hql)).1 $$ Hrec
    with ⟨⟨%j', %qj', Hel, Hr'⟩, Hrec⟩
  ihave %Hjq := ghostMapElem_agree iL g.γlj _ _ _ _ $$ Hr Hr'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj Hjq
  imod hup $$ [HR Hel] with ⟨HQ, Hel⟩
  · iframe
  imod Hclose $$ [Hst2 HW HWd Hview Hents HK Hpool Hrec Hled HLJ HJ Hel Hr'] with -
  · inext
    iunfold swift.descInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hst2
    iexists Mc, q0, L, dm1, W
    iframe HW HWd Hview Hents HK Hpool Hled
    isplitl [Hrec Hel Hr']
    · iunfold swift.loanRec
      iapply (BigSepM.bigSepM_delete (Φ := fun i _ => iprop(∃ (j : Nat) (qj : Qp),
        ghostMapElem γn j (DFrac.own qj) false ∗
        ghostMapElem g.γlj i (DFrac.own (1 : Qp).half) (j, qj)))
        (show Iris.Std.PartialMap.get? L iL = some ql from hql)).2
      iframe Hrec
      iexists j, qj
      iframe Hel Hr'
    iunfold swift.rcptAuth
    iexists LJ
    iframe HLJ
    isplitr
    · ipureintro; exact Hrc
    iexists _
    iexact HJ
  imodintro
  iframe Hloan Hr HQ

/-- **A loan back into the sub-pool** (round 38, plan R9.1 (4) `descInv_returnLoan`; table rev 9
T7e/T7r, T16b, T19x: `epochPoolX_return` with `X q`): the share (its `cmdDescs` fraction agrees
with the pool's), the token (the not-stopped witness) and the holder's receipt half; the record's
registry share comes back. -/
theorem swift.descInv_returnLoan (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (Run : Loc → swift.CommandId → IProp netDistGF)
    (str : swift.CommandId → GoString) (iL : Nat) (q : Qp) (j : Nat) (qj : Qp) (dm : GoSlice) :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR Run str) ∗ £ 1 ∗
      swift.epochShare ep g.ev q ∗ swift.descX ep.rp γd g dm q ∗ swift.epochLoan g.γq iL q ∗
      ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) (j, qj) ⊢
    |={⊤}=> ghostMapElem γn j (DFrac.own qj) false := by
  iintro ⟨#HI, Hlc, Hsh, HX, Hloan, Hr⟩
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
  -- the loan's `cmdDescs` fraction is the pool's (`dm = dm1`)
  ihave %Hdm : ⌜dm = dm1⌝ $$ [HX Hpool]
  · iunfold swift.epochPoolX at Hpool
    iunfold swift.poolS at Hpool
    icases Hpool with ⟨-, Hs0, -⟩
    iunfold swift.epochShareX at Hs0
    icases Hs0 with ⟨-, Hx0⟩
    iunfold swift.descX at HX Hx0
    icases HX with ⟨H1, -⟩
    icases Hx0 with ⟨H2, -⟩
    icombine H1 H2 gives %h
    ipureintro; exact h
  subst Hdm
  ihave Hsx : swift.epochShareX ep g.ev (swift.descX ep.rp γd g dm) q $$ [Hsh HX]
  · iunfold swift.epochShareX; iframe
  iunfold swift.rcptAuth at Hrca
  icases Hrca with ⟨%LJ, HLJ, %Hrc, %J, HJ⟩
  ihave %HrJ := ghost_map_lookup $$ HLJ Hr
  obtain ⟨ql, hql⟩ : ∃ ql, L.lookup iL = some ql := by
    cases e : L.lookup iL with
    | none => exact absurd e (Hrc iL (by rw [HrJ]; simp))
    | some ql => exact ⟨ql, rfl⟩
  iunfold swift.loanRec at Hrec
  icases (BigSepM.bigSepM_delete (show Iris.Std.PartialMap.get? L iL = some ql from hql)).1 $$ Hrec
    with ⟨⟨%j', %qj', Hel, Hr'⟩, Hrec⟩
  ihave %Hjq := ghostMapElem_agree iL g.γlj _ _ _ _ $$ Hr Hr'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj Hjq
  ihave Hrw := (ghostMapElem_halves g.γlj iL (j, qj)).2 $$ [Hr Hr']
  · iframe
  imod ghost_map_delete $$ HLJ Hrw with HLJ
  imod swift.poolS_return _ (swift.epochShareDX_split ep g.ev ep.rp γd g dm) g.Qd g.γq q0 L iL q
    $$ [Hpool Hsx Hloan] with Hpool
  · iframe
  imod Hclose $$ [Hst2 HW HWd Hview Hents HK Hpool Hrec Hled HLJ HJ] with -
  · inext
    iunfold swift.descInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hst2
    iexists Mc, (q0 + q), (GMap.delete iL L), dm, W
    iframe HW HWd Hview Hents HK Hpool Hled
    isplitl [Hrec]
    · iunfold swift.loanRec
      iexact Hrec
    iunfold swift.rcptAuth
    iexists LJ.delete iL
    iframe HLJ
    isplitr
    · ipureintro
      intro i hi
      by_cases e : iL = i
      · subst e; rw [GMap.lookup_delete] at hi; exact absurd rfl hi
      · rw [GMap.lookup_delete_ne _ e] at hi ⊢; exact Hrc i hi
    iexists _
    iexact HJ
  imodintro
  iexact Hel

/-- **An owner's epoch share, agreed with the pool's** (round 40; table rev 10 §3R10.16 #5, rev 10a
C3): the owner holds its epoch share as `epochRd q` (with its pin) and `shOwnR`'s `status`/`FQ` at
existential values; with the pool's own share (at the epoch's values `v`) they agree, so they form
`epochShare n v q`. -/
theorem swift.epochShare_own (n : swift.EpN) (v : swift.EpV) (q0 q : Qp) (b : Nat) (bw : w32)
    (stp rcp : Loc) (st : w64) (fq : GoInterface) :
    swift.epochShare n v q0 ∗ swift.epochRd n.γe n.γxe n.rp n.rr q b bw stp rcp ∗
      ghostVar n.γxp q b ∗ typedPointsto (swift.fld n.rp go!"status") st (DFrac.own q) ∗
      typedPointsto (swift.fld n.rp go!"FQ") fq (DFrac.own q) ⊢
    swift.epochShare n v q0 ∗ swift.epochShare n v q := by
  iintro ⟨H0, Hrd, Hp, Hst, Hfq⟩
  iunfold swift.epochShare at H0
  icases H0 with ⟨Hrd0, Hp0, Hst0, Hfq0⟩
  iunfold swift.epochRd at Hrd0 Hrd
  icases Hrd0 with ⟨Hb0, HS0, Hrc0, He0, Hx0, %Hbal0⟩
  icases Hrd with ⟨Hb, HS, Hrc, He, Hx, %Hbal⟩
  iunfold swift.fqShare at Hfq0
  icases Hfq0 with ⟨Hfq0, #Hq, %Hm⟩
  icombine Hb0 Hb gives %h1
  icombine HS0 HS gives %h2
  icombine Hrc0 Hrc gives %h3
  icombine Hx0 Hx gives %h4
  icombine Hst0 Hst gives %h5
  icombine Hfq0 Hfq gives %h6
  obtain ⟨-, h4⟩ := h4
  obtain ⟨hb, -⟩ := Prod.mk.inj h4
  subst h1 h2 h3 h5 h6 hb
  isplitl [Hb0 HS0 Hrc0 He0 Hx0 Hp0 Hst0 Hfq0]
  · iunfold swift.epochShare
    iunfold swift.epochRd
    iunfold swift.fqShare
    iframe
    isplitr
    · ipureintro; exact Hbal0
    iframe Hq
    ipureintro; exact Hm
  iunfold swift.epochShare
  iunfold swift.epochRd
  iunfold swift.fqShare
  iframe
  isplitr
  · ipureintro; exact Hbal
  iframe Hq
  ipureintro; exact Hm

/-- **A loan back from an owner** (round 40; table rev 10 T7e/T7r/T16b/T19x, §3R10.16 #5, rev 10a
C3, plan R10a.3 `descInv_returnLoanO`): the owner's epoch share at existential values is agreed with
the pool's own share in a first opening (`epochShare_own`), then `descInv_returnLoan` (which the
raw goroutine's path uses as it stands). -/
theorem swift.descInv_returnLoanO (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (Run : Loc → swift.CommandId → IProp netDistGF)
    (str : swift.CommandId → GoString) (iL : Nat) (q : Qp) (j : Nat) (qj : Qp) (dm : GoSlice)
    (b : Nat) (bw : w32) (stp rcp : Loc) (st : w64) (fq : GoInterface) :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR Run str) ∗ £ 1 ∗ £ 1 ∗
      swift.epochRd ep.γe ep.γxe ep.rp ep.rr q b bw stp rcp ∗ ghostVar ep.γxp q b ∗
      typedPointsto (swift.fld ep.rp go!"status") st (DFrac.own q) ∗
      typedPointsto (swift.fld ep.rp go!"FQ") fq (DFrac.own q) ∗
      swift.descX ep.rp γd g dm q ∗ swift.epochLoan g.γq iL q ∗
      ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) (j, qj) ⊢
    |={⊤}=> ghostMapElem γn j (DFrac.own qj) false := by
  iintro ⟨#HI, Hlc1, Hlc2, Hrd, Hp, Hst, Hfq, HX, Hloan, Hr⟩
  ihave Hsh : |={⊤}=> swift.epochLoan g.γq iL q ∗ swift.epochShare ep g.ev q
    $$ [Hlc1 Hrd Hp Hst Hfq Hloan]
  · iinv HI with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑swift.descN) $$ Hlc1 Hi with Hi
    iunfold swift.descInv at Hi
    icases Hi with ⟨%st', Hst2, Hrest⟩
    cases st'
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
    iunfold swift.epochPoolX at Hpool
    iunfold swift.poolS at Hpool
    icases Hpool with ⟨Ha, Hs0, Hwp⟩
    iunfold swift.epochShareX at Hs0
    icases Hs0 with ⟨Hs0, HX0⟩
    ihave ⟨Hs0, Hsh⟩ := swift.epochShare_own ep g.ev q0 q b bw stp rcp st fq $$ [Hs0 Hrd Hp Hst Hfq]
    · iframe
    imod Hclose $$ [Hst2 HW HWd Hview Hents HK Ha Hs0 HX0 Hwp Hrec Hled Hrca] with -
    · inext
      iunfold swift.descInv
      iexists false
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hst2
      iexists Mc, q0, L, dm1, W
      iframe HW HWd Hview Hents HK Hrec Hled Hrca
      iunfold swift.epochPoolX
      iunfold swift.poolS
      iframe Ha Hwp
      iunfold swift.epochShareX
      iframe
    imodintro
    iframe
  imod Hsh with ⟨Hloan, Hsh⟩
  iapply swift.descInv_returnLoan γ γd γn γout g ep DR Run str iL q j qj dm $$ [Hlc2 Hsh HX Hloan Hr]
  iframe HI Hlc2 Hsh HX Hloan Hr

/-- **An incarnation's name, fresh for the entries' receipts** (round 35, table rev 7 §3.11 T2',
D36): in one `descInv` opening, `γi` is allocated avoiding the receipts' keys and its receipt
`γj γi` is inserted (a placeholder value; the spawn's `descInv_spawnLoan` sets it). Round 40 (plan
R10.2 (2), table §3R10.16 #1): with any not-stopped witness `Wt` (R's `γst` half; G/I's loan
token), so a goroutine's or the inline owner's creation (T2' by G/I) uses it. -/
theorem swift.descInv_allocInc
    (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (Run : Loc → swift.CommandId → IProp netDistGF)
    (str : swift.CommandId → GoString) (a : GoString × Loc) (Wt : IProp netDistGF)
    (hWt : swift.liveOk g Wt) :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR Run str) ∗ Wt ∗ £ 1 ⊢
    |={⊤}=> Wt ∗
      ∃ γi : GName, ghostVar γi 1 a ∗ ghostMapElem g.γj γi (DFrac.own 1) ((0 : Nat), (1 : Qp)) := by
  iintro ⟨#HI, Hst, Hlc⟩
  iinv HI with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑swift.descN) $$ Hlc Hi with Hi
  iunfold swift.descInv at Hi
  icases Hi with ⟨%st, Hst2, Hrest⟩
  cases st
  rotate_left
  · simp only [↓reduceIte]
    iexfalso
    have hWt' := hWt
    unfold swift.liveOk at hWt'
    iapply hWt' $$ [Hst Hst2 Hrest]
    iframe
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hrest with ⟨%Mc, Hrest⟩
  icases Hrest with ⟨%q0, Hrest⟩
  icases Hrest with ⟨%L, Hrest⟩
  icases Hrest with ⟨%dm1, Hrest⟩
  icases Hrest with ⟨%W, Hview, HW, HWd, Hents, HK, Hpool, Hrec, Hled, Hrca⟩
  iunfold swift.rcptAuth at Hrca
  icases Hrca with ⟨%LJ, HLJ, %Hrc, %J, HJ⟩
  obtain ⟨l, hl⟩ := J.finite
  imod (ghostVar_alloc_strong (GF := netDistGF) a (· ∉ l) (pred_infinite_not_mem l))
    with ⟨%γi, %Hγi, Hv⟩
  have hJ : J.lookup γi = none := by
    cases e : J.lookup γi with
    | none => rfl
    | some v => exact absurd (hl γi (by rw [show J !! γi = J.lookup γi from rfl, e]; simp)) Hγi
  imod ghost_map_insert γi ((0 : Nat), (1 : Qp)) hJ $$ HJ with ⟨HJ, Hel⟩
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
  iframe Hst
  iexists γi
  iframe

/-- **A new sequential descriptor joins the run loop's store** (round 27, D23 G9): its `γS` element
(fresh, or a retired one's updated: `newDesc` reused it), the store's other entries. -/
theorem swift.seqStore_addN (P : Loc → swift.CommandId → IProp netDistGF)
    (hP : ∀ d y, P d y ⊢ ∃ (a : Bool) (qa : Qp),
      typedPointsto (swift.dfld d go!"active") a (DFrac.own qa) ∗ True)
    (γS : GName) (S : GMap Loc swift.CommandId) (d : Loc) (y : swift.CommandId)
    (E : CoPset) :
    ghostMapAuth γS 1 S ∗ ([∗map] d' ↦ y' ∈ S, P d' y' ∨ ghostMapElem γS d' (DFrac.own 1) y') ∗
      swift.dfld d go!"active" ↦ true ⊢
    |={E}=> ∃ S' : GMap Loc swift.CommandId, ⌜S' !! d = some y⌝ ∗ ghostMapAuth γS 1 S' ∗
      ([∗map] d' ↦ y' ∈ S'.delete d, P d' y' ∨ ghostMapElem γS d' (DFrac.own 1) y') ∗
      ghostMapElem γS d (DFrac.own 1) y ∗ swift.dfld d go!"active" ↦ true := by
  iintro ⟨Ha, Hm, Hact⟩
  cases hS : S !! d with
  | none =>
    imod ghost_map_insert d y hS $$ Ha with ⟨Ha, He⟩
    imodintro
    iexists (<[d := y]> S)
    iframe Ha He Hact
    isplitr
    · ipureintro; exact GMap.lookup_insert _ _ _
    rw [GMap.delete_insert S d y hS]
    iexact Hm
  | some y' =>
    icases (BigSepM.bigSepM_delete (show Iris.Std.PartialMap.get? S d = some y' from hS)).1 $$ Hm
      with ⟨Hd, Hm⟩
    icases Hd with (Hso | He)
    · iexfalso
      ihave ⟨%a, %qa, Ha2, -⟩ := hP d y' $$ Hso
      iapply swift.bool_pt_excl _ true a qa $$ [Hact Ha2]
      iframe
    imod ghost_map_update y $$ Ha He with ⟨Ha, He⟩
    imodintro
    iexists (<[d := y]> S)
    iframe Ha He Hact
    isplitr
    · ipureintro; exact GMap.lookup_insert _ _ _
    rw [GMap.delete_insert_eq S d y]
    iexact Hm

/-- The run loop's store's instance of `seqStore_addN` (round 27). -/
theorem swift.seqStore_add (γ : sp.Names) (DR : Loc → IProp netDistGF) (g : swift.DescG)
    (c0 : swift.DC) (RC0 : Loc → w32 → IProp netDistGF) (hSo : swift.soOk γ DR c0 RC0 g) (S : GMap Loc swift.CommandId) (d : Loc) (y : swift.CommandId)
    (E : CoPset) :
    ghostMapAuth g.γS 1 S ∗ ([∗map] d' ↦ y' ∈ S, g.so d' y' ∨ ghostMapElem g.γS d' (DFrac.own 1) y') ∗
      swift.dfld d go!"active" ↦ true ⊢
    |={E}=> ∃ S' : GMap Loc swift.CommandId, ⌜S' !! d = some y⌝ ∗ ghostMapAuth g.γS 1 S' ∗
      ([∗map] d' ↦ y' ∈ S'.delete d, g.so d' y' ∨ ghostMapElem g.γS d' (DFrac.own 1) y') ∗
      ghostMapElem g.γS d (DFrac.own 1) y ∗ swift.dfld d go!"active" ↦ true :=
  swift.seqStore_addN g.so hSo.2.2.2.1 g.γS S d y E

/-- **The run loop takes a sequential descriptor's owner state** (round 29, D26 G11): from the store
its entry's element names (its own `γS`, or the goroutines' inbox `γS2`: the entry is moved to the
run loop's store, a credit pays the inbox's `▷`), the state out, the run loop's store without it,
the element now `γS`'s. An inbox entry meeting a live one of the run loop's: `soOk`'s clause 1. -/
theorem swift.seqTake (γ : sp.Names) (DR : Loc → IProp netDistGF) (g : swift.DescG)
    (c0 : swift.DC) (RC0 : Loc → w32 → IProp netDistGF) (hSo : swift.soOk γ DR c0 RC0 g) (γe : GName) (hγe : γe = g.γS ∨ γe = g.γS2) (d : Loc)
    (y : swift.CommandId) (E : CoPset) (hE : ↑swift.seqN ⊆ E) :
    inv swift.seqN (swift.seqInbox g) ∗ £ 1 ∗ ghostMapElem γe d (DFrac.own 1) y ∗ swift.seqStore g ⊢
    |={E}=> ghostMapElem g.γS d (DFrac.own 1) y ∗ ∃ S : GMap Loc swift.CommandId,
      ⌜S !! d = some y⌝ ∗ ghostMapAuth g.γS 1 S ∗
      ([∗map] d' ↦ y' ∈ S.delete d, g.so d' y' ∨ ghostMapElem g.γS d' (DFrac.own 1) y') ∗
      g.so d y := by
  iintro ⟨#HSI, Hlc, Hel, HS⟩
  rcases hγe with hγe | hγe <;> subst hγe
  · iunfold swift.seqStore at HS
    icases HS with ⟨%S, HSa, HSm⟩
    ihave %HSd := ghost_map_lookup $$ HSa Hel
    icases (BigSepM.bigSepM_delete HSd).1 $$ HSm with ⟨Hso, HSm⟩
    icases Hso with (Hso | Hel2)
    rotate_left
    · iexfalso
      icombine Hel Hel2 gives %Hc
      exfalso; have := DFrac.valid_own_op Hc.1; simp at this
    imodintro
    iframe Hel
    iexists S
    iframe HSa HSm Hso
    ipureintro; exact HSd
  · imod (inv_acc (E := E) (N := swift.seqN) hE) $$ HSI with ⟨Hi, Hclose⟩
    imod lc_fupd_elim_later (E := E \ ↑swift.seqN) $$ Hlc Hi with Hi
    iunfold swift.seqInbox at Hi
    icases Hi with ⟨%S2, HA2, HM2⟩
    ihave %HSd2 := ghost_map_lookup $$ HA2 Hel
    icases (BigSepM.bigSepM_delete HSd2).1 $$ HM2 with ⟨Hso, HM2⟩
    icases Hso with (Hso | Hel2)
    rotate_left
    · iexfalso
      icombine Hel Hel2 gives %Hc
      exfalso; have := DFrac.valid_own_op Hc.1; simp at this
    imod ghost_map_delete $$ HA2 Hel with HA2
    imod Hclose $$ [HA2 HM2] with -
    · inext
      iunfold swift.seqInbox
      iexists (S2.delete d)
      iframe HA2 HM2
    ihave Hso := hSo.2.2.2.2.1 d y $$ Hso
    iunfold swift.seqStore at HS
    icases HS with ⟨%S, HSa, HSm⟩
    cases hS : S !! d with
    | none =>
      imod ghost_map_insert d y hS $$ HSa with ⟨HSa, He⟩
      imodintro
      iframe He
      iexists (<[d := y]> S)
      iframe HSa Hso
      isplitr
      · ipureintro; exact GMap.lookup_insert _ _ _
      rw [GMap.delete_insert S d y hS]
      iexact HSm
    | some y' =>
      icases (BigSepM.bigSepM_delete (show Iris.Std.PartialMap.get? S d = some y' from hS)).1 $$ HSm
        with ⟨Hd, HSm⟩
      icases Hd with (Hso' | He)
      · iexfalso
        iapply hSo.1 d y' y $$ [Hso' Hso]
        iframe
      imod ghost_map_update y $$ HSa He with ⟨HSa, He⟩
      imodintro
      iframe He
      iexists (<[d := y]> S)
      iframe HSa Hso
      isplitr
      · ipureintro; exact GMap.lookup_insert _ _ _
      rw [GMap.delete_insert_eq S d y]
      iexact HSm

/-- **A goroutine's new sequential descriptor joins the inbox** (round 29, D26 G11; for `depSpecI`'s
sequential creation, inside its commit): with `active` whole (an inbox entry of `d` with an owner
state is refuted by `soOk`'s clause 4; a retired one's element is updated), the owner state made
from it (`soOk`'s clause 3 at the commit) goes into the inbox; the inbox's element comes out. Round
40 (gap 40-3): over `srA` (in every owner's `ownCtx`), not `soOk`, which G/I do not hold. -/
theorem swift.seqInbox_add (g : swift.DescG) (hsrA : swift.srA g) (d : Loc) (y : swift.CommandId)
    (R : IProp netDistGF) (E : CoPset)
    (hE : ↑swift.seqN ⊆ E) :
    inv swift.seqN (swift.seqInbox g) ∗ £ 1 ∗ swift.dfld d go!"active" ↦ true ∗
      (swift.dfld d go!"active" ↦ true -∗ g.sr d y ∗ R) ⊢
    |={E}=> ghostMapElem g.γS2 d (DFrac.own 1) y ∗ R := by
  iintro ⟨#HSI, Hlc, Hact, Hmk⟩
  imod (inv_acc (E := E) (N := swift.seqN) hE) $$ HSI with ⟨Hi, Hclose⟩
  imod lc_fupd_elim_later (E := E \ ↑swift.seqN) $$ Hlc Hi with Hi
  iunfold swift.seqInbox at Hi
  icases Hi with ⟨%S, HSa, HSm⟩
  imod swift.seqStore_addN g.sr hsrA g.γS2 S d y _
    $$ [HSa HSm Hact] with ⟨%S', %HS', HSa, HSm, He, Hact⟩
  · iframe
  ihave ⟨Hso, HR⟩ := Hmk $$ Hact
  imod Hclose $$ [HSa HSm Hso] with -
  · inext
    iunfold swift.seqInbox
    iexists S'
    iframe HSa
    iapply (BigSepM.bigSepM_delete HS').2
    iframe HSm
    ileft; iexact Hso
  imodintro
  iframe He HR

/-- **A retired sequential entry's element is the run loop's** (round 29, G11; for `seqSpecD`'s
slot case): an inbox element of `d` meets an owner state of `d` (the inbox's) while the caller
holds another one (`soOk`'s clause 1). -/
theorem swift.sqE_toS (γ : sp.Names) (DR : Loc → IProp netDistGF) (g : swift.DescG)
    (c0 : swift.DC) (RC0 : Loc → w32 → IProp netDistGF) (hSo : swift.soOk γ DR c0 RC0 g) (d : Loc) (y y' : swift.CommandId) (E : CoPset)
    (hE : ↑swift.seqN ⊆ E) :
    inv swift.seqN (swift.seqInbox g) ∗ £ 1 ∗ swift.sqE g d y ∗ g.so d y' ⊢
    |={E}=> ghostMapElem g.γS d (DFrac.own 1) y ∗ swift.sqC d y ∗ g.so d y' := by
  iintro ⟨#HSI, Hlc, Hq, Hso⟩
  iunfold swift.sqE at Hq
  icases Hq with ⟨%γe, %Hγe, Hel, Hq⟩
  rcases Hγe with hγe | hγe <;> subst hγe
  · imodintro; iframe
  · imod (inv_acc (E := E) (N := swift.seqN) hE) $$ HSI with ⟨Hi, Hclose⟩
    imod lc_fupd_elim_later (E := E \ ↑swift.seqN) $$ Hlc Hi with Hi
    iunfold swift.seqInbox at Hi
    icases Hi with ⟨%S2, HA2, HM2⟩
    ihave %HSd2 := ghost_map_lookup $$ HA2 Hel
    icases (BigSepM.bigSepM_delete HSd2).1 $$ HM2 with ⟨Hso2, HM2⟩
    iexfalso
    icases Hso2 with (Hso2 | Hel2)
    · ihave Hso2 := hSo.2.2.2.2.1 d y $$ Hso2
      iapply hSo.1 d y y' $$ [Hso2 Hso]
      iframe
    · icombine Hel Hel2 gives %Hc
      exfalso; have := DFrac.valid_own_op Hc.1; simp at this

/-- **A retired sequential entry's element is the run loop's, from inside the inline call**
(round 40; table rev 10 T16aI, P39-2, rev 10a §3R10.21 C4/40-2): as `sqE_toS`, but the inline owner
holds no `g.so` (T7s made it the owner state at `cI`); an inbox element meets the inbox's raw form
`g.sr`, which the owner's half of the share map's element refutes (`shSr`, `soOk`'s clause 6). -/
theorem swift.sqE_toSI (g : swift.DescG) (γsh : GName)
    (hsh : ∀ (d : Loc) (y : swift.CommandId) (q : Qp),
      g.sr d y ∗ ghostMapElem γsh d (DFrac.own (1 : Qp).half) q ⊢ (False : IProp netDistGF))
    (d : Loc) (y : swift.CommandId) (q : Qp) (E : CoPset) (hE : ↑swift.seqN ⊆ E) :
    inv swift.seqN (swift.seqInbox g) ∗ £ 1 ∗ swift.sqE g d y ∗
      ghostMapElem γsh d (DFrac.own (1 : Qp).half) q ⊢
    |={E}=> ghostMapElem g.γS d (DFrac.own 1) y ∗ swift.sqC d y ∗
      ghostMapElem γsh d (DFrac.own (1 : Qp).half) q := by
  iintro ⟨#HSI, Hlc, Hq, Hsh⟩
  iunfold swift.sqE at Hq
  icases Hq with ⟨%γe, %Hγe, Hel, Hq⟩
  rcases Hγe with hγe | hγe <;> subst hγe
  · imodintro; iframe
  · imod (inv_acc (E := E) (N := swift.seqN) hE) $$ HSI with ⟨Hi, Hclose⟩
    imod lc_fupd_elim_later (E := E \ ↑swift.seqN) $$ Hlc Hi with Hi
    iunfold swift.seqInbox at Hi
    icases Hi with ⟨%S2, HA2, HM2⟩
    ihave %HSd2 := ghost_map_lookup $$ HA2 Hel
    icases (BigSepM.bigSepM_delete HSd2).1 $$ HM2 with ⟨Hso2, HM2⟩
    iexfalso
    icases Hso2 with (Hso2 | Hel2)
    · iapply hsh d y q $$ [Hso2 Hsh]
      iframe
    · icombine Hel Hel2 gives %Hc
      exfalso; have := DFrac.valid_own_op Hc.1; simp at this

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
