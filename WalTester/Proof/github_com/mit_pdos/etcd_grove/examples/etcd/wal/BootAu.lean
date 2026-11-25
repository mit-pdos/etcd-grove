/-
`Boot`'s ghost steps on the tester's invariant (W4c U5, eleventh session): reading the oracle's relation
to the WAL (`tInv_rel`); raising the program's view of the WAL to named when the oracle says `Create`
returned (`tInv_named`, over the WAL's `walDirIs_named`: so that `Exist`'s `false` arm contradicts it, B2);
`Create`'s update from a state `Exist`'s `false` arm allows (`tInv_createAu`, B3, for the hypothesis
`wal.Create.specFresh`); and the fresh oracle's accounting of the fresh WAL. Lean-first (no Rocq
counterpart).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RestartAu
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Crash
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.StepLive
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Resume
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.NamedView
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.Exist

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

/-! ## The fresh oracle and the fresh WAL (pure) -/

section pure
variable [GooseExts]

theorem tPre_since {o : TOracle} (h : tPre o) : o.since = [] := by
  have := congrArg TOracle.since h; simpa [tFreshOracle] using this

/-- **The fresh oracle (up to its opens) accounts for `Create`'s fresh WAL** through its candidate. -/
theorem tCandOk_fresh {o : TOracle} (h : tPre o) (md : List w8) : tCandOk o tCand0 (walDurFresh md) := by
  have hh : tCandHist o tCand0 = [] := by simp [tCandHist, tCand0, tPre_since h]
  refine ⟨?_, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl, ?_, ?_⟩
  · rw [hh, tPre_mark h]; exact ⟨0, Nat.le_refl _, Nat.zero_le _, Or.inl rfl⟩
  · rw [hh]; intro x hx; cases hx
  · rw [hh, tPre_mark h]; exact tSimAt_tSim (tSimAt_nil 0)

/-- The created fresh oracle (`Boot`: `m.o = freshOracle(); m.o.created = true`). -/
def tFreshC : TOracle := { tFreshOracle with created := true }

theorem tFreshC_cand : tCand0 ∈ tFreshC.cands := by simp [tFreshC, tFreshOracle, tCand0]

theorem tCandOk_freshC (md : List w8) : tCandOk tFreshC tCand0 (walDurFresh md) := by
  have h := tCandOk_fresh (o := tFreshOracle) tPre_fresh md
  exact h

theorem tCheckWf_pre {o : TOracle} (h : tPre o) : tCheckWf o := by
  refine ⟨by simp [tPre_synced h, tPre_since h], fun cd hcd => ?_⟩
  rw [tPre_cands h] at hcd
  simp only [List.mem_singleton] at hcd
  subst hcd
  have hh : tCandHist o tCand0 = [] := by simp [tCandHist, tCand0, tPre_since h]
  rw [hh]
  exact ⟨fun x hx => (by cases hx), by simp⟩

theorem tPre_freshC_not : ¬ tPre tFreshC := by
  intro h; have := tPre_created h; simp [tFreshC] at this

theorem tOrSmall_freshC : tOrSmall tFreshC := by
  unfold tOrSmall; rw [tEncodeOracle_length]
  simp [tOrRest, tFreshC, tFreshOracle, tOpsBytes, tU64_length]

theorem tMemOk_freshC (md : List w8) : tMemOk tFreshC tCand0 (walDurFresh md) := by
  have hh : tCandHist tFreshC tCand0 = [] := by simp [tCandHist, tCand0, tFreshC, tFreshOracle]
  refine ⟨rfl, tFreshC_cand, rfl, ?_, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl, ?_, ?_, ?_⟩
  · rw [hh]; rfl
  · rw [hh]; intro x hx; cases hx
  · simp [tFreshC, tFreshOracle]
  · rw [hh]; exact tSimAt_tSim (tSimAt_nil _)

theorem tMemHs_freshC (md : List w8) : tMemHs tFreshC (walDurFresh md) := rfl

theorem tCheckWf_freshC : tCheckWf tFreshC := by
  refine ⟨by simp [tFreshC, tFreshOracle], fun cd hcd => ?_⟩
  simp only [tFreshC, tFreshOracle, List.mem_singleton] at hcd
  subst hcd
  have hh : tCandHist tFreshC ⟨[], W64 0, W64 0⟩ = [] := by simp [tCandHist, tFreshC, tFreshOracle]
  rw [hh]
  exact ⟨fun x hx => (by cases hx), by simp⟩

theorem tMemFields_c0 : tMemFields (tResumeTerm tC0) (tResumeTerms tC0) := by
  refine ⟨by simp [tResumeTerm, tC0, tHs0], ?_⟩
  intro k x h
  simp only [tResumeTerms, tC0, List.foldl_nil] at h
  rcases (GMap.lookup_insert_Some _ _ _ _ _).1 h with ⟨-, rfl⟩ | ⟨-, h⟩
  · simp
  · simp at h

theorem tMemSim_freshC : tMemSim tFreshC tCand0 tC0.baseIdx (tResumeLast tC0) (tResumeCommit tC0) := by
  have hh : tCandHist tFreshC tCand0 = [] := by simp [tCandHist, tCand0, tFreshC, tFreshOracle]
  refine ⟨walFresh, ?_, ?_, ?_, ?_⟩
  · rw [hh]; exact tSimAt_nil _
  · rfl
  · simp [walFresh, StorContents.last, tResumeLast, tC0]; rfl
  · simp [walFresh, StorContents.commit, tResumeCommit, tResumeLast, tC0, tHs0]

end pure

/-! ## The ghost steps -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- The file system's invariants, out of the WAL area's. -/
theorem walAreaOk_os (W : WalGS GF) (e : TEnv) :
    WalFs.walAreaOk (W := W) walCodec walRaftMr e.R e.jr (e.area) ⊢ osInv (GF := GF) ∗ osSharedInv (GF := GF) e.R := by
  unfold WalFs.walAreaOk
  iintro ⟨-, #Hos, #Hsi, -, -⟩
  iframe #

/-- **The oracle's relation to the WAL**, read off the invariant (persistent). -/
theorem tInv_rel (W : WalGS GF) (e : TEnv) (γ : TGS) (o : TOracle) (od : Option WalDur) (E : CoPset)
    (hE : ↑tN ⊆ E) :
    TInv (W := W) e γ ∗ tOrOwn γ o none ∗ tWalOwn γ od ={E}=∗
      tOrOwn γ o none ∗ tWalOwn γ od ∗ tRelI (W := W) e.area o od := by
  iintro ⟨#Hinv, Ho, Hwo⟩
  iunfold TInv at Hinv
  imod inv_acc (E := E) hE $$ Hinv with ⟨Hi, Hclose⟩
  imod Hi
  iunfold TInvBody at Hi
  icases Hi with ⟨%s, %o1, %oa, %od1, Hs, %hfile, Ho1, Hwd, Hw1, #Hr1, #Ha1⟩
  ihave %hag := tWalOwn_agree γ od od1 $$ Hwo Hw1
  subst od1
  ihave %hag2 := tOrOwn_agree γ o o1 none oa $$ Ho Ho1
  obtain ⟨h1, h2⟩ := hag2
  subst o1; subst h2
  imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
  · inext; iunfold TInvBody; iexists s, o, none, od; iframe; iframe #; ipureintro; exact hfile
  imodintro
  iframe; iframe #

/-- **What the restart takes of the relation**: a candidate accounting for the WAL, if there is one,
the oracle well formed, and `tRelW` (created: the mark synced and the WAL named; else fresh up to the
opens, with the fresh candidate). -/
theorem tRelI_relW (W : WalGS GF) (area : GoString) (o : TOracle) (od : Option WalDur) :
    tRelI (W := W) area o od ⊢ ∃ cd : TCand,
      ⌜cd ∈ o.cands ∧ (∀ d, od = some d → tCandOk o cd d) ∧ tCheckWf o⌝ ∗ tRelW (W := W) area o cd := by
  unfold tRelI tRelW
  cases hcr : o.created with
  | true =>
    simp only [ite_true]
    iintro ⟨%d, %c, %h, #Hsl, #Hnm⟩
    obtain ⟨hod, hc, hok, hw⟩ := h
    iexists c
    isplitr
    · ipureintro
      refine ⟨hc, fun d' hd' => ?_, hw⟩
      rw [hod] at hd'; cases hd'; exact hok
    · iframe #; ipureintro; exact hw
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    iintro %h
    obtain ⟨hpre, hod⟩ := h
    iexists tCand0
    isplitr
    · ipureintro
      refine ⟨by rw [tPre_cands hpre]; simp, fun d' hd' => ?_, tCheckWf_pre hpre⟩
      rcases hod with h | ⟨d, h, hok⟩
      · rw [h] at hd'; cases hd'
      · rw [h] at hd'; cases hd'; exact hok
    · ipureintro; exact hpre

/-- **The view raised to named** (B2): with the oracle created, its relation gives a candidate `c`
accounting for the WAL `d`, whose view becomes named (`walDirIs_named`); both halves of the WAL state
move, the relation re-established with the same candidate (`tCandOk` does not read `named`). -/
theorem tInv_named (W : WalGS GF) (e : TEnv) (γ : TGS) (o : TOracle) (od : Option WalDur)
    (hcr : o.created = true) :
    TInv (W := W) e γ ∗ WalFs.walAreaOk (W := W) walCodec walRaftMr e.R e.jr (e.area) ∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ tOrOwn γ o none ∗ tWalOwn γ od ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ tOrOwn γ o none ∗
      ∃ (d : WalDur) (c : TCand), tWalOwn γ (some d) ∗
        ⌜d.named = true ∧ c ∈ o.cands ∧ tCandOk o c d ∧ tCheckWf o⌝ ∗
        WalFs.walSyncedLb (W := W) (tWalDir e.area) 0 (tCandMark o c) ∗
        WalFs.walNamed (W := W) (tWalDir e.area) 0 := by
  iintro ⟨#Hinv, #Hok, Hnc, Ho, Hwo⟩
  unfold WalFs.walAreaOk
  icases Hok with ⟨#Hwi, -, -, -, -⟩
  iunfold TInv at Hinv
  imod inv_acc (E := ⊤) CoPset.subseteq_top $$ Hinv with ⟨Hi, Hclose⟩
  imod Hi
  iunfold TInvBody at Hi
  icases Hi with ⟨%s, %o1, %oa, %od1, Hs, %hfile, Ho1, Hwd, Hw1, #Hr1, #Ha1⟩
  ihave %hag := tWalOwn_agree γ od od1 $$ Hwo Hw1
  subst od1
  ihave %hag2 := tOrOwn_agree γ o o1 none oa $$ Ho Ho1
  obtain ⟨h1, h2⟩ := hag2
  subst o1; subst h2
  iunfold tRelI at Hr1
  simp only [hcr, ↓reduceIte]
  icases Hr1 with ⟨%d, %c, %hdc, #Hsl, #Hnm⟩
  obtain ⟨hod, hc, hok, hw⟩ := hdc
  subst hod
  imod walDirIs_named (L := hG.goose_localGS) (W := W) walCodec walRaftMr e.R e.jr e.area
    ((⊤ : CoPset) \ ↑tN) walN_sub_tN (tWalDir e.area) 0 d $$ Hwi Hnc Hwd Hnm with ⟨Hnc, Hwd⟩
  iunfold tWalOwn at Hwo
  imod ghostVar_update_halves (some { d with named := true }) γ.γw _ _ $$ Hwo Hw1 with ⟨Hwo, Hw1⟩
  have hok' : tCandOk o c { d with named := true } := hok
  imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
  · inext; iunfold TInvBody
    iexists s, o, none, some { d with named := true }
    iframe Hs Ho1 Hwd Hw1
    isplitr
    · ipureintro; exact hfile
    isplitl
    · iunfold tRelI
      simp only [hcr, ↓reduceIte]
      iexists { d with named := true }, c
      iframe #
      ipureintro; exact ⟨rfl, hc, hok', hw⟩
    · iunfold tRelA; iempintro
  imodintro
  iframe Hnc Ho
  iexists { d with named := true }, c
  iunfold tWalOwn
  iframe Hwo
  iframe #
  ipureintro; exact ⟨rfl, hc, hok', hw⟩

/-- **`Create`'s update** from a state `Exist`'s `false` arm allows (`wal.Create.specFresh`'s), committed
to the fresh WAL: the oracle, not created and fresh up to its opens, accounts for it (`tCandOk_fresh`). -/
theorem tInv_createAu (W : WalGS GF) (e : TEnv) (γ : TGS) (o : TOracle) (od : Option WalDur) (md : List w8)
    (hex : wal.ExistFalseOk od) (hpre : tPre o) (hcr : o.created = false) :
    TInv (W := W) e γ ∗ tOrOwn γ o none ∗ tWalOwn γ od ⊢
      AU <{ ∃∃ o' : Option WalDur, WalFs.walDirIsI (W := W) (tWalDir e.area) 0 o' ∗ ⌜wal.ExistFalseOk o'⌝ }>
        @ WalFs.walAuMask, ∅
        <{ WalFs.walDiskAtI (W := W) (tWalDir e.area) 0 (walDurFresh md),
          COMM tOrOwn γ o none ∗ tWalOwn γ (some (walDurFresh md)) }> := by
  iintro ⟨#Hinv, Ho, Hwo⟩
  iauintro
  unfold atomic_acc
  iunfold TInv at Hinv
  imod inv_acc (E := WalFs.walAuMask) tN_sub_walAu $$ Hinv with ⟨Hi, Hclose⟩
  imod Hi
  iunfold TInvBody at Hi
  icases Hi with ⟨%s0, %o2, %oa, %od1, Hs, %hfile, Ho1, Hwd, Hw1, #Hr1, #Ha1⟩
  ihave %hag := tWalOwn_agree γ od od1 $$ Hwo Hw1
  subst od1
  ihave %hag2 := tOrOwn_agree γ o o2 none oa $$ Ho Ho1
  obtain ⟨h1, h2⟩ := hag2
  subst h2; subst o2
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ WalFs.walAuMask \ ↑tN from LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists od
  iframe Hwd
  isplitr
  · ipureintro; exact hex
  isplit
  · iintro ⟨Hwd, -⟩
    imod Hclose2 with -
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody; iexists s0, o, none, od; iframe; iframe #; ipureintro; exact hfile
    imodintro
    iframe
  · iintro Hwd
    imod Hclose2 with -
    iunfold tWalOwn at Hwo
    imod ghostVar_update_halves (some (walDurFresh md)) γ.γw _ _ $$ Hwo Hw1 with ⟨Hwo, Hw1⟩
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody
      iexists s0, o, none, some (walDurFresh md)
      iframe Hs Ho1 Hw1
      isplitr
      · ipureintro; exact hfile
      isplitl [Hwd]
      · iunfold WalFs.walDiskAtI at Hwd; iexact Hwd
      isplitl
      · iunfold tRelI
        simp only [hcr, Bool.false_eq_true, ↓reduceIte]
        ipureintro; exact ⟨hpre, Or.inr ⟨_, rfl, tCandOk_fresh hpre md⟩⟩
      · iunfold tRelA; iempintro
    imodintro
    iunfold tWalOwn
    iframe

end proof

end etcd_wal
end EtcdGrove
end Perennial
