/-
(hraft_robust R4b) **The main goroutine's protocol state through its view** (`srvV rc s`, the crash
invariant `srvDurInv` holding `srvOwn`): reading facts of `srvOwn` (`durFact`), and the timeless pieces of
`durBody` (so that opening the invariant outside an atomic update needs no later credit: only the stores'
client authorities and `latestDur` are not timeless, and no step of the main goroutine's state changes
them).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Crash
public import Dsverify.Proof.github_com.hashicorp.raft.core.Helpers

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft

open proto gprot

section dur
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

instance dv_srvOwn_timeless (γ : GNames) (i : SID) (s : SState) :
    Timeless (srvOwn (GF := GF) γ i s) := by
  unfold srvOwn; infer_instance

instance dv_durView_timeless (γ : GNames) (i : SID) (q : Qp) (d : Nat) :
    Timeless (durView (GF := GF) γ i q d) := by
  unfold durView; infer_instance

instance dv_logCouple_timeless (γ : GNames) (i : SID) (L : RLog) :
    Timeless (logCouple (GF := GF) γ i L) := by
  unfold logCouple; infer_instance

instance dv_termCouple_timeless (γ : GNames) (i : SID) (t : Nat) :
    Timeless (termCouple (GF := GF) γ i t) := by
  unfold termCouple; infer_instance

instance dv_cidxCouple_timeless (γ : GNames) (i : SID) (c : Nat) :
    Timeless (cidxCouple (GF := GF) γ i c) := by
  unfold cidxCouple; infer_instance

/-- The main goroutine's view agrees with the crash state's (no pending step). -/
theorem dvN_gprot_dur : (↑gprotN : CoPset) ⊆ ⊤ \ ↑durN := gprotN_diff_raft "dur"

theorem dvN_dur_term : (↑durN : CoPset) ⊆ ⊤ \ ↑termN := by
  unfold durN termN raftN; solve_ndisj

/-- The main goroutine's view agrees with the crash state's (no pending step). -/
theorem srvV_agree (rc : RCtx GF) (X : SrvDur) (s : SState) :
    ghostVar rc.dur.sv (1 : Qp).half (X.s, X.tp, X.dp) ∗ srvV rc s ⊢
      ⌜X.s = s ∧ X.tp = none ∧ X.dp = none⌝ := by
  unfold srvV
  iintro ⟨H1, H2⟩
  ihave %h := ghostVar_agree _ _ _ _ _ $$ H1 H2
  ipureintro
  simp only [Prod.mk.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- (hraft_robust R4b) **A fact of the main goroutine's protocol state**, through its view: what a gprot
law gives from `srvOwn γ i s` (and other resources `R`) without changing it. -/
theorem durFact (γ : GNames) (rc : RCtx GF) (i : SID) {E : CoPset} (hE : ↑durN ⊆ E) (s : SState)
    (R P : IProp GF) (h : R ∗ srvOwn γ i s ⊢ |={E \ ↑durN}=> srvOwn γ i s ∗ P) :
    srvDurInv γ rc i ∗ srvV rc s ∗ R ⊢ |NC={E}=> srvV rc s ∗ P := by
  iintro ⟨#Hinv, Hv, HR⟩ Hnc
  iunfold srvDurInv at Hinv
  icases Hinv with ⟨#Hinv, -⟩
  ihave Hacc := durAcc γ rc i hE $$ Hinv
  imod Hacc $$ Hnc with ⟨Hnc, HX, Hclose⟩
  unfold durBody srvV
  imod later_exists_except0 $$ HX with ⟨%X, HX⟩
  icases HX with ⟨>Hsrv, Hdv, Hlc, Htc, Hcc, >Hsv, Hrest⟩
  ihave %Hag := ghostVar_agree _ _ _ _ _ $$ Hsv Hv
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨hs, -, -⟩ := Hag
  subst hs
  imod h $$ [HR Hsrv] with ⟨Hsrv, HP⟩
  · iframe
  imod Hclose $$ [Hsrv Hdv Hlc Htc Hcc Hsv Hrest] with -
  · inext; iexists X; iframe
  imodintro
  iframe

variable [hRB : ReceiptBoundLe GF (2 ^ 62)] in
/-- The main goroutine's term, as a persistent lower bound (from `durBody`'s `termCouple`). -/
theorem srvV_termLb (γ : GNames) (rc : RCtx GF) (i : SID) {E : CoPset} (hE : ↑durN ⊆ E) (s : SState) :
    srvDurInv γ rc i ∗ srvV rc s ⊢ |NC={E}=> srvV rc s ∗ termLb γ i s.term := by
  iintro ⟨#Hinv, Hv⟩ Hnc
  iunfold srvDurInv at Hinv
  icases Hinv with ⟨#Hinv, -⟩
  ihave Hacc := durAcc γ rc i hE $$ Hinv
  imod Hacc $$ Hnc with ⟨Hnc, HX, Hclose⟩
  unfold durBody srvV
  imod later_exists_except0 $$ HX with ⟨%X, HX⟩
  icases HX with ⟨Hsrv, Hdv, Hlc, >Htc, Hcc, >Hsv, Hrest⟩
  ihave %Hag := ghostVar_agree _ _ _ _ _ $$ Hsv Hv
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨hs, -, -⟩ := Hag
  subst hs
  ihave ⟨Htc, #Hlb⟩ := termCouple_get_lb (GF := GF) γ i X.s.term $$ Htc
  imod Hclose $$ [Hsrv Hdv Hlc Htc Hcc Hsv Hrest] with -
  · inext; iexists X; iframe
  imodintro
  iframe; iframe #

/-- `durFact` for a law of the shape `Inv ∗ srvOwn ∗ R ⊢ |={E∖durN}=> srvOwn ∗ P` (`R`, `P` inferred). -/
theorem durFactL (γ : GNames) (rc : RCtx GF) (i : SID) {E : CoPset} (hE : ↑durN ⊆ E) (s : SState)
    {R P : IProp GF} (h : Inv γ ∗ srvOwn γ i s ∗ R ⊢ |={E \ ↑durN}=> srvOwn γ i s ∗ P) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ R ⊢ |NC={E}=> srvV rc s ∗ P := by
  iintro ⟨#HI, #Hinv, Hv, HR⟩ Hnc
  iunfold srvDurInv at Hinv
  icases Hinv with ⟨#Hinv, -⟩
  ihave Hacc := durAcc γ rc i hE $$ Hinv
  imod Hacc $$ Hnc with ⟨Hnc, HX, Hclose⟩
  unfold durBody srvV
  imod later_exists_except0 $$ HX with ⟨%X, HX⟩
  icases HX with ⟨>Hsrv, Hdv, Hlc, Htc, Hcc, >Hsv, Hrest⟩
  ihave %Hag := ghostVar_agree _ _ _ _ _ $$ Hsv Hv
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨hs, -, -⟩ := Hag
  subst hs
  imod h $$ [HR Hsrv] with ⟨Hsrv, HP⟩
  · iframe; iframe #
  imod Hclose $$ [Hsrv Hdv Hlc Htc Hcc Hsv Hrest] with -
  · inext; iexists X; iframe
  imodintro
  iframe

/-- (hraft_robust R4b) **A crash-token update before a step**, as an entailment: run `P ⊢ |NC={E}=> Q`
before the next step of a non-value `e` (`wp_ncfupd`). A proof applies it with the law and the
continuation: `iapply wp_ncmod _ _ rfl (srvV_facts γ rc i s)`, then frames `P` and introduces `Q`. -/
theorem wp_ncmod {E : CoPset} (e : Expr) (Φ : val → IProp GF) (h : toVal e = none) {P Q : IProp GF}
    (hPQ : P ⊢ |NC={E}=> Q) :
    P ∗ (Q -∗ WP e @ E {{ Φ }}) ⊢ WP e @ E {{ Φ }} := by
  iintro ⟨HP, HW⟩
  iapply (wp_ncfupd _ _ h)
  iintro Hnc
  ihave H := hPQ $$ HP
  imod H $$ Hnc with ⟨Hnc, HQ⟩
  imodintro
  iframe Hnc
  iapply HW $$ HQ

variable [hRB : ReceiptBoundLe GF (2 ^ 62)] in
/-- `gprot.srvOwn_facts` through the view. -/
theorem srvV_facts (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ⊢ |NC={⊤}=> srvV rc s ∗ isSrv γ i ∗
      ⌜(s.log = [] ∨ ent s.log 1 = some γ.g) ∧ s.dur.1 ≤ s.log.length ∧ s.cidx ≤ s.dur.1 ∧
        s.vterm ≤ s.term ∧ (s.log ≠ [] → 1 ≤ s.term) ∧ s.term < 2 ^ 62 ∧ s.log.length < 2 ^ 62 ∧
        (∀ k e, ent s.log k = some e → e.kind = kConfig → cfgValid γ.srvs (γ.cv e.data)) ∧
        (∀ k e, ent s.log k = some e →
          e.kind = kCommand ∨ e.kind = kNoop ∨ e.kind = kBarrier ∨ e.kind = kConfig)⌝ := by
  have h := srvOwn_facts (GF := GF) γ (⊤ \ ↑durN) dvN_gprot_dur i s
  iintro ⟨#HI, #Hd, Hv⟩
  iapply durFact γ rc i (E := ⊤) (by solve_ndisj) s iprop(Inv γ) _ h $$ [$Hd $Hv $HI]

variable [hRB : ReceiptBoundLe GF (2 ^ 62)] in
/-- `gprot.llogIdx_leader` through the view. -/
theorem srvV_llogIdx_leader (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (k : Nat) (e : Entry) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ leaderIs γ s.term i ∗ llogIdx γ s.term k e ⊢
      |NC={⊤}=> srvV rc s ∗ ⌜ent s.log k = some e⌝ := by
  have h : iprop(Inv (GF := GF) γ ∗ leaderIs γ s.term i ∗ llogIdx γ s.term k e) ∗ srvOwn γ i s ⊢
      |={⊤ \ ↑durN}=> srvOwn γ i s ∗ ⌜ent s.log k = some e⌝ := by
    iintro ⟨⟨#HI, #Hl, #Hx⟩, Hs⟩
    iapply llogIdx_leader γ (⊤ \ ↑durN) dvN_gprot_dur i s k e
    iframe; iframe #
  iintro ⟨#HI, #Hd, Hv, #Hl, #Hx⟩
  iapply durFact γ rc i (E := ⊤) (by solve_ndisj) s _ _ h $$ [$Hd $Hv]
  iframe #

variable [hRB : ReceiptBoundLe GF (2 ^ 62)] in
/-- `gprot.srvOwn_durLb` through the view. -/
theorem srvV_durLb (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ⊢ |NC={⊤}=> srvV rc s ∗ durLb γ i s.dur.1 := by
  have h := srvOwn_durLb (GF := GF) γ (⊤ \ ↑durN) dvN_gprot_dur i s
  iintro ⟨#HI, #Hd, Hv⟩
  iapply durFact γ rc i (E := ⊤) (by solve_ndisj) s iprop(Inv γ) _ h $$ [$Hd $Hv $HI]

end dur

end github_com.hashicorp.raft

end Perennial
