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

theorem gprotN_diff_durN : (↑gprotN : CoPset) ⊆ ⊤ \ ↑durN := gprotN_diff_raft "dur"

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

end dur

end github_com.hashicorp.raft

end Perennial
