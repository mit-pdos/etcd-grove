/-
(hraft_robust rcl) Helper lemmas of `NewRaft`'s `restoreFromCommittedLogs` (`RestoreCommittedLogs` on): a
log-store read by the main goroutine after the boot that learns the written commit index is durable.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.CrashLaws
public import Dsverify.Proof.github_com.hashicorp.raft.DurHelpers

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

open proto gprot

section rcl
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

variable (γ : GNames) (rc : RCtx GF) (i : SID)

theorem rcl_dur_storeN : (↑durN : CoPset) ⊆ ⊤ \ ↑storeN := by
  unfold durN raftN storeN; solve_ndisj

/-- **A main-goroutine read of the log store** (any of its atomic updates that leaves the store as it is:
`LastIndex`, `GetCommitIndex`), over `srvDurInv` and the main goroutine's view at `s`: the commit index
the store wrote is durable (`durCore`'s `ci ≤ dur`). -/
theorem mainRead_L (s : SState) (Ψ : LogAbs → IProp GF) :
    srvDurInv γ rc i ∗ srvV rc s ∗ (srvV rc s -∗ ∀ A : LogAbs, ⌜uint.nat A.ci ≤ s.dur.1⌝ -∗ Ψ A) ⊢
      |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A, rc.ownL A ∗ (rc.ownL A ={∅, ⊤ \ ↑storeN}=∗ Ψ A) := by
  iintro ⟨#Hdur, Hv, HK⟩ Hnc
  ihave Hacc := durOpen γ rc i (E := ⊤ \ ↑storeN) rcl_dur_storeN $$ Hdur
  imod Hacc $$ Hnc with ⟨Hnc, %X, Hc, Hs, Hclose⟩
  ihave ⟨Hc, Hv, %Hag⟩ := durCore_srvV_agree γ rc i X s $$ [Hc Hv]
  · iframe
  iunfold durCore at Hc
  icases Hc with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, %Hp, Hrest⟩
  have hci : uint.nat X.A.ci ≤ s.dur.1 := by rw [← Hag.1]; exact Hp.2.2.2.2.1
  iunfold durStores at Hs
  icases Hs with ⟨HownL, Hs⟩
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iframe Hnc
  inext
  iexists X.A
  iframe HownL
  iintro HownL
  imod Hmask with -
  imod Hclose $$ %X [H1 H2 H3 H4 H5 H6 H7 H8 H9 Hrest] [HownL Hs] with -
  · iunfold durCore; iframe; ipureintro; exact Hp
  · inext; iunfold durStores; iframe
  imodintro
  iapply HK $$ Hv
  ipureintro; exact hci

end rcl

end github_com.hashicorp.raft

end Perennial
