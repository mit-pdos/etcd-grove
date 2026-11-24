/-
The durability of the tree: a successful `fsync(2)` of a directory commits every entry of the tree's
log (`DirSync`, `Impl.lean`: ext4 commits the whole journal), and a crash keeps every committed
entry (`MachineCrash`). The ghost state records it as a persistent lower bound on the committed
prefix of the log (`osCommitLb n`: the first `n` entries are committed), held against the
authoritative bound of the state interpretation (`commitRes`, `Ghost.lean`); `wp_osDirSyncS`
(`TreeShared.lean`) gives it, and `crashRest_region'` turns it into what a crash keeps of a region.
Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeStepLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- The first `n` entries of the tree's log are committed: a crash keeps them (persistent). -/
def osCommitLb (n : Nat) : IProp GF := gCommitLb (gooseOsGS (L := L)) n

instance osCommitLb_persistent (n : Nat) : Persistent (osCommitLb (L := L) n) := by
  unfold osCommitLb; infer_instance

instance osCommitLb_timeless (n : Nat) : Timeless (osCommitLb (L := L) n) := by
  unfold osCommitLb; infer_instance

/-- A lower bound weakened. -/
theorem osCommitLb_le {n : Nat} (n' : Nat) (h : n' ≤ n) :
    ⊢ osCommitLb (L := L) n -∗ osCommitLb (L := L) n' := by
  unfold osCommitLb; exact gCommitLb_le _ n' h

/-- Nothing is a lower bound for free. -/
theorem osCommitLb_zero : ⊢ |==> osCommitLb (L := L) 0 := by
  unfold osCommitLb gCommitLb
  letI := (gooseOsGS (L := L)).osAllG
  exact monoNatLbOwn_0 _

/-- `commitRes` after a commit of the whole log: the bound raised to the log's length, and a lower
bound of it. -/
theorem commitRes_commitAll (st : OsState) :
    ⊢ commitRes (gooseOsGS (L := L)) st ==∗
      commitRes (gooseOsGS (L := L)) st.commitAll ∗ osCommitLb (L := L) st.fs.metaLog.length := by
  unfold commitRes osCommitLb
  iintro ⟨%c, %hc, Ha⟩
  imod gCommit_update _ c (max c st.fs.metaLog.length) (Nat.le_max_left _ _) $$ Ha with ⟨Ha, #Hlb⟩
  imodintro
  isplitl [Ha]
  · iexists (max c st.fs.metaLog.length)
    iframe Ha
    ipureintro
    intro y hy
    show st.fs.committed y ∨ y < st.fs.metaLog.length
    by_cases h : y < c
    · exact Or.inl (hc y h)
    · exact Or.inr (by omega)
  · iapply gCommitLb_le _ _ (Nat.le_max_right _ _) $$ Hlb

end specs

end Fs
end Perennial

end
