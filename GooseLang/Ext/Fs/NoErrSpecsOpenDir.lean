/-
What the program logic may use of the premises **no I/O error** (`NoIoErr`) and **no error of the
lock, mapping and descriptor calls** (`NoMapLockErr`) on `open(2)` read-only of a covered directory in
the shared mode: its call has a success from every free fd (`openDir_succ`, `OpenEffect`'s directory
case), so a failing step fails only with `EINTR` (`open_failure_eintr`), which the models of `open`
retry (`wp_osOpenDirSNE`). As `NoErrSpecsOpenFile.lean` for a file. Untrusted.
-/
module

public import GooseLang.Ext.Fs.NoErrSpecsOpenFile
public import GooseLang.Ext.Fs.TreeShared

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- The directory of a path that fits fits (a prefix of it). -/
theorem pathFits_of_child {d b : GoString} (h : PathFits (child d b)) : PathFits d :=
  have hp : d <+: child d b := ⟨_ :: b, rfl⟩
  ⟨Nat.lt_of_le_of_lt hp.length_le h.1, fun s hs hl => h.2 s (hs.trans hp.isInfix) hl⟩

section step
variable [GooseExts] [GoGlobalContext] [go.BasicIntoValInj]

/-- **`open(2)` read-only of the directory `p` has a success from every free fd** (`OpenEffect`'s
directory case: read-only, no `O_CREAT`, no `O_TRUNC`). -/
theorem openDir_succ {st : OsState} {p : GoString} {j : Ino} {k s0 : Nat}
    (hcall : st.proc.calls !! k = some (s0, p)) (hl : st.lookup p = some (.dir j)) :
    ∀ fd, FdFree st fd →
      ∃ st'', IsFsStep "Open" (PairV (osTokV k) (PairV (#p) (#flRO))) st (osRes (#fd) 0) st'' := by
  intro fd hfree
  have hl0 : (st.metaEnd k).lookup p = some (.dir j) := hl
  refine ⟨_, .inl ⟨p, flRO, k, s0, rfl, treePath_of_lookup hl, flRO_ok, hcall,
    fun h => absurd h (by decide), .inl ⟨st.metaEnd k, .dir j, fd, ?_, hfree, rfl, rfl⟩⟩⟩
  unfold OpenEffect
  rw [hl0]
  exact ⟨by decide, by decide, by decide, rfl, rfl⟩

end step

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [S : ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **`open(2)` read-only of the directory `p` with no error** (shared mode, a spine to it; `p`
covered): `wp_osOpenDirS'`, a failure's errno `EINTR`. -/
theorem wp_osOpenDirSNE (Sio : IoSet) [FsStepSat (NoIoErr Sio)] [FsStepSat (NoMapLockErr Sio)]
    (R : Roots) (p : GoString) (j : Ino) (dq : DFrac) (k s0 : Nat) (q : Qp)
    (hS : Sio.path p ∧ PathFits p) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R p dq j -∗
      osCallS (L := L) k s0 p q -∗
      (∀ fd : w64, ∀ e : w64, ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ fd = -1 ∧ e = EINTR)⌝ -∗
        osCallPerm (L := L) (callKey R p) q -∗
        osPathS (L := L) R p dq j -∗ (⌜e = 0⌝ -∗ osDirFdS (L := L) fd j .idle) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#p) (#flRO))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv #Hsi Hp Hk HΦ
  iapply wp_osOpenDirGenSQ R p j (osPathS (L := L) R p dq j) k s0 q
    (fun _ Γn _ hR hcoh => osPathS_lookup hR hcoh p dq j) hE hE' Φ (· = EINTR)
    (fun _st _e' _st' hcall hl Hst Hsem => by
      obtain ⟨hh, hh', Hsem⟩ := Hsem
      exact open_failure_eintr hS (openDir_succ hcall hl) Hst Hsem) $$ Hinv Hsi Hp Hk
  iintro %fd %e %hres Hq Hp Hfd
  iapply HΦ $$ %fd %e [] Hq Hp Hfd
  ipureintro
  rcases hres with h0 | ⟨h1, -, h3, h4⟩
  · exact .inl h0
  · exact .inr ⟨h1, h3, h4⟩

end specs

end Fs
end Perennial

end
