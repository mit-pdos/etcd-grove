/-
Facts of `unix.Munmap`'s proof that other proofs use (`Proof/golang_org/x/sys/unix/Munmap.lean`,
`Proof/os/CrashStSpec.lean`, `Proof/os/CrashStILSpec.lean`): a defs module (`etc/tier-check.py`).
-/
module

public import GooseLang.Ext.Fs.Specs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- A mapping with a cell is at a positive address (its first cell's points-to says so). -/
theorem cellsR_pos (base : Loc) (n : Nat) (vf : Nat → val) (hn : 0 < n) :
    cellsR (GF := GF) base 0 n vf ⊢ cellsR (GF := GF) base 0 n vf ∗ ⌜0 < base.addr⌝ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  unfold cellsR
  rw [List.range'_succ]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H0, Hr⟩
  unfold heapPointsto
  icases H0 with ⟨%Hl, H0⟩
  isplitl [H0 Hr]
  · iapply BigSepL.bigSepL_cons.2
    iframe Hr
    iframe H0
    ipureintro; exact Hl
  · ipureintro
    have : (base +ₗ ((0 : Nat) : Int)) = base := by simp
    rw [this] at Hl; exact Hl.1

end facts

end EtcdGrove
end Perennial
