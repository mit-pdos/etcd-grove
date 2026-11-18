/-
`cellsR_pos` (a mapping with a cell is at a positive address), out of `Munmap.lean`'s proof so
that `os/CrashStSpec.lean` imports it without the proof (import tiers, 2026-11-18).
-/
module

public import Spec.golang_org.x.sys.unix.Munmap
public import Perennial.Golang.Theory.Unsafe

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [golang_org.x.sys.unix.Assumptions]

omit [HasExt Fs.fsExt] [sem : go.Semantics] [golang_org.x.sys.unix.Assumptions] in
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


end proof

end EtcdGrove
end Perennial
