/-
The shared mode of the tree: the laws of its resources (`TreeShared.lean` states them and takes
their proofs from here). Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedSwitch
public import GooseLang.Ext.Fs.CrashRegion

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- A claim knows of no entry past the log. -/
theorem namesOf_next_le (V : Hist) (j : Ino) (N : NameSet) : (namesOf V j N).next ≤ V.2.length := by
  unfold NamesH.next
  cases hl : (namesOf V j N).ents.getLast? with
  | none => simp
  | some xe =>
    have hm := List.mem_of_getLast? hl
    rw [namesOf_ents] at hm
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm
    have := List.mem_range.1 (List.mem_filter.1 hx).1
    simp only [Option.map_some, Option.getD_some]
    omega

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {E : CoPset}

theorem osNames_next' (R : Roots) (j : Ino) (N : NameSet) (dq : DFrac) (h : NamesH)
    (hE : ↑osShN ⊆ E) :
    osSharedInv (L := L) R -∗ osNames (L := L) j N dq h ={E}=∗
      osNames (L := L) j N dq h ∗ osLogLb (L := L) h.next := by
  unfold osSharedInv
  iintro #Hsi H
  imod inv_acc hE $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases osNames_auth L hcoh.2 _ _ _ _ $$ HAn H with %hh
  ihave #Hlb := (letI := (gooseOsGS (L := L)).osAllG; monoNatLbOwn_get _ _ _) $$ Halen
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists Vs, Γn; iframe; ipureintro; exact hcoh
  imodintro
  iframe H
  unfold osLogLb
  iapply (letI := (gooseOsGS (L := L)).osAllG;
    monoNatLbOwn_le (γ := (gooseOsGS (L := L)).γlen) h.next (hh ▸ namesOf_next_le Vs j N)) $$ Hlb

end laws

end Fs
end Perennial

end
