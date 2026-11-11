/-
Crash reasoning for the durable-state extension (WAL W4a, 2026-11-11; the W4 Draft's §5): its crash
interpretation. The files survive a crash unchanged (`durable_semantics`), so the new generation
keeps the old generation's ghost variable (`crashStart old new := ⌜new = old⌝`, as Perennial's
`fs_crash_interp`), and the old generation's `durableOwn fs` is the new one's.
-/
module

public import Perennial.GooseLang.CrashAdequacy
public import GooseLang.Ext.Durable.Specs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- The durable state keeps its ghost state across a crash. -/
instance durable_crash_interp : ExtCrashInterp durableExt where
  crashStart hL hL' := iprop(⌜hL' = hL⌝)
  local_crash _ _ hL σ σ' h := by
    obtain rfl := (show σ' = σ from h)
    iintro H
    imodintro
    iexists hL
    iframe H
    ipureintro; rfl

section gen
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- The old generation's files are the new one's. -/
theorem durableOwn_crash (L L' : GooseLocalGS GF) (fs : DurableState) :
    ⊢@{IProp GF} durable_crash_interp.crashStart (gooseDurableGS (L := L)) (gooseDurableGS (L := L'))
      -∗ durableOwn (L := L) fs -∗ durableOwn (L := L') fs := by
  iintro Hc H
  ihave %h : ⌜gooseDurableGS (L := L') = gooseDurableGS (L := L)⌝ $$ [Hc]
  · iexact Hc
  unfold durableOwn
  rw [h]
  iexact H

end gen

end Perennial
