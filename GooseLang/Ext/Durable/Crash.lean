/-
Crash reasoning for the durable-state extension (WAL W4a, 2026-11-11; the W4 Draft's §5): its crash
interpretation. The files survive a crash unchanged (`durable_semantics`), so the new generation
keeps the old generation's ghost variable (`crashStart old new := ⌜new = old⌝`, as Perennial's
`fs_crash_interp`), and the old generation's `durableOwn fs` is the new one's.

The WAL area's reservation (2026-11-11; its authority and invariant in the interpretation since
2026-11-12) keeps its ghost name too, and the crash gives no start resources (the unreserved
element `() ↪ none` is minted only at the first start, `durable_local_init`), so it is never
re-minted: the program carries its ownership across the crash
in whichever mode it is (`durableOwnM_crash`), and a reserved area stays reserved, with its
persistent `durableReserved r` (`durableReserved_crash`).
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

/-- The old generation's reservation is the new one's. -/
theorem durableReserved_crash (L L' : GooseLocalGS GF) (r : GoString) :
    ⊢@{IProp GF} durable_crash_interp.crashStart (gooseDurableGS (L := L)) (gooseDurableGS (L := L'))
      -∗ durableReserved (L := L) r -∗ durableReserved (L := L') r := by
  iintro Hc H
  ihave %h : ⌜gooseDurableGS (L := L') = gooseDurableGS (L := L)⌝ $$ [Hc]
  · iexact Hc
  unfold durableReserved
  rw [h]
  iexact H

/-- The old generation's files, in the area `r` reserved, are the new one's. -/
theorem durableOwnR_crash (L L' : GooseLocalGS GF) (r : GoString) (fs : DurableState) :
    ⊢@{IProp GF} durable_crash_interp.crashStart (gooseDurableGS (L := L)) (gooseDurableGS (L := L'))
      -∗ durableOwnR (L := L) r fs -∗ durableOwnR (L := L') r fs := by
  iintro Hc H
  ihave %h : ⌜gooseDurableGS (L := L') = gooseDurableGS (L := L)⌝ $$ [Hc]
  · iexact Hc
  unfold durableOwnR durableReserved
  rw [h]
  iexact H

/-- The old generation's files, in the mode `o`, are the new one's (in the same mode). -/
theorem durableOwnM_crash (L L' : GooseLocalGS GF) (o : Option GoString) (fs : DurableState) :
    ⊢@{IProp GF} durable_crash_interp.crashStart (gooseDurableGS (L := L)) (gooseDurableGS (L := L'))
      -∗ durableOwnM (L := L) o fs -∗ durableOwnM (L := L') o fs := by
  cases o <;> simp only [durableOwnM]
  · exact durableOwn_crash L L' fs
  · exact durableOwnR_crash L L' _ fs

end gen

end Perennial
