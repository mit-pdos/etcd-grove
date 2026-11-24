/-
The tree across a crash (`notes/wal-fsext-i2-design.md`, §4.2): what a region
concludes (`crashRest_region'`, from the crash's facts `crashShared` keeps and `regionCrashed_of_cut`)
and the new generation's tree (`crashRest_treeS'`, well formed: `crashRest_treeWf'`). `TreeShared.lean` states them and takes their
proofs from here. Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedSwitch
public import GooseLang.Ext.Fs.CrashRegion
public import GooseLang.Ext.Fs.CrashTok

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- The claims held, with their authority coherent with `V`: each is the history's. -/
theorem claims_lookup (L : GooseLocalGS GF) {V : Hist} {Γn : GMap (Ino × NameSet) NamesH}
    (hcoh : NamesCoh V Γn) :
    ∀ cl : List (Claim × DFrac),
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ osClaims L cl -∗
      ⌜∀ c ∈ cl, c.1.2.2 = namesOf V c.1.1 c.1.2.1⌝ ∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn ∗ osClaims L cl
  | [] => by
    iintro HA Hc
    iframe
    ipureintro; intro c hc; cases hc
  | c :: cl => by
    iintro HA Hc
    icases (osClaims_cons L c cl).1 $$ Hc with ⟨H1, Hc⟩
    icases osNames_auth L hcoh _ _ _ _ $$ HA H1 with %h1
    icases claims_lookup L hcoh cl $$ HA Hc with ⟨%hcl, HA, Hc⟩
    iframe HA
    isplitr
    · ipureintro
      intro c' hc'
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact h1
      · exact hcl c' hc'
    iapply (osClaims_cons L c cl).2
    iframe

/-- The claims held are one log's (their entries its entries), a log whose entries' calls began no
later than they took effect (`NamesCoh.starts`). -/
theorem osClaims_log' (L : GooseLocalGS GF) (R : Roots) (cl : List (Claim × DFrac)) (E : CoPset)
    (hE : ↑osShN ⊆ E) :
    osSharedInv (L := L) R -∗ osClaims L cl ={E}=∗ osClaims L cl ∗
      ⌜∃ log : List LogEntry, Starts log ∧
        ∀ c ∈ cl, ∀ x e Es, (x, e, Es) ∈ c.1.2.2.ents → log[x]? = some e⌝ := by
  unfold osSharedInv
  iintro #Hsi Hc
  imod inv_acc hE $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases claims_lookup L hcoh.2 cl $$ HAn Hc with ⟨%hcl, HAn, Hc⟩
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists Vs, Γn; iframe; ipureintro; exact hcoh
  imodintro
  iframe Hc
  ipureintro
  refine ⟨Vs.2, hcoh.2.starts, fun c hc x e Es hx => ?_⟩
  rw [hcl c hc, namesOf_ents] at hx
  obtain ⟨x0, hx0, hxe⟩ := List.mem_map.1 hx
  simp only [Prod.mk.injEq] at hxe
  obtain ⟨rfl, rfl, -⟩ := hxe
  have hxL : x0 < Vs.2.length := List.mem_range.1 (List.mem_filter.1 hx0).1
  simp [List.getElem?_eq_getElem hxL]

theorem crashRest_region' (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (R : Roots) (cl : List (Claim × DFrac)) (n : Nat) (E : CoPset)
    (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R -∗ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗
      osClaims L cl -∗ osCommitLb (L := L) n ={E}=∗
      ⌜RegionCrashed (cl.map (·.1)) n V'.now⌝ ∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' ∗ osClaims L cl := by
  iintro #Hsi Hr Hcl #Hlb
  unfold crashRest
  icases Hr with ⟨%Γb, %Γm, %F, %st, %st', %Γf, %Γt, %hrel, Hab, Ham, Hfs, HAt, Htok, Htl, Hcc⟩
  unfold crashShared
  icases Hcc with ⟨Has, %hsh, Hcm⟩
  obtain ⟨hwf0, hst, S, hSlt, hcl, hSc, hslot⟩ := hsh
  unfold commitRes
  icases Hcm with ⟨%c, %hc, Hc⟩
  unfold osCommitLb
  icases gCommitLb_valid _ c n $$ Hc Hlb with %hn
  unfold osSharedInv
  imod inv_acc hE $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %hVs
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hVs
  obtain ⟨hR, rfl⟩ := hVs
  icases claims_lookup L hcoh.2 cl $$ HAn Hcl with ⟨%hlk, HAn, Hcl⟩
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
  imodintro
  iframe Hcl
  isplitr
  · ipureintro
    refine regionCrashed_of_cut (V := (st.fs.treeDur, st.fs.metaLog)) hst hcl
      (fun y hy => hSc y (hc y hy)) hn hslot _ ?_
    intro cc hcc
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hcc
    exact hlk c0 hc0
  iexists Γb, Γm, F, st, st', Γf, Γt
  iframe Hab Ham Hfs HAt Htok Htl Has
  isplitr
  · ipureintro; exact hrel
  isplitr
  · ipureintro; exact ⟨hwf0, hst, S, hSlt, hcl, hSc, hslot⟩
  iexists c
  iframe Hc
  ipureintro; exact hc

/-- The new generation's tree is well formed over the shared invariant's roots (`closed_cut`, which
`crashShared` keeps). -/
theorem crashRest_treeWf' (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (R : Roots) (E : CoPset) (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' ={E}=∗
      ⌜TreeWf R V'.now⌝ ∗ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' := by
  iintro #Hsi Hr
  unfold crashRest
  icases Hr with ⟨%Γb, %Γm, %F, %st, %st', %Γf, %Γt, %hrel, Hab, Ham, Hfs, HAt, Htok, Htl, Hcc⟩
  unfold crashShared
  icases Hcc with ⟨Has, %hsh, Hcm⟩
  unfold osSharedInv
  imod inv_acc hE $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %hVs
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hVs
  obtain ⟨hR, rfl⟩ := hVs
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
  imodintro
  isplitr
  · ipureintro; rw [← hR]; exact hsh.1
  iexists Γb, Γm, F, st, st', Γf, Γt
  iframe Hab Ham Hfs HAt Htok Htl Has Hcm
  isplitr
  · ipureintro; exact hrel
  ipureintro; exact hsh

/-- **The new generation's tree**: its shared invariants, allocated from the tree resources the
restart holds (`osSwitchKit_open`), on the old shared invariant's roots (which are the crashed
state's, and the new state's). -/
theorem crashRest_treeS' (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (V' : Hist) (R : Roots) (E : CoPset) (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D false V' ={E}=∗
      ⌜V'.2 = []⌝ ∗ osShared (L := L') R V' ∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D true V' := by
  iintro #Hsi Hr
  unfold crashRest
  icases Hr with ⟨%Γb, %Γm, %F, %st, %st', %Γf, %Γt, %hrel, Hab, Ham, Hfs, HAt, Htok, Htl, Hcc⟩
  unfold crashShared
  icases Hcc with ⟨Has, %hsh, Hcm⟩
  unfold osSharedInv
  imod inv_acc hE $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %hVs
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hVs
  obtain ⟨hR, rfl⟩ := hVs
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
  unfold treeLeft
  rw [← hR]
  imod osSwitchKit_open (L := L') st.fs.roots V' E $$ Htl with Hsh
  imodintro
  iframe Hsh
  isplitr
  · ipureintro; rw [hrel.2.2.2.2.2.2.1]
  iexists Γb, Γm, F, st, st', Γf, Γt
  iframe Hab Ham Hfs HAt Htok Has Hcm
  isplitr
  · ipureintro; exact hrel
  ipureintro; exact hsh

end crash

end Fs
end Perennial

end
