/-
The shared mode of the tree across a crash (`notes/wal-fsext-i2-design.md`, §4.2): what a region
concludes (`crashRest_region'`, from the crash's facts `crashShared` keeps and `regionCrashed_of_cut`)
and the new generation's tree (`crashRest_treeS'`). `TreeShared.lean` states them and takes their
proofs from here. Untrusted.
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

/-- In the legacy mode the restart holds the shared history's authority empty: no shared
invariant is the generation's. -/
theorem sharedInv_legacy_excl (L : GooseLocalGS GF) (R : Roots) (E : CoPset) (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γs (∅ : GMap Unit (Roots × Hist)) ={E}=∗
      False := by
  unfold osSharedInv
  iintro #Hsi Has
  imod inv_acc hE $$ Hsi with ⟨Hi, -⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, -⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %h
  simp at h

theorem crashRest_region' (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (R : Roots) (cl : List (Claim × DFrac)) (n : Nat) (E : CoPset)
    (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R -∗ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗
      osClaims L cl -∗ osCommitLb (L := L) n ={E}=∗
      ⌜RegionCrashed (cl.map (·.1)) n V'.now⌝ ∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' ∗ osClaims L cl := by
  iintro #Hsi Hr Hcl #Hlb
  unfold crashRest
  icases Hr with ⟨%Γb, %Γm, %F, %st, %st', %Γf, %Γt, %V, %hrel, Hab, Ham, Hfs, HAt, Htok, HAd,
    Htl, Hcc⟩
  unfold crashMode
  icases Hcc with (⟨Hcc, Has⟩ | Hcc)
  · imod sharedInv_legacy_excl L R E hE $$ Hsi Has with %h
    exact h.elim
  unfold crashShared
  icases Hcc with ⟨Hd, Has, %hsh, Hcm⟩
  obtain ⟨hst, S, hSlt, hcl, hSc, hslot⟩ := hsh
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
  iexists Γb, Γm, F, st, st', Γf, Γt, V
  iframe Hab Ham Hfs HAt Htok HAd Htl
  isplitr
  · ipureintro; exact hrel
  iright
  iframe Hd Has
  isplitr
  · ipureintro; exact ⟨hst, S, hSlt, hcl, hSc, hslot⟩
  iexists c
  iframe Hc
  ipureintro; exact hc

theorem crashRest_treeS' (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (V' : Hist) (R : Roots) (E : CoPset) (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D false V' ={E}=∗
      ⌜V'.2 = []⌝ ∗ osTree (L := L') (DFrac.own 1) R V' ∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D true V' := by
  iintro #Hsi Hr
  unfold crashRest
  icases Hr with ⟨%Γb, %Γm, %F, %st, %st', %Γf, %Γt, %V, %hrel, Hab, Ham, Hfs, HAt, Htok, HAd,
    Htl, Hcc⟩
  unfold crashMode
  icases Hcc with (⟨Hcc, Has⟩ | Hcc)
  · imod sharedInv_legacy_excl L R E hE $$ Hsi Has with %h
    exact h.elim
  unfold crashShared
  icases Hcc with ⟨Hd, Has, %hsh, Hcm⟩
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
  unfold treeLeft osTree
  rw [← hR]
  iframe Htl
  isplitr
  · ipureintro; exact treeCrashed_log hrel.2.2.2.2.2.2.1
  iexists Γb, Γm, F, st, st', Γf, Γt, V
  iframe Hab Ham Hfs HAt Htok HAd
  isplitr
  · ipureintro; exact hrel
  isplitr
  · iempintro
  iright
  iframe Hd Has Hcm
  ipureintro; exact hsh

end crash

end Fs
end Perennial

end
