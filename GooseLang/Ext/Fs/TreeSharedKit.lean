/-
**The mode switch in two halves** (wal-safe, 2026-11-21; `notes/wal-units/tester.md`, twelfth session):
`wp_osShareE`'s switch (`TreeSharedSwitchE.lean`) split into its ghost updates on the tree's
interpretation (`treeCtx_switchG`, a basic update over any `OsGS`, so that a crash interpretation can
run it on the new generation: `CrashShared.lean`) and the allocation of the two invariants
(`osSwitchKit_open`). Between the two the switch's resources are `osSwitchKitG`. With them:
`wp_osShareE_acc`, the switch whose tree comes from an accessor (an invariant opened around it), so
that a crash before the switch can still be handled from the invariant. `wp_osShareE` itself is
unchanged. Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedSwitchE

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## The switch's ghost updates, over any generation's ghost names -/

theorem histMap_insert_emptyG (RV : Roots × Hist) :
    (<[() := RV]> (∅ : GMap Unit (Roots × Hist))) = histMap RV := by
  apply GMap.ext; intro u; cases u; simp [histMap]

section kitG
variable {GF : BundledGFunctors} (hL : OsGS GF)

/-- The directories of the tree, each once. -/
abbrev dirsOf (V : Hist) : List Ino := (GMap.toList V.now).map (·.1)

/-- **The switch's resources before its invariants are allocated**: what the shared invariant holds
(the shared history `(R, V)`, the claims' authority, the log's length and map), the call permission of
key `[]` (the dispenser's), every other root's whole call permission, the log's lower bound, and a
whole claim on all names of every directory. -/
def osSwitchKitG (R : Roots) (V : Hist) : IProp GF :=
  iprop(gElem hL hL.γs () (DFrac.own 1) (R, V) ∗
    gAuth hL hL.γn (claimsInit V (dirsOf V)) ∗ ⌜RootsOk R ∧ NamesCoh V (claimsInit V (dirsOf V))⌝ ∗
    (letI := hL.osAllG; monoNatAuthOwn hL.γlen 1 V.2.length) ∗ gAuth hL hL.γlog (logMap V.2) ∗
    gElem hL hL.γperm ([] : GoString) (DFrac.own 1) () ∗
    ([∗map] r ↦ u ∈ GMap.delete [] (permMap R), gElem hL hL.γperm r (DFrac.own 1) u) ∗
    (letI := hL.osAllG; monoNatLbOwn hL.γlen V.2.length) ∗
    [∗list] j ∈ dirsOf V, gElem hL hL.γn (j, NameSet.except []) (DFrac.own 1) (namesOf V j (.except [])))

/-- The holder of the whole history knows that no directory fd is open and no call is in flight
(`whole_alone`, over any generation's ghost names). -/
theorem whole_aloneG (R : Roots) (V : Hist) (Γdf : GMap w64 (Ino × DirPh)) (Γc : GMap Nat CallV) :
    ⊢ gElem hL hL.γd () (DFrac.own 1) (R, V) -∗ rdRes hL Γdf -∗ callRes hL Γc -∗
      ⌜Γdf = ∅ ∧ Γc = ∅⌝ ∗ gElem hL hL.γd () (DFrac.own 1) (R, V) ∗ rdRes hL Γdf ∗ callRes hL Γc := by
  iintro Hd Hrd Hcr
  by_cases h1 : Γdf = ∅
  · by_cases h2 : Γc = ∅
    · iframe; ipureintro; exact ⟨h1, h2⟩
    · have : ∃ t x, Γc !! t = some x := by
        refine Classical.byContradiction fun hn => h2 (GMap.ext fun t => ?_)
        cases h : Γc !! t with
        | none => rfl
        | some x => exact absurd ⟨t, x, h⟩ hn
      obtain ⟨t, x, hx⟩ := this
      unfold callRes
      icases (BigSepM.bigSepM_lookup (Φ := fun (_t : Nat) (x : CallV) =>
          iprop(∃ RV : Roots × Hist, gElem hL hL.γd () (DFrac.own x.2) RV)) hx) $$ Hcr with ⟨%RV, Hq⟩
      icases gElem_valid_2 _ _ _ _ _ _ _ $$ Hd Hq with %Hv
      exact absurd (DFrac.valid_own_op Hv.1) (by simp)
  · have : ∃ fd x, Γdf !! fd = some x := by
      refine Classical.byContradiction fun hn => h1 (GMap.ext fun t => ?_)
      cases h : Γdf !! t with
      | none => rfl
      | some x => exact absurd ⟨t, x, h⟩ hn
    obtain ⟨fd, x, hx⟩ := this
    unfold rdRes
    icases (BigSepM.bigSepM_lookup (Φ := fun (_ : w64) (x : Ino × DirPh) => rdPart hL x) hx) $$ Hrd
      with Hq
    unfold rdPart
    icases Hq with ⟨%RV, Hq, -⟩
    icases gElem_valid_2 _ _ _ _ _ _ _ $$ Hd Hq with %Hv
    exact absurd (DFrac.valid_own_op Hv.1) (by simp)

/-- **The switch's ghost updates** (`wp_osShareE`'s, without its invariants): the whole legacy history
`(R, V)` and the tree's interpretation in the legacy mode become the interpretation in the shared mode
and `osSwitchKitG`; `(R, V)` is the state's roots and history. -/
theorem treeCtx_switchG (st : OsState) (R : Roots) (V : Hist) :
    ⊢ gElem hL hL.γd () (DFrac.own 1) (R, V) -∗ treeCtx hL st ==∗
      treeCtx hL st ∗ osSwitchKitG hL R V ∗ ⌜R = st.fs.roots ∧ V = (st.fs.treeDur, st.fs.metaLog)⌝ := by
  iintro Hh Ht
  unfold treeCtx
  icases Ht with ⟨Hm, Hcm⟩
  icases Hm with (Hm | Hm)
  rotate_left
  · unfold treeShared
    icases Hm with ⟨%V0, %s0, %Γdf, %Γc, %Γg, %hw, -, Hd, -⟩
    icases gElem_valid_2 _ _ _ _ _ _ _ $$ Hh Hd with %Hv
    exact absurd (DFrac.valid_op_own Hv.1) (by simp)
  unfold treeLegacy legacyHolds
  icases Hm with ⟨%V0, %Γdf, %Γc, %hns, HAd, HAdf, HAc, Hrd, Hcr, Has, Hadfs, Hacs, Hperm, Han,
    Halen, Halog, Hag⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ HAd Hh with %Heq
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl⟩ := Heq
  icases whole_aloneG hL _ _ Γdf Γc $$ Hh Hrd Hcr with ⟨%Hal, Hh, -, -⟩
  obtain ⟨hdf, hcl⟩ := Hal
  have hcohS := cohS_switch hns.1 hns.2 hdf hcl
  have hV : V0 = (st.fs.treeDur, st.fs.metaLog) := hns.2.hist
  subst hdf hcl
  imod gAuth_insert _ _ _ () (st.fs.roots, V0) (by rfl) $$ Has with ⟨Has, Hs⟩
  rw [histMap_insert_emptyG]
  imod (letI := hL.osAllG; mono_nat_own_update (γ := hL.γlen) V0.2.length (Nat.zero_le _)) $$ Halen
    with ⟨Halen, #Hlb⟩
  imod log_alloc hL V0.2 $$ Halog with Halog
  imod perm_alloc hL st.fs.roots $$ Hperm with Hperm
  icases (BigSepM.bigSepM_delete (M := GMap GoString)
    (Φ := fun (r' : GoString) (u : Unit) => gElem hL hL.γperm r' (DFrac.own 1) u)
    (permMap_lookup st.fs.roots [] (.inl rfl))).1 $$ Hperm with ⟨Hp0, Hperm⟩
  imod claims_alloc hL V0 _ (GMap.toList_keys_nodup _) $$ Han with ⟨Han, Hcl⟩
  imodintro
  isplitl [HAd Hh HAdf HAc Has Hadfs Hacs Hag Hcm]
  · iframe Hcm
    iright
    unfold treeShared
    iexists V0, st.fs.metaLog.length, ∅, ∅, ∅
    rw [← hV]
    iframe HAd Hh HAdf HAc Has Hadfs Hacs Hag
    isplitr
    · ipureintro; exact ⟨hns.1, hcohS⟩
    unfold callResS
    isplitl []
    · iapply BigSepM.bigSepM_empty.2; itrivial
    · iapply BigSepM.bigSepM_empty.2; itrivial
  isplitl
  · unfold osSwitchKitG
    iframe Hs Han Halen Halog Hp0 Hperm Hlb Hcl
    ipureintro
    exact ⟨hns.1.roots, namesCoh_init V0 (by rw [hV]; exact hcohS.starts)⟩
  · ipureintro; exact ⟨rfl, hV⟩

end kitG

/-! ## The invariants, and the switch through an accessor -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **What the shared mode's switch gives** (`wp_osShareE`'s continuation's resources): the shared
invariant, the dispenser of key `[]`, every other root's whole call permission, the log's lower
bound, a whole claim on all names of every directory of the tree. -/
def osShared (R : Roots) (V : Hist) : IProp GF :=
  iprop(osSharedInv (L := L) R ∗ osAboveInv (L := L) ∗ osCallPerms (L := L) R ∗
    osLogLb (L := L) V.2.length ∗
    [∗list] j ∈ dirsOf V, osNames (L := L) j (.except []) (DFrac.own 1) (namesOf V j (.except [])))

/-- **The switch's invariants**: `osSwitchKitG`'s resources for `osShared`. -/
theorem osSwitchKit_open (R : Roots) (V : Hist) (E : CoPset) :
    ⊢ osSwitchKitG (gooseOsGS (L := L)) R V ={E}=∗ osShared (L := L) R V := by
  unfold osSwitchKitG
  iintro ⟨Hs, Han, %hok, Halen, Halog, Hp0, Hperm, #Hlb, Hcl⟩
  imod inv_alloc osAbN E iprop(∃ q, osCallPerm (L := L) [] q) $$ [Hp0] with #Hab
  · inext; iexists 1; unfold osCallPerm; iexact Hp0
  imod inv_alloc osShN E iprop(∃ (Vs : Hist) (Γn : GMap (Ino × NameSet) NamesH),
    gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γs () (DFrac.own 1) (R, Vs) ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn ∗ ⌜RootsOk R ∧ NamesCoh Vs Γn⌝ ∗
    (letI := (gooseOsGS (L := L)).osAllG; monoNatAuthOwn (gooseOsGS (L := L)).γlen 1 Vs.2.length) ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γlog (logMap Vs.2)) $$ [Hs Han Halen Halog]
    with #Hsi
  · inext
    iexists V, (claimsInit V (dirsOf V))
    iframe Hs Han Halen Halog
    ipureintro; exact hok
  imodintro
  unfold osShared
  simp only [osNames_except]
  unfold osSharedInv osAboveInv osCallPerms osCallPerm osLogLb
  iframe Hsi Hab Hperm Hlb Hcl

/-- **The mode switch through an accessor**: as `wp_osShareE`, the whole legacy history coming from an
update to the mask `E'` (an invariant opened), which gets back to `E` with the switch's resources
(the invariant closed with something else). -/
theorem wp_osShareE_acc (e : Expr) (he : toVal e = none) (E' : CoPset) (Φ : val → IProp GF) :
    ⊢ (|={E, E'}=> ∃ (R : Roots) (V : Hist), osTree (L := L) (DFrac.own 1) R V ∗
        (osShared (L := L) R V ={E', E}=∗ WP e @ s; E {{ Φ }})) -∗
      WP e @ s; E {{ Φ }} := by
  iintro Hacc
  iapply wp_ext_acc (X := fsExt) e Φ he
  iintro %σ %g Hl Hg
  icases (os_local_ctx_eq σ).mp $$ Hl with Hl
  unfold osCtx
  icases Hl with ⟨HF, Ht, Hof⟩
  imod Hacc with ⟨%R, %V, Hh, Hk⟩
  unfold osTree
  imod treeCtx_switchG (gooseOsGS (L := L)) σ R V $$ Hh Ht with ⟨Ht, Hkit, -⟩
  imod osSwitchKit_open R V E' $$ Hkit with Hsh
  imod Hk $$ Hsh with Hwp
  imodintro
  iframe Hg Hwp
  iapply (os_local_ctx_eq σ).mpr
  unfold osCtx
  iframe

end specs

end Fs
end Perennial
