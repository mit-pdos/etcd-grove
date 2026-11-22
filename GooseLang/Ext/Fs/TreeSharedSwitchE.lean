/-
**The mode switch at any step** (S3e, 2026-11-17; per-root resources since wal-link's L4, merged
2026-11-19): `wp_osShare'` (`TreeSharedSwitch.lean`) at the step of any expression that is not a
value, not only an operation of the extension. The switch reads and rewrites only the extension's part
of the state interpretation, which every step of the program gives access to (`wp_ext_acc`), so it may
be done before the program's first step: a closed theorem that starts in the legacy mode (`fs_start`'s
whole tree) switches at once, before handing the proof of its program the shared mode's claims
(`Proof/runtime/StartFiles.lean`; the etcd examples' closed theorems, which allocate their WAL areas at
adequacy). Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedSwitch

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **The mode switch, at the extension's state interpretation** (the core of `wp_osShareE`): the
whole legacy history `V` for the shared mode's resources, the interpretation of the local state `σ`
kept; at any mask `E` (it allocates `osAbN`'s and `osShN`'s invariants). -/
theorem osShare_ctx (R : Roots) (V : Hist) (σ : OsState) :
    ⊢ osTree (L := L) (DFrac.own 1) R V -∗
      fs_interp.localCtx (extLocalGS fsExt) σ ={E}=∗
      fs_interp.localCtx (extLocalGS fsExt) σ ∗
      osSharedInv (L := L) R ∗ osAboveInv (L := L) ∗ osCallPerms (L := L) R ∗
      osLogLb (L := L) V.2.length ∗
      ([∗list] j ∈ (GMap.toList V.now).map (·.1),
        osNames (L := L) j (.except []) (DFrac.own 1) (namesOf V j (.except []))) := by
  iintro Hh Hl
  icases (os_local_ctx_eq σ).mp $$ Hl with Hl
  unfold osCtx
  icases Hl with ⟨HF, Ht, Hof⟩
  icases treeCtx_legacy _ (legacyWit_tree _ _ _) σ $$ Hh Ht with ⟨Hh, Ht, Hcm⟩
  unfold treeLegacy legacyHolds
  icases Ht with ⟨%V0, %Γdf, %Γc, %hns, HAd, HAdf, HAc, Hrd, Hcr, Has, Hadfs, Hacs, Hperm, Han,
    Halen, Halog, Hag⟩
  icases osTree_auth _ _ _ _ _ $$ HAd Hh with %Heq
  obtain ⟨rfl, rfl⟩ := Heq
  icases whole_alone _ _ Γdf Γc $$ Hh Hrd Hcr with ⟨%Hal, Hh, -, -⟩
  obtain ⟨hdf, hcl⟩ := Hal
  have hcohS := cohS_switch hns.1 hns.2 hdf hcl
  have hV : V = (σ.fs.treeDur, σ.fs.metaLog) := hns.2.hist
  subst hdf hcl
  imod gAuth_insert _ _ _ () (σ.fs.roots, V) (by rfl) $$ Has with ⟨Has, Hs⟩
  rw [histMap_insert_empty]
  imod (letI := (gooseOsGS (L := L)).osAllG;
    mono_nat_own_update (γ := (gooseOsGS (L := L)).γlen) V.2.length (Nat.zero_le _)) $$ Halen
    with ⟨Halen, #Hlb⟩
  imod log_alloc _ V.2 $$ Halog with Halog
  imod perm_alloc _ σ.fs.roots $$ Hperm with Hperm
  icases (BigSepM.bigSepM_delete (M := GMap GoString)
    (Φ := fun (r' : GoString) (u : Unit) => gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm r'
      (DFrac.own 1) u) (permMap_lookup σ.fs.roots [] (.inl rfl))).1 $$ Hperm with ⟨Hp0, Hperm⟩
  imod inv_alloc osAbN E iprop(∃ q, osCallPerm (L := L) [] q) $$ [Hp0] with #Hab
  · inext; iexists 1; unfold osCallPerm; iexact Hp0
  imod claims_alloc _ V _ (GMap.toList_keys_nodup _) $$ Han with ⟨Han, Hcl⟩
  imod inv_alloc osShN E iprop(∃ (Vs : Hist) (Γn : GMap (Ino × NameSet) NamesH),
    gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γs () (DFrac.own 1) (σ.fs.roots, Vs) ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn ∗ ⌜RootsOk σ.fs.roots ∧ NamesCoh Vs Γn⌝ ∗
    (letI := (gooseOsGS (L := L)).osAllG; monoNatAuthOwn (gooseOsGS (L := L)).γlen 1 Vs.2.length) ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γlog (logMap Vs.2)) $$ [Hs Han Halen Halog]
    with #Hsi
  · inext
    iexists V, (claimsInit V ((GMap.toList V.now).map (·.1)))
    iframe Hs Han Halen Halog
    ipureintro; exact ⟨hns.1.roots, namesCoh_init V (by rw [hV]; exact hcohS.starts)⟩
  imodintro
  isplitl [HF Hh HAd HAdf HAc Has Hadfs Hacs Hag Hcm Hof]
  · iapply (os_local_ctx_eq σ).mpr
    unfold osCtx treeCtx
    iframe HF Hcm Hof
    iright
    unfold treeShared
    iexists V, σ.fs.metaLog.length, ∅, ∅, ∅
    rw [← hV]
    unfold osTree
    iframe HAd Hh HAdf HAc Has Hadfs Hacs Hag
    isplitr
    · ipureintro; exact ⟨hns.1, hcohS⟩
    unfold callResS
    isplitl []
    · iapply BigSepM.bigSepM_empty.2; itrivial
    · iapply BigSepM.bigSepM_empty.2; itrivial
  simp only [osNames_except]
  ihave Hab' : osAboveInv (L := L) $$ [Hab]
  · unfold osAboveInv; iexact Hab
  unfold osSharedInv osCallPerms osCallPerm osLogLb
  iframe Hsi Hab' Hperm Hlb Hcl


/-- **The mode switch before any step of a non-value `e`** (see the file header): the whole legacy
history `V` (no legacy call or directory fd) for the shared mode's resources: its invariant, the whole
call permission, the log's length, a claim on all names of every directory of the tree; key `[]`'s
whole permission goes into its dispenser (`osAboveInv`). Irreversible. -/
theorem wp_osShareE (R : Roots) (V : Hist) (e : Expr) (he : toVal e = none) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) (DFrac.own 1) R V -∗
      (osSharedInv (L := L) R -∗ osAboveInv (L := L) -∗ osCallPerms (L := L) R -∗
        osLogLb (L := L) V.2.length -∗
        ([∗list] j ∈ (GMap.toList V.now).map (·.1),
          osNames (L := L) j (.except []) (DFrac.own 1) (namesOf V j (.except []))) -∗
        WP e @ s; E {{ Φ }}) -∗
      WP e @ s; E {{ Φ }} := by
  iintro #_ Hh HΦ
  iapply wp_ext_acc (X := fsExt) e Φ he
  iintro %σ %g Hl Hg
  imod osShare_ctx R V σ $$ Hh Hl with ⟨Hl, Hsi, Hab, Hperm, Hlb, Hcl⟩
  imodintro
  iframe Hl Hg
  iapply HΦ $$ Hsi Hab Hperm Hlb Hcl

/-- **The mode switch before any step, its history from an update** (for a generation whose crash
frame must learn of the switch: the history kept in an invariant, opened here, at the step, and closed
again with what the switch allocated): `wp_osShareE` with `osTree` given by an update from `E` to `E'`,
and the update back from `E'` to `E` given the shared mode's resources. -/
theorem wp_osShareE_upd (R : Roots) (V : Hist) (e : Expr) (he : toVal e = none) (E' : CoPset)
    (Φ : val → IProp GF) :
    ⊢ (|={E, E'}=> osTree (L := L) (DFrac.own 1) R V ∗
        (osSharedInv (L := L) R -∗ osAboveInv (L := L) -∗ osCallPerms (L := L) R -∗
          osLogLb (L := L) V.2.length -∗
          ([∗list] j ∈ (GMap.toList V.now).map (·.1),
            osNames (L := L) j (.except []) (DFrac.own 1) (namesOf V j (.except []))) ={E', E}=∗
          WP e @ s; E {{ Φ }})) -∗
      WP e @ s; E {{ Φ }} := by
  iintro Hu
  iapply wp_ext_acc (X := fsExt) e Φ he
  iintro %σ %g Hl Hg
  imod Hu with ⟨Hh, HΦ⟩
  imod osShare_ctx (E := E') R V σ $$ Hh Hl with ⟨Hl, Hsi, Hab, Hperm, Hlb, Hcl⟩
  imod HΦ $$ Hsi Hab Hperm Hlb Hcl with Hwp
  imodintro
  iframe Hl Hg Hwp

end specs

end Fs
end Perennial
