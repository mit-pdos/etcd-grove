/-
The shared mode of the tree: **guard calls** (`notes/wal-fsext-i2-design.md`, "Implementation log,
guard calls"). A guard is a call begun by `CallBegin` that never logs: it holds a fraction of the
call permission (`osGuardS`), so that no directory is renamed while it is in flight (a directory
`Rename` needs the whole permission), and is ended by a `LstatDir`, a step without effect, which
gives the fraction back. `os.RemoveAll`'s model holds one across its inner calls; under it, a
directory operation other than a rename takes a call holding the rest of the permission
(`wp_osRmdirSG'`, `wp_osMkdirSG'`, in `TreeSharedMeta.lean`). `TreeShared.lean` states the specs and
takes their proofs from here. Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedMeta

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- A path of the roots `R` (a root followed by valid components) is a path of the tree. -/
theorem treePath_of_roots {st : OsState} {R : Roots} {p : GoString} (hR : st.fs.roots = R)
    (hp : ∃ r j0 cs, (r, j0) ∈ R ∧ (∀ c ∈ cs, NameOk c) ∧ p = joinPath r cs) : st.TreePath p := by
  obtain ⟨r, j0, cs, hrj, hcs, rfl⟩ := hp
  rw [← hR] at hrj
  rcases cs with _ | ⟨c, cs⟩
  · left; exact ⟨(r, j0), hrj, by simp [joinPath]⟩
  · right; exact ⟨(r, j0), hrj, c :: cs, by simp, hcs, rfl⟩

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

theorem wp_osCallBeginGuardS' (R : Roots) (p : GoString) (g : Qp) (n : Nat) (hE : ↑osN ⊆ E)
    (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osCallPerm (L := L) (callKey R p) g -∗
      osLogLb (L := L) n -∗
      (∀ (t s0 : Nat), ⌜n ≤ s0⌝ -∗ osGuardS (L := L) t s0 p g -∗ osLogLb (L := L) s0 -∗
        Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "CallBegin" (Val (#p))) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi Hq #Hlb HΦ
  iapply wp_fs_stepM "CallBegin" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Ht
  icases (treeCtx_eq _ _).1 $$ Ht with ⟨Ht, Hcm⟩
  unfold treeCtxT
  icases Ht with ⟨%Γdf, %Γc, %Γg, %hns, Has, Hadfs, Hacs, Hcr, HAg, Hgr⟩
  obtain ⟨hw, hc⟩ := hns
  unfold osSharedInv
  imod inv_acc (osShN_sub hE') $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %hVs
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hVs
  obtain ⟨hR, rfl⟩ := hVs
  unfold osLogLb
  icases (letI := (gooseOsGS (L := L)).osAllG; monoNatLbOwn_valid _ _ _ _) $$ Halen Hlb with %hn
  ihave #Hlb' := (letI := (gooseOsGS (L := L)).osAllG; monoNatLbOwn_get _ _ _) $$ Halen
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh'⟩ := Hwc
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  obtain ⟨t, ht1, ht2⟩ := exists_fresh2 st.proc.calls st.proc.inflight
  have hs : FilesSame st (st.setProc { st.proc with
      calls := <[t := (st.fs.metaLog.length, p)]> st.proc.calls }) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf hs Hag
    exact ⟨_, h, _, ⟨t, p, rfl, ht1, ht2, rfl, rfl⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  imod Hclose2
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨t', p', hpv, h1', h2', rfl, rfl⟩ := Hst
  cases go.intoVal_inj hpv
  imod osWorld_filesSame (st := st)
    (st' := st.setProc { st.proc with calls := <[t' := (st.fs.metaLog.length, p)]> st.proc.calls })
    ⟨rfl, rfl, rfl, rfl, rfl⟩ Hr Hfr $$ [HAb HAm HAf HAt Htok Hcells Hσ]
    with Hw
  · unfold osWorld; iframe; ipureintro; exact ⟨hwf, hcoh'⟩
  have hΓg : Γg !! t' = none := (hc.fresh h1').2
  imod gAuth_insert _ _ _ _ (((st.fs.metaLog.length, p), g) : CallV) hΓg $$ HAg with ⟨HAg, Hk⟩
  imodintro
  iexists Γb, Γm, Γf, Γt
  dsimp only
  isplitl [Hw]
  · unfold osWorld; iexact Hw
  isplitl [Has Hadfs Hacs Hcr HAg Hgr Hq Hcm]
  · iapply (treeCtx_eq _ _).2
    isplitr [Hcm]
    rotate_left
    · iapply commitRes_setProc $$ Hcm
    unfold treeCtxT
    simp only [OsState.setProc]
    iexists Γdf, Γc, <[t' := (((st.fs.metaLog.length, p), g) : CallV)]> Γg
    try unfold callResS
    iframe Has Hadfs Hacs Hcr HAg
    isplitr
    · ipureintro
      exact ⟨⟨hw.roots, hw.hist, hw.dfds, hw.disj, hw.files_lt⟩, treeCohS_beginGuard hc t' p g h1'⟩
    · try unfold callResS
      iapply (BigSepM.bigSepM_insert (Φ := fun (_t : Nat) (x : CallV) =>
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm (callKey st.fs.roots x.1.2) (DFrac.own x.2) ()) hΓg).2
      iframe Hgr
      unfold osCallPerm; rw [hR]; iexact Hq
  iapply wp_value'
  unfold osGuardS
  iapply HΦ $$ %t' %st.fs.metaLog.length %hn.2 Hk Hlb'

theorem wp_osLstatDirGuardS' (R : Roots) (p : GoString) (t sg : Nat) (g : Qp)
    (hp : ∃ r j0 cs, (r, j0) ∈ R ∧ (∀ c ∈ cs, NameOk c) ∧ p = joinPath r cs)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osGuardS (L := L) t sg p g -∗
      (∀ isDir : w64, ∀ e : w64, ⌜isDir = 1 → e ≠ 0⌝ -∗ osCallPerm (L := L) (callKey R p) g -∗
        Φ (PairV (#isDir) (#e))) -∗
      WP (ExternalOp fsExt.name "LstatDir" (Val (PairV (osTokV t) (#p)))) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi Hk HΦ
  iapply wp_fs_stepM "LstatDir" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Ht
  icases (treeCtx_eq _ _).1 $$ Ht with ⟨Ht, Hcm⟩
  unfold treeCtxT
  icases Ht with ⟨%Γdf, %Γc, %Γg, %hns, Has, Hadfs, Hacs, Hcr, HAg, Hgr⟩
  obtain ⟨hw, hc⟩ := hns
  unfold osSharedInv
  imod inv_acc (osShN_sub hE') $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %hVs
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hVs
  obtain ⟨hR, rfl⟩ := hVs
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
  unfold osGuardS
  icases gAuth_lookup _ _ _ _ _ _ $$ HAg Hk with %hk
  have hcall : st.proc.calls !! t = some (sg, p) := hc.gcalls t _ hk
  have htp : st.TreePath p := treePath_of_roots hR hp
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hs : FilesSame st (st.metaEnd t) := filesSame_metaEnd st t
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 hs Hag
    exact ⟨_, h, _, ⟨p, 0, 0, t, sg, rfl, htp, hcall, rfl, .inr rfl, rfl⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  imod Hclose2
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨p', isDir, e, t', s', hv, -, -, rfl, hres, rfl⟩ := Hst
  obtain ⟨rfl, rfl⟩ := tokPath_inj hv
  have hW : isDir = 1 → e ≠ 0 := by
    intro h1
    rcases hres with ⟨-, -, he0⟩ | h0
    · exact he0
    · rw [h0] at h1; exact absurd h1 (by decide)
  imod osWorld_filesSame (st := st) (st' := st.metaEnd t) hs Hr Hfr
    $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
  · unfold osWorld; iframe; ipureintro; exact Hwc
  unfold callResS
  icases (BigSepM.bigSepM_delete (M := GMap Nat)
    (Φ := fun (_t : Nat) (x : CallV) =>
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm (callKey st.fs.roots x.1.2) (DFrac.own x.2) ()) hk).1 $$ Hgr
    with ⟨Hq, Hgr⟩
  imod gAuth_delete _ _ _ _ _ $$ HAg Hk with HAg
  imodintro
  iexists Γb, Γm, Γf, Γt
  isplitl [Hw]
  · unfold osWorld; iexact Hw
  isplitl [Has Hadfs Hacs Hcr HAg Hgr Hcm]
  · iapply (treeCtx_eq _ _).2
    isplitr [Hcm]
    rotate_left
    · iapply commitRes_grow (gooseOsGS (L := L)) (st := st) (st' := st.metaEnd t)
        (commitGrows_of_eq rfl) $$ Hcm
    try unfold treeCtxT
    simp only [OsState.metaEnd]
    iexists Γdf, Γc, GMap.delete t Γg
    try unfold callResS
    iframe
    ipureintro; exact ⟨fsTreeWf_metaEnd hw t, treeCohS_guardEnd hc t hk⟩
  iapply wp_value'
  iapply HΦ $$ %isDir %e %hW [Hq]
  unfold osCallPerm; rw [← hR]; iexact Hq

end specs

end Fs
end Perennial

end
