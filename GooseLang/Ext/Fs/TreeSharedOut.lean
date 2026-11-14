/-
The strict ancestors of the roots (2026-11-13, `notes/wal-fsext-models-review.md`, "Above-root
Stat/Open"): `RootsAbove` and why such a path is no path of the roots' trees; the outside fds
(`osOutFd`, `ProcState.ofds`) and the lifting of a step that sees them (`wp_fs_stepO`); the specs of
`Open`'s outside case in the shared mode (`wp_osOpenAboveS`), of `FdKind` (`2`), `OutSync` and
`OutClose` on an outside fd. Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedOpenDir
public import GooseLang.Ext.Fs.TreeSharedCreate

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Strict ancestors of the roots -/

/-- `p` is a strict ancestor of a root of `R` (`OsState.AboveRoot` of a state with roots `R`). -/
def RootsAbove (R : Roots) (p : GoString) : Prop :=
  p = [slashB] ∨ (p ≠ [] ∧ ∃ rj ∈ R, (p ++ [slashB]).IsPrefix rj.1)

theorem rootForm_len {r : GoString} (h : RootForm r) : 2 ≤ r.length := by
  obtain ⟨cs, hne, hok, rfl⟩ := h
  rcases cs with _ | ⟨c, cs⟩
  · exact absurd rfl hne
  · have hc : c ≠ [] := (hok c (by simp)).1
    rcases c with _ | ⟨x, c⟩
    · exact absurd rfl hc
    · simp [joinPath]

theorem prefix_joinPath_cons (r c : GoString) (cs : List GoString) :
    (r ++ [slashB]).IsPrefix (joinPath r (c :: cs)) :=
  ⟨c ++ cs.flatMap (fun c => slashB :: c), by simp [joinPath]⟩

/-- **A strict ancestor of a root is no path of the roots' trees** (well-formed roots). -/
theorem rootsAbove_not_treePath {st : OsState} {p : GoString} (hR : RootsOk st.fs.roots)
    (h : RootsAbove st.fs.roots p) : ¬ st.TreePath p := by
  have hlen : ∀ rj ∈ st.fs.roots, 2 ≤ rj.1.length := fun rj hm => rootForm_len (hR.2.2 rj hm).1
  -- `r ++ "/"` is a prefix of `p` for a root `r` of which `p` is the root or below
  have hpre : st.TreePath p → ∃ rj ∈ st.fs.roots, rj.1 = p ∨ (rj.1 ++ [slashB]).IsPrefix p := by
    rintro (⟨rj, hm, rfl⟩ | ⟨rj, hm, cs, hne, -, rfl⟩)
    · exact ⟨rj, hm, .inl rfl⟩
    · rcases cs with _ | ⟨c, cs⟩
      · exact absurd rfl hne
      · exact ⟨rj, hm, .inr (prefix_joinPath_cons _ _ _)⟩
  intro htp
  obtain ⟨r2, hm2, h2⟩ := hpre htp
  rcases h with rfl | ⟨hne, r1, hm1, h1⟩
  · -- `/` is shorter than any root, and than anything below one
    have hl2 := hlen r2 hm2
    rcases h2 with h2 | h2
    · rw [h2] at hl2; simp at hl2
    · have hl3 := h2.length_le
      simp only [List.length_append, List.length_singleton] at hl3; omega
  · -- `r2 ++ "/"` is a prefix of `r1`: `r2` is `r1` (too long) or above it (`RootsOk`)
    have h21 : (r2.1 ++ [slashB]).IsPrefix r1.1 := by
      rcases h2 with h2 | h2
      · rw [h2]; exact h1
      · exact h2.trans ((List.prefix_append p [slashB]).trans h1)
    by_cases heq : r2.1 = r1.1
    · have := h21.length_le; rw [heq] at this; simp at this; omega
    · exact (hR.2.2 r2 hm2).2 r1 hm1 heq (.inr h21)

/-! ## Outside fds -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **The fd `fd` of a directory outside the roots' trees** (`Open`'s outside case), held whole. -/
def osOutFd (fd : w64) : IProp GF :=
  gFdElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γo fd (DFrac.own 1) ()

instance osOutFd_timeless (fd : w64) : Timeless (osOutFd (L := L) fd) := by
  unfold osOutFd; infer_instance

/-- An open outside fd is not negative. -/
theorem osOutFd_nonneg (fd : w64) : osOutFd (L := L) fd ⊢ ⌜0 ≤ fd.toInt⌝ := by
  unfold osOutFd; exact gFdElem_nonneg _ _ _ _ _

/-- **The lifting of any operation, with the outside fds' interpretation too** (`wp_fs_stepM`'s
continuation also gets and gives back `ofdCtx`). -/
theorem wp_fs_stepO (o : String) (v : val) (Φ : val → IProp GF) (hv : v.isPanic = false)
    (hE : ↑osN ⊆ E) :
    ⊢ osInv (L := L) -∗
      (∀ st Γb Γm Γf Γt h, osWorld st Γb Γm Γf Γt h -∗ treeCtx (gooseOsGS (L := L)) st -∗
          ofdCtx (gooseOsGS (L := L)) st ={E \ ↑osN, ∅}=∗
        ⌜∃ e' h' st', FsStep o v h st () e' h' st' ()⌝ ∗
        ▷ ∀ e' h' st', ⌜FsStep o v h st () e' h' st' ()⌝ ={∅, E \ ↑osN}=∗
          ∃ Γb' Γm' Γf' Γt', osWorld st' Γb' Γm' Γf' Γt' h' ∗
            treeCtx (gooseOsGS (L := L)) st' ∗ ofdCtx (gooseOsGS (L := L)) st' ∗
            WP e' @ s; E {{ Φ }}) -∗
      WP (ExternalOp fsExt.name o (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv HF
  iapply wp_extStep o v Φ hv
  iintro %h %σ %g Hheap Hl -
  icases (os_local_ctx_eq σ).mp $$ Hl with Hl
  unfold osCtx osCtxF
  icases Hl with ⟨⟨%Γb, %Γm, %Γf, %Γt, %Hwc, HAb, HAm, HAf, HAt, Htok, Hv⟩, Hns, Hof⟩
  unfold osInv
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%cv, %n, Hv', Hcells⟩
  icases gVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl⟩ := Heq
  imod HF $$ %σ %Γb %Γm %Γf %Γt %h [HAb HAm HAf HAt Htok Hcells Hheap] Hns Hof with ⟨%Hex, Hcont⟩
  · unfold osWorld; iframe; ipureintro; exact Hwc
  imodintro
  isplitr
  · ipureintro
    obtain ⟨e', h', st', Hst⟩ := Hex
    exact FsSemOk.step_ex _ _ _ _ g _ _ _ ()
      (fun _ _ _ _ _ h1 h2 => mapsTo_unique Hwc.1 h1 h2) Hst
  inext
  iintro %e' %h' %σ' %g' %Hst -
  have Hst := FsSemOk.step_sub _ _ _ _ _ _ _ _ _ Hst
  imod Hcont $$ %e' %h' %σ' %Hst with ⟨%Γb', %Γm', %Γf', %Γt', Hw, Hn, Hof, Hwp⟩
  unfold osWorld
  icases Hw with ⟨%Hwc', HAb, HAm, HAf, HAt, Htok, Hcells, Hheap⟩
  imod gVar_update _ _ _ (cellView σ', GMap.size σ'.proc.inflight) $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Hcells] with -
  · inext; iexists (cellView σ'), (GMap.size σ'.proc.inflight); iframe
  imodintro
  iframe Hheap Hwp
  isplitl [HAb HAm HAf HAt Htok Hv Hn Hof]
  · iapply (os_local_ctx_eq σ').mpr
    unfold osCtx osCtxF
    iframe Hn Hof
    iexists Γb', Γm', Γf', Γt'
    iframe
    ipureintro; exact Hwc'
  · have : (ExtInterp.globalCtx (E := fsExt) (extGlobalGS fsExt) g' : IProp GF) =
        iprop(True) := rfl
    rw [this]; itrivial

theorem filesSame_delOfd (st : OsState) (fd : w64) : FilesSame st (st.delOfd fd) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem treeFrame_delOfd (st : OsState) (fd : w64) : TreeFrame st (st.delOfd fd) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => Iff.rfl, fun _ h => Or.inl h⟩

theorem ofdDisj_delOfd {st : OsState} (h : OfdDisj st) (fd : w64) : OfdDisj (st.delOfd fd) := by
  intro fd' ho
  have ho' : (GMap.delete fd st.proc.ofds) !! fd' ≠ none := ho
  rw [GMap.lookup_delete_iff] at ho'
  split at ho'
  · exact absurd rfl ho'
  · exact h fd' ho'

/-- The outside fd held is one of the state's, and no other fd has its number. -/
theorem outFd_lookup (st : OsState) (fd : w64) :
    ⊢ ofdCtx (gooseOsGS (L := L)) st -∗ osOutFd (L := L) fd -∗
      ⌜st.proc.ofds !! fd = some () ∧ st.proc.fds !! fd = none ∧ st.proc.dfds !! fd = none⌝ := by
  unfold ofdCtx osOutFd
  iintro ⟨%hd, Ha⟩ Hfd
  icases gFdElem_lookup _ _ _ _ _ _ $$ Ha Hfd with %hl
  ipureintro
  exact ⟨hl, hd fd (by rw [hl]; simp)⟩

/-- **`FdKind(fd)` of an outside fd**: `2`. -/
theorem wp_osFdKindOut (fd : w64) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osOutFd (L := L) fd -∗ (osOutFd (L := L) fd -∗ Φ (#(2 : w64))) -∗
      WP (ExternalOp fsExt.name "FdKind" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_fs_stepO "FdKind" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Ht Hof
  icases outFd_lookup st fd $$ Hof Hfd with %hl
  obtain ⟨ho, hnf, hnd⟩ := hl
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 (filesSame_refl st) Hag
    exact ⟨_, h, st, ⟨fd, rfl, rfl, .inr (.inr ⟨hnf, hnd, ho, rfl⟩)⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  imod Hclose2
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', hv, hst, hres⟩ := Hst
  subst st'
  cases go.intoVal_inj hv
  rcases hres with ⟨⟨d, hd⟩, -⟩ | ⟨-, ⟨df, hd⟩, -⟩ | ⟨-, -, -, rfl⟩
  · rw [hnf] at hd; cases hd
  · rw [hnd] at hd; cases hd
  imod osWorld_filesSame (st := st) (st' := st) (filesSame_refl st) Hr Hfr
    $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
  · unfold osWorld; iframe; ipureintro; exact Hwc
  imodintro
  iexists Γb, Γm, Γf, Γt
  isplitl [Hw]
  · unfold osWorld; iexact Hw
  iframe Ht Hof
  iapply wp_value'
  iapply HΦ $$ Hfd

/-- **`OutSync(fd)`** (`fsync(2)` of an outside fd): any errno, nothing changed. -/
theorem wp_osOutSync (fd : w64) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osOutFd (L := L) fd -∗ (∀ e : w64, osOutFd (L := L) fd -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "OutSync" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_fs_stepO "OutSync" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Ht Hof
  icases outFd_lookup st fd $$ Hof Hfd with %hl
  obtain ⟨ho, -, -⟩ := hl
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 (filesSame_refl st) Hag
    exact ⟨_, h, st, ⟨fd, 0, rfl, ho, rfl, rfl⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  imod Hclose2
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', e, hv, -, hst, rfl⟩ := Hst
  subst st'
  imod osWorld_filesSame (st := st) (st' := st) (filesSame_refl st) Hr Hfr
    $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
  · unfold osWorld; iframe; ipureintro; exact Hwc
  imodintro
  iexists Γb, Γm, Γf, Γt
  isplitl [Hw]
  · unfold osWorld; iexact Hw
  iframe Ht Hof
  iapply wp_value'
  iapply HΦ $$ %e Hfd

/-- **`OutClose(fd)`** (`close(2)` of an outside fd): any errno, the fd freed. -/
theorem wp_osOutClose (fd : w64) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osOutFd (L := L) fd -∗ (∀ e : w64, Φ (#e)) -∗
      WP (ExternalOp fsExt.name "OutClose" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_fs_stepO "OutClose" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Ht Hof
  icases outFd_lookup st fd $$ Hof Hfd with %hl
  obtain ⟨ho, -, -⟩ := hl
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 (filesSame_delOfd st fd) Hag
    exact ⟨_, h, _, ⟨fd, 0, rfl, ho, rfl, rfl⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  imod Hclose2
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', e, hv, -, hst, rfl⟩ := Hst
  cases go.intoVal_inj hv
  subst st'
  imod osWorld_filesSame (st := st) (st' := st.delOfd fd) (filesSame_delOfd st fd) Hr Hfr
    $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
  · unfold osWorld; iframe; ipureintro; exact Hwc
  unfold ofdCtx osOutFd
  icases Hof with ⟨%hd, Ha⟩
  imod gFdElem_delete _ _ _ _ _ $$ Ha Hfd with Ha
  imodintro
  iexists Γb, Γm, Γf, Γt
  isplitl [Hw]
  · unfold osWorld; iexact Hw
  isplitl [Ht]
  · iapply treeCtx_frame _ (treeFrame_delOfd st fd) $$ Ht
  isplitl [Ha]
  · isplitr
    · ipureintro; exact ofdDisj_delOfd hd fd
    · simp only [OsState.delOfd]; iexact Ha
  iapply wp_value'
  iapply HΦ $$ %e

/-- **`open(p, O_RDONLY|O_CLOEXEC)` of a strict ancestor `p` of a root, in the shared mode** (its
outside case): the call ends (its fraction of the call permission back); an outside fd, or any
errno. -/
theorem wp_osOpenAboveS (R : Roots) (p : GoString) (hp : RootsAbove R p) (k s0 : Nat) (q : Qp)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osCallS (L := L) k s0 q -∗
      (∀ fd : w64, ∀ e : w64, ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ fd = -1)⌝ -∗
        osCallPerm (L := L) q -∗ (⌜e = 0⌝ -∗ osOutFd (L := L) fd) -∗ Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#p) (#flRO))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv #Hsi Hk HΦ
  iapply wp_fs_stepO "Open" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Ht Hof
  unfold treeCtx
  icases Ht with ⟨Hm, Hcm⟩
  icases Hm with (Hm | Hm)
  · iexfalso; iapply legacy_callS_excl st k s0 q $$ Hk Hm
  unfold treeShared
  icases Hm with ⟨%V0, %s1, %Γdf, %Γc, %Γg, %hns, HAd, Hd, HAdf, HAc, Has, Hadfs, Hacs, Hcr, HAg, Hgr⟩
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
  subst hR
  have hntp : ¬ st.TreePath p := rootsAbove_not_treePath hw.roots hp
  unfold osCallS
  icases gAuth_lookup _ _ _ _ _ _ $$ Hacs Hk with %hk
  have hcall : st.proc.calls !! k = some s0 := hc.calls k _ hk
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 (filesSame_metaEnd st k) Hag
    exact ⟨_, h, _, .inr ⟨p, flRO, k, s0, rfl, hntp, hp, .inr (by decide), hcall,
      .inr ⟨1, by decide, rfl, rfl⟩⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  imod Hclose2
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  have hstep := Hst
  simp only [IsFsStep] at Hst
  rcases Hst with ⟨p', fl, k', s', hv, htp, -⟩ | ⟨p', fl, k', s', hv, -, -, -, hk', hres⟩
  · obtain ⟨rfl, rfl, rfl⟩ := tokPathFl_inj hv
    exact absurd htp hntp
  obtain ⟨rfl, rfl, rfl⟩ := tokPathFl_inj hv
  rw [hcall] at hk'; cases hk'
  -- the call's fraction back
  unfold callResS
  icases (BigSepM.bigSepM_delete (M := GMap Nat)
    (Φ := fun (_t : Nat) (x : Nat × Qp) =>
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm () (DFrac.own x.2) ()) hk).1 $$ Hcr
    with ⟨Hq, Hcr⟩
  imod gAuth_delete _ _ _ _ _ $$ Hacs Hk with Hacs
  unfold ofdCtx
  icases Hof with ⟨%hd, Ha⟩
  have hd' := (isFsStep_ofd (o := "Open") hstep (by decide) hd).1
  rcases hres with ⟨fd, hfree, rfl, rfl⟩ | ⟨e, he, rfl, rfl⟩
  · have hs : FilesSame st ((st.metaEnd k).addOfd fd) := ⟨rfl, rfl, rfl, rfl, rfl⟩
    imod osWorld_filesSame (st := st) (st' := (st.metaEnd k).addOfd fd) hs Hr Hfr
      $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
    · unfold osWorld; iframe; ipureintro; exact Hwc
    imod gFdElem_insert _ _ _ fd () hfree.1 hfree.2.2.2 $$ Ha with ⟨Ha, Hfd⟩
    imodintro
    iexists Γb, Γm, Γf, Γt
    isplitl [Hw]
    · unfold osWorld; iexact Hw
    isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr HAg Hgr Hcm]
    · try unfold treeCtx
      isplitr [Hcm]
      rotate_left
      · iapply commitRes_grow (gooseOsGS (L := L)) (st := st)
          (st' := (st.metaEnd k).addOfd fd) (commitGrows_of_eq rfl) $$ Hcm
      iright
      simp only [OsState.addOfd, OsState.metaEnd]
      try unfold treeShared
      iexists V0, s1, Γdf, GMap.delete k Γc, Γg
      iframe
      ipureintro
      exact ⟨⟨hw.roots, hw.hist, hw.dfds, hw.disj, hw.files_lt⟩,
        (treeCohS_metaEnd hc k hk).congr rfl rfl rfl rfl⟩
    isplitl [Ha]
    · isplitr
      · ipureintro; exact hd'
      · simp only [OsState.addOfd, OsState.metaEnd]; iexact Ha
    iapply wp_value'
    iapply HΦ $$ %fd %0 %(.inl ⟨rfl, hfree.1⟩) [Hq]
    · unfold osCallPerm; iexact Hq
    iintro -
    unfold osOutFd; iexact Hfd
  · imod osWorld_filesSame (st := st) (st' := st.metaEnd k) (filesSame_metaEnd st k) Hr Hfr
      $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
    · unfold osWorld; iframe; ipureintro; exact Hwc
    imodintro
    iexists Γb, Γm, Γf, Γt
    isplitl [Hw]
    · unfold osWorld; iexact Hw
    isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr HAg Hgr Hcm]
    · try unfold treeCtx
      isplitr [Hcm]
      rotate_left
      · iapply commitRes_grow (gooseOsGS (L := L)) (st := st) (st' := st.metaEnd k)
          (commitGrows_of_eq rfl) $$ Hcm
      iright
      simp only [OsState.addOfd, OsState.metaEnd]
      try unfold treeShared
      iexists V0, s1, Γdf, GMap.delete k Γc, Γg
      iframe
      ipureintro; exact ⟨fsTreeWf_metaEnd hw k, treeCohS_metaEnd hc k hk⟩
    isplitl [Ha]
    · isplitr
      · ipureintro; exact hd'
      · simp only [OsState.addOfd, OsState.metaEnd]; iexact Ha
    iapply wp_value'
    iapply HΦ $$ %(-1) %e %(.inr ⟨he, rfl⟩) [Hq]
    · unfold osCallPerm; iexact Hq
    iintro %he0
    exact absurd he0 he

end specs

end Fs
end Perennial

end
