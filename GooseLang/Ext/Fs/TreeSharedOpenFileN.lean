/-
The shared mode of the tree: `open(2)` without `O_TRUNC` of a name holding a file, through a fraction
of a claim on names containing it (`wp_osOpenFileS'`, `TreeSharedCreate.lean`), with its failure's
errno made `ENOENT`-free (`wp_osOpenFileSN'`): the semantics' `ENOENT` rule (`Impl.lean`, `IsFsStep`'s
`"Open"`, 2026-11-14, pending review) returns `ENOENT` only for a path that does not resolve at the
step, and the claim keeps the file at the name. What `durable`'s `tryRead` needs to tell a present
file from a missing one (`errors.Is(err, os.ErrNotExist)`). The proof is `wp_osOpenFileS'`'s, with the
rule's premise used in the failure branch. Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedCreate

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

/-- **`open(2)` of `d/b`, a name holding the file `i`, without `O_TRUNC`** (shared mode), with a
fraction of a claim on names containing `b`: no entry; on success a fresh fd on `i`; a failure is not
`ENOENT`. -/
theorem wp_osOpenFileSN' (R : Roots) (d b : GoString) (j i : Ino) (N : NameSet) (dq dqn : DFrac)
    (h : NamesH) (k s0 : Nat) (q : Qp) (fl : w64) (hfl : OpenFlagsOk fl.toNat)
    (htr : fl.toNat / O_TRUNC % 2 = 0) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = some (.file i)) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N dqn h -∗ osCallS (L := L) k s0 (child d b) q -∗
      (∀ fd : w64, ∀ e : w64, ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ e ≠ ENOENT ∧ fd = -1)⌝ -∗
        osCallPerm (L := L) (callKey R d) q -∗ osPathS (L := L) R d dq j -∗ osNames (L := L) j N dqn h -∗
        (if e = 0 then osFd (L := L) fd (DFrac.own 1) (openFd i fl) else emp) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#fl)))))
        @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  icases osPathS_callKey R d dq j $$ Hp with ⟨Hp, %hkd⟩
  iapply wp_fs_stepM "Open" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h0 Hw Ht
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
  icases osPathS_lookup hR hcoh.2 d dq j $$ HAn Hp with %hl
  icases osNames_entry hcoh.2 j N dqn h $$ HAn Hn with %hent
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
  have hen : st.tree.entry j b = some (.file i) := by rw [hent b hN]; exact hi
  have hl' : st.lookup (child d b) = some (.file i) := by rw [lookup_child hw.roots hl hb]; exact hen
  have hl0 : (st.metaEnd k).lookup (child d b) = some (.file i) := hl'
  unfold osCallS
  icases gAuth_lookup _ _ _ _ _ _ $$ Hacs Hk with %hk
  have hcall : st.proc.calls !! k = some (s0, child d b) := by
    exact hc.calls k _ hk
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h0 _ $$ Hσ Hcells with %Hag
  have htr' : decide ((fl.toNat / O_TRUNC) % 2 = 1) = false := by simp [htr]
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h0) Hwc.1 (filesSame_metaEnd st k) Hag
    exact ⟨_, h0, _, .inl ⟨child d b, fl, k, s0, rfl, treePath_of_lookup hl', hfl, hcall,
      ⟨fun h => absurd h (by simp [htr']), .inr ⟨1, by decide, fun h => absurd h (by decide), rfl, .inl rfl⟩⟩⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  imod Hclose2
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  replace Hst := open_inTree Hst (treePath_of_lookup hl')
  obtain ⟨p', fl', k', s', hv, -, -, hk', hres⟩ := Hst
  obtain ⟨rfl, rfl, rfl⟩ := tokPathFl_inj hv
  rw [hcall] at hk'; cases hk'
  simp only [htr', Bool.false_eq_true, ↓reduceIte] at hres
  unfold callResS
  icases (BigSepM.bigSepM_delete (M := GMap Nat)
    (Φ := fun (_t : Nat) (x : CallV) =>
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm (callKey st.fs.roots x.1.2) (DFrac.own x.2) ()) hk).1 $$ Hcr
    with ⟨Hq, Hcr⟩
  imod gAuth_delete _ _ _ _ _ $$ Hacs Hk with Hacs
  ihave Hw : osWorld (L := L) st Γb Γm Γf Γt h0 $$ [HAb HAm HAf HAt Htok Hcells Hσ]
  · unfold osWorld; iframe; ipureintro; exact Hwc
  obtain ⟨-, hres⟩ := hres
  rcases hres with ⟨st1, tgt, fd, heff, hfree, hst, rfl⟩ | ⟨e, he, hnoent, rfl, hst⟩
  · unfold OpenEffect at heff
    rw [hl0] at heff
    obtain ⟨⟨f', -, hst1⟩, rfl⟩ := heff
    simp only [htr', Bool.false_eq_true, ↓reduceIte] at hst1
    subst st1
    obtain ⟨hfd0, hfdn, hdfn, -⟩ := hfree
    have hst'' : st' = (st.metaEnd k).setProc { (st.metaEnd k).proc with
        fds := <[fd := openFd i fl]> (st.metaEnd k).proc.fds } := hst
    subst hst''
    imod osWorld_addFd (filesSame_metaEnd st k) (d := openFd i fl) hfdn hfd0 (file_of_entry hw hen)
      Hr Hfr $$ Hw with ⟨Hw, Hfd⟩
    imodintro
    iexists Γb, Γm, <[fd := openFd i fl]> Γf, Γt
    isplitl [Hw]
    · unfold osWorld; iexact Hw
    isplitl [Has Hadfs Hacs Hcr HAg Hgr Hcm]
    · iapply (treeCtx_eq _ _).2
      isplitr [Hcm]
      rotate_left
      · iapply commitRes_grow (gooseOsGS (L := L)) (st := st)
          (st' := (st.metaEnd k).setProc { (st.metaEnd k).proc with
            fds := <[fd := openFd i fl]> (st.metaEnd k).proc.fds }) (commitGrows_of_eq rfl) $$ Hcm
      try unfold treeCtxT
      simp only [OsState.metaEnd, OsState.setProc]
      iexists Γdf, GMap.delete k Γc, Γg
      try unfold callResS
      iframe
      ipureintro
      exact ⟨fsTreeWf_addFd (fsTreeWf_metaEnd hw k) hdfn,
        (treeCohS_metaEnd hc k hk).congr rfl rfl rfl rfl rfl⟩
    iapply wp_value'
    iapply HΦ $$ %fd %0 %(.inl ⟨rfl, hfd0⟩) [Hq] Hp Hn
    · unfold osCallPerm; rw [← hkd b, ← hR]; iexact Hq
    rw [if_pos rfl]; iexact Hfd
  · have hst' : st' = st.metaEnd k := by
      rcases hst with rfl | ⟨tgt, heff⟩
      · rfl
      · unfold OpenEffect at heff; rw [hl0] at heff
        obtain ⟨⟨f', -, h1⟩, -⟩ := heff
        simpa [htr'] using h1
    subst hst'
    imod osWorld_filesSame (filesSame_metaEnd st k) Hr Hfr $$ Hw with Hw
    imodintro
    iexists Γb, Γm, Γf, Γt
    isplitl [Hw]
    · unfold osWorld; iexact Hw
    isplitl [Has Hadfs Hacs Hcr HAg Hgr Hcm]
    · iapply (treeCtx_eq _ _).2
      isplitr [Hcm]
      rotate_left
      · iapply commitRes_grow (gooseOsGS (L := L)) (st := st) (st' := st.metaEnd k)
          (commitGrows_of_eq rfl) $$ Hcm
      try unfold treeCtxT
      simp only [OsState.metaEnd]
      iexists Γdf, GMap.delete k Γc, Γg
      try unfold callResS
      iframe
      ipureintro; exact ⟨fsTreeWf_metaEnd hw k, treeCohS_metaEnd hc k hk⟩
    iapply wp_value'
    iapply HΦ $$ %(-1) %e %(.inr ⟨he, (fun h => by rw [hnoent h] at hl0; cases hl0), rfl⟩) [Hq] Hp Hn
    · unfold osCallPerm; rw [← hkd b, ← hR]; iexact Hq
    rw [if_neg he]; iempintro


end specs

end Fs
end Perennial

end
