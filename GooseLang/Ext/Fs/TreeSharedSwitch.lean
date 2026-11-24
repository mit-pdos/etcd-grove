/-
The tree's coherence as a call begins (`treeCohS_begin`, `treeCohS_beginGuard`) and `CallBegin`
(`wp_osCallBeginS'`, `notes/wal-fsext-i2-design.md`, §2.3). `TreeShared.lean` states the API and
takes its proofs from here. Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedRes

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Pure facts -/

/-- A key of the logging or guard calls is a call in flight. -/
theorem TreeCohS.fresh {st : OsState} {Γdf : GMap w64 (Ino × DirPhS)}
    {Γc Γg : GMap Nat CallV} (hc : TreeCohS st Γdf Γc Γg) {t : Nat}
    (ht : st.proc.calls !! t = none) : Γc !! t = none ∧ Γg !! t = none := by
  constructor
  · cases h0 : Γc !! t with
    | none => rfl
    | some x => have := hc.calls t x h0; rw [ht] at this; cases this
  · cases h0 : Γg !! t with
    | none => rfl
    | some x => have := hc.gcalls t x h0; rw [ht] at this; cases this

/-- The state after `CallBegin` of the call `t` on `p`. -/
abbrev OsState.callBegin (st : OsState) (t : Nat) (p : GoString) : OsState :=
  st.setProc { st.proc with calls := <[t := (st.fs.metaLog.length, p)]> st.proc.calls }

/-- The shared coherence with a logging call begun, holding `q`. -/
theorem treeCohS_begin {st : OsState} {Γdf : GMap w64 (Ino × DirPhS)}
    {Γc Γg : GMap Nat CallV} (hc : TreeCohS st Γdf Γc Γg) (t : Nat) (p : GoString) (q : Qp)
    (ht : st.proc.calls !! t = none) :
    TreeCohS (st.callBegin t p) Γdf (<[t := (((st.fs.metaLog.length, p), q) : CallV)]> Γc) Γg := by
  obtain ⟨hct, hgt⟩ := hc.fresh ht
  have hnone : ∀ y, st.fs.metaLog.length ≤ y → st.fs.metaLog[y]? = none := fun y hy =>
    List.getElem?_eq_none_iff.2 hy
  refine ⟨hc.starts, hc.pss, hc.rc.elim (fun ρ h => ⟨ρ, h.1.congr rfl rfl rfl, ?_⟩), hc.valid,
    hc.fds, hc.ph, fun t0 x hx => ?_, fun t0 x hx => ?_, fun t0 x hx => ?_,
    fun t0 x hx => ?_, fun t0 s hs => ?_⟩
  · obtain ⟨hw, ha, hp⟩ := h.2
    refine ⟨fun t0 x hx hq y ey hy he => ?_, fun t0 x hx y ey he hd => ?_,
      fun c x t0 g hx hg hk hq hle y ey hy he => ?_⟩
    · by_cases h0 : t = t0
      · subst h0; rw [GMap.lookup_insert] at hx; cases hx
        change st.fs.metaLog[y]? = some ey at he; rw [hnone y hy] at he; cases he
      · rw [GMap.lookup_insert_ne _ _ h0] at hx; exact hw t0 x hx hq y ey hy he
    · by_cases h0 : t = t0
      · subst h0; rw [GMap.lookup_insert] at hx; cases hx
        exact (List.getElem?_eq_some_iff.1 he).1
      · rw [GMap.lookup_insert_ne _ _ h0] at hx; exact ha t0 x hx y ey he hd
    · by_cases h0 : t = c
      · subst h0; rw [GMap.lookup_insert] at hx; cases hx
        change st.fs.metaLog[y]? = some ey at he; rw [hnone y hy] at he; cases he
      · rw [GMap.lookup_insert_ne _ _ h0] at hx; exact hp c x t0 g hx hg hk hq hle y ey hy he
  · show (<[t := (st.fs.metaLog.length, p)]> st.proc.calls) !! t0 = _
    by_cases h0 : t = t0
    · subst h0; rw [GMap.lookup_insert] at hx; cases hx; simp
    · rw [GMap.lookup_insert_ne _ _ h0] at hx; rw [GMap.lookup_insert_ne _ _ h0]; exact hc.calls t0 x hx
  · by_cases h0 : t = t0
    · subst h0; rw [GMap.lookup_insert] at hx; cases hx; exact Nat.le_refl _
    · rw [GMap.lookup_insert_ne _ _ h0] at hx; exact hc.callsLe t0 x hx
  · show (<[t := (st.fs.metaLog.length, p)]> st.proc.calls) !! t0 = _
    by_cases h0 : t = t0
    · subst h0; rw [hgt] at hx; cases hx
    · rw [GMap.lookup_insert_ne _ _ h0]; exact hc.gcalls t0 x hx
  · by_cases h0 : t = t0
    · subst h0; rw [hgt] at hx; cases hx
    · rw [GMap.lookup_insert_ne _ _ h0]; exact hc.gdisj t0 x hx
  · change (<[t := (st.fs.metaLog.length, p)]> st.proc.calls) !! t0 = some s at hs
    by_cases h0 : t = t0
    · subst h0; left; rw [GMap.lookup_insert]; simp
    · rw [GMap.lookup_insert_ne _ _ h0] at hs; rw [GMap.lookup_insert_ne _ _ h0]; exact hc.cover t0 s hs

/-- The shared coherence with a guard call begun, holding `g`. -/
theorem treeCohS_beginGuard {st : OsState} {Γdf : GMap w64 (Ino × DirPhS)}
    {Γc Γg : GMap Nat CallV} (hc : TreeCohS st Γdf Γc Γg) (t : Nat) (p : GoString) (g : Qp)
    (ht : st.proc.calls !! t = none) :
    TreeCohS (st.callBegin t p) Γdf Γc (<[t := (((st.fs.metaLog.length, p), g) : CallV)]> Γg) := by
  obtain ⟨hct, hgt⟩ := hc.fresh ht
  have hnone : ∀ y, st.fs.metaLog.length ≤ y → st.fs.metaLog[y]? = none := fun y hy =>
    List.getElem?_eq_none_iff.2 hy
  refine ⟨hc.starts, hc.pss, hc.rc.elim (fun ρ h => ⟨ρ, h.1.congr rfl rfl rfl, ?_⟩), hc.valid,
    hc.fds, hc.ph, fun t0 x hx => ?_, hc.callsLe, fun t0 x hx => ?_,
    fun t0 x hx => ?_, fun t0 s hs => ?_⟩
  · obtain ⟨hw, ha, hp⟩ := h.2
    refine ⟨hw, ha, fun c x t0 g' hx hg hk hq hle y ey hy he => ?_⟩
    by_cases h0 : t = t0
    · subst h0; rw [GMap.lookup_insert] at hg; cases hg
      have := Nat.le_antisymm (hc.callsLe c x hx) hle
      change st.fs.metaLog[y]? = some ey at he
      have hy' : st.fs.metaLog.length ≤ y := by
        have : x.1.1 = st.fs.metaLog.length := this
        omega
      rw [hnone y hy'] at he; cases he
    · rw [GMap.lookup_insert_ne _ _ h0] at hg; exact hp c x t0 g' hx hg hk hq hle y ey hy he
  · show (<[t := (st.fs.metaLog.length, p)]> st.proc.calls) !! t0 = _
    by_cases h0 : t = t0
    · subst h0; rw [hct] at hx; cases hx
    · rw [GMap.lookup_insert_ne _ _ h0]; exact hc.calls t0 x hx
  · show (<[t := (st.fs.metaLog.length, p)]> st.proc.calls) !! t0 = _
    by_cases h0 : t = t0
    · subst h0; rw [GMap.lookup_insert] at hx; cases hx; simp
    · rw [GMap.lookup_insert_ne _ _ h0] at hx; rw [GMap.lookup_insert_ne _ _ h0]; exact hc.gcalls t0 x hx
  · by_cases h0 : t = t0
    · subst h0; exact hct
    · rw [GMap.lookup_insert_ne _ _ h0] at hx; exact hc.gdisj t0 x hx
  · change (<[t := (st.fs.metaLog.length, p)]> st.proc.calls) !! t0 = some s at hs
    by_cases h0 : t = t0
    · subst h0; right; rw [GMap.lookup_insert]; simp
    · rw [GMap.lookup_insert_ne _ _ h0] at hs; rw [GMap.lookup_insert_ne _ _ h0]; exact hc.cover t0 s hs

theorem osShN_sub {E : CoPset} (h : ↑osShN ⊆ E) : (↑osShN : CoPset) ⊆ E \ ↑osN := by
  have hd : (↑osShN : CoPset) ## ↑osN := ndot_ne_disjoint nroot (by decide)
  intro p hp
  exact LawfulSet.mem_diff.2 ⟨h p hp, fun hn => hd p ⟨hp, hn⟩⟩

/-! ## The switch and `CallBegin` -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

instance osSharedBody_timeless (R : Roots) : Timeless (PROP := IProp GF)
    iprop(∃ (Vs : Hist) (Γn : GMap (Ino × NameSet) NamesH),
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γs () (DFrac.own 1) (R, Vs) ∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn ∗ ⌜RootsOk R ∧ NamesCoh Vs Γn⌝ ∗
      (letI := (gooseOsGS (L := L)).osAllG; monoNatAuthOwn (gooseOsGS (L := L)).γlen 1 Vs.2.length) ∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γlog (logMap Vs.2)) := by
  letI := (gooseOsGS (L := L)).osAllG; infer_instance

theorem commitRes_setProc (st : OsState) (p : ProcState) :
    commitRes (gooseOsGS (L := L)) st ⊢ commitRes (gooseOsGS (L := L)) (st.setProc p) :=
  commitRes_grow _ (commitGrows_of_eq rfl)

theorem wp_osCallBeginS' (R : Roots) (p : GoString) (q : Qp) (n : Nat) (hE : ↑osN ⊆ E)
    (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osCallPerm (L := L) (callKey R p) q -∗
      osLogLb (L := L) n -∗
      (∀ (t s0 : Nat), ⌜n ≤ s0⌝ -∗ osCallS (L := L) t s0 p q -∗ osLogLb (L := L) s0 -∗
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
  have hΓc : Γc !! t' = none := (hc.fresh h1').1
  imod gAuth_insert _ _ _ _ (((st.fs.metaLog.length, p), q) : CallV) hΓc $$ Hacs with ⟨Hacs, Hk⟩
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
    iexists Γdf, <[t' := (((st.fs.metaLog.length, p), q) : CallV)]> Γc, Γg
    try unfold callResS
    iframe Has Hadfs Hacs HAg Hgr
    isplitr
    · ipureintro
      exact ⟨⟨hw.roots, hw.hist, hw.dfds, hw.disj, hw.files_lt⟩, treeCohS_begin hc t' p q h1'⟩
    · try unfold callResS
      iapply (BigSepM.bigSepM_insert (Φ := fun (_t : Nat) (x : CallV) =>
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm (callKey st.fs.roots x.1.2)
          (DFrac.own x.2) ()) hΓc).2
      iframe Hcr
      unfold osCallPerm; rw [hR]; iexact Hq
  iapply wp_value'
  unfold osCallS
  iapply HΦ $$ %t' %st.fs.metaLog.length %hn.2 Hk Hlb'

end specs

end Fs
end Perennial

end
