/-
The shared mode of the tree: what claims and spines say of the state (`osNames_entry`,
`osPathS_lookup`), and the steps of a call that only end it (`wp_callEndS`): `LstatDir`, and the
no-effect cases of `Unlink`, `Rmdir` and `Rename`. `TreeShared.lean` states the specs and takes
their proofs from here. Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedDirFd

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- The shared coherence with a logging call ended. -/
theorem treeCohS_metaEnd {st : OsState} {s0 : Nat} {Γdf : GMap w64 (Ino × DirPhS)}
    {Γc Γg : GMap Nat (Nat × Qp)} (hc : TreeCohS st s0 Γdf Γc Γg) (k : Nat) {xk : Nat × Qp}
    (hk : Γc !! k = some xk) :
    TreeCohS (st.metaEnd k) s0 Γdf (GMap.delete k Γc) Γg := by
  refine ⟨hc.starts, hc.pss, hc.dox, hc.valid, hc.s0le, hc.fds,
    fun fd x df hx hdf => (hc.ph fd x df hx hdf).congr rfl rfl, fun t0 x hx => ?_, fun t0 x hx => ?_,
    fun t0 x hx hq => ?_, fun t0 x hx y ey hy hd => ?_, fun t0 x hx => ?_, fun t0 x hx => ?_,
    fun t0 s hs => ?_, fun c x t0 g hx hg hq hle => ?_⟩
  · show (GMap.delete k st.proc.calls) !! t0 = _
    by_cases h0 : k = t0
    · subst h0; simp at hx
    · rw [GMap.lookup_delete_ne _ h0] at hx; rw [GMap.lookup_delete_ne _ h0]; exact hc.calls t0 x hx
  · by_cases h0 : k = t0
    · subst h0; simp at hx
    · rw [GMap.lookup_delete_ne _ h0] at hx; exact hc.callsLe t0 x hx
  · by_cases h0 : k = t0
    · subst h0; simp at hx
    · rw [GMap.lookup_delete_ne _ h0] at hx; exact hc.whole t0 x hx hq
  · by_cases h0 : k = t0
    · subst h0; simp at hx
    · rw [GMap.lookup_delete_ne _ h0] at hx; exact hc.after t0 x hx y ey hy hd
  · show (GMap.delete k st.proc.calls) !! t0 = _
    by_cases h0 : k = t0
    · subst h0; have := hc.gdisj k x hx; rw [hk] at this; cases this
    · rw [GMap.lookup_delete_ne _ h0]; exact hc.gcalls t0 x hx
  · by_cases h0 : k = t0
    · subst h0; simp
    · rw [GMap.lookup_delete_ne _ h0]; exact hc.gdisj t0 x hx
  · change (GMap.delete k st.proc.calls) !! t0 = some s at hs
    by_cases h0 : k = t0
    · subst h0; simp at hs
    · rw [GMap.lookup_delete_ne _ h0] at hs; rw [GMap.lookup_delete_ne _ h0]; exact hc.cover t0 s hs
  · by_cases h0 : k = c
    · subst h0; simp at hx
    · rw [GMap.lookup_delete_ne _ h0] at hx; exact hc.pair c x t0 g hx hg hq hle

/-- The shared coherence with a guard call ended. -/
theorem treeCohS_guardEnd {st : OsState} {s0 : Nat} {Γdf : GMap w64 (Ino × DirPhS)}
    {Γc Γg : GMap Nat (Nat × Qp)} (hc : TreeCohS st s0 Γdf Γc Γg) (t : Nat) {xt : Nat × Qp}
    (ht : Γg !! t = some xt) :
    TreeCohS (st.metaEnd t) s0 Γdf Γc (GMap.delete t Γg) := by
  have htc := hc.gdisj t xt ht
  refine ⟨hc.starts, hc.pss, hc.dox, hc.valid, hc.s0le, hc.fds,
    fun fd x df hx hdf => (hc.ph fd x df hx hdf).congr rfl rfl, fun t0 x hx => ?_, hc.callsLe,
    hc.whole, hc.after, fun t0 x hx => ?_, fun t0 x hx => ?_,
    fun t0 s hs => ?_, fun c x t0 g hx hg hq hle => ?_⟩
  · show (GMap.delete t st.proc.calls) !! t0 = _
    by_cases h0 : t = t0
    · subst h0; rw [htc] at hx; cases hx
    · rw [GMap.lookup_delete_ne _ h0]; exact hc.calls t0 x hx
  · show (GMap.delete t st.proc.calls) !! t0 = _
    by_cases h0 : t = t0
    · subst h0; simp at hx
    · rw [GMap.lookup_delete_ne _ h0] at hx; rw [GMap.lookup_delete_ne _ h0]; exact hc.gcalls t0 x hx
  · by_cases h0 : t = t0
    · subst h0; simp at hx
    · rw [GMap.lookup_delete_ne _ h0] at hx; exact hc.gdisj t0 x hx
  · change (GMap.delete t st.proc.calls) !! t0 = some s at hs
    by_cases h0 : t = t0
    · subst h0; simp at hs
    · rw [GMap.lookup_delete_ne _ h0] at hs; rw [GMap.lookup_delete_ne _ h0]; exact hc.cover t0 s hs
  · by_cases h0 : t = t0
    · subst h0; simp at hg
    · rw [GMap.lookup_delete_ne _ h0] at hg; exact hc.pair c x t0 g hx hg hq hle

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- A claim's names hold, in the state, what the claim knows. -/
theorem osNames_entry {st : OsState} {Γn : GMap (Ino × NameSet) NamesH}
    (hcoh : NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn) (j : Ino) (N : NameSet) (dq : DFrac)
    (h : NamesH) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ osNames (L := L) j N dq h -∗
      ⌜∀ b, N.Mem b → st.tree.entry j b = h.cur !! b⌝ := by
  iintro HA H
  icases osNames_auth L hcoh j N dq h $$ HA H with %hh
  ipureintro
  intro b hb
  rw [hh]
  simp only [namesOf]
  rw [restrictN_lookup _ _ _ hb, entsOf_lookup]
  rfl

/-- A spine is a walk of the state's tree. -/
theorem osSpine_walk {st : OsState} {Γn : GMap (Ino × NameSet) NamesH}
    (hcoh : NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn) (cs : List GoString) (j0 : Ino)
    (dq : DFrac) (j : Ino) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ osSpine (L := L) j0 cs dq j -∗
      ⌜walk st.tree (.dir j0) cs = some (.dir j)⌝ := by
  induction cs generalizing j0 with
  | nil =>
    rw [osSpine_nil]
    iintro HA %h
    ipureintro; rw [h]; rfl
  | cons c cs ih =>
    rw [osSpine_cons]
    iintro HA ⟨%h, %J, Hn, %hJ, Hs⟩
    icases osNames_entry hcoh j0 (.only [c]) dq h $$ HA Hn with %he
    icases ih J $$ HA Hs with %hw
    ipureintro
    have he' : st.tree.entry j0 c = some (.dir J) := by
      rw [he c (by simp [NameSet.Mem]), hJ]
    simp only [walk, he']
    exact hw

/-- A path's spine: the path names its directory in the state. -/
theorem osPathS_lookup {st : OsState} {R : Roots} {Γn : GMap (Ino × NameSet) NamesH}
    (hR : st.fs.roots = R) (hcoh : NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn) (p : GoString)
    (dq : DFrac) (j : Ino) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ osPathS (L := L) R p dq j -∗
      ⌜st.lookup p = some (.dir j)⌝ := by
  unfold osPathS
  iintro HA ⟨%r, %j0, %cs, %hp, Hs⟩
  icases osSpine_walk hcoh cs j0 dq j $$ HA Hs with %hw
  ipureintro
  obtain ⟨hRk, hm, hcs, rfl⟩ := hp
  subst hR
  rw [lookup_joinPath hRk hm hcs, hw]

end facts

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- A shared call excludes the legacy mode. -/
theorem legacy_callS_excl (st : OsState) (k s0 : Nat) (q : Qp) :
    ⊢ osCallS (L := L) k s0 q -∗ treeLegacy (gooseOsGS (L := L)) st -∗ False := by
  unfold treeLegacy legacyHolds osCallS
  iintro Hk ⟨%V0, %Γdf, %Γc, %hns, -, -, -, -, -, -, -, Hacs, -⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ Hacs Hk with %hl
  simp at hl

/-- **A step that only ends the call `k`**, from what it finds of the state (`P`, given by the
caller's resources `F` through the claims' authority) and what it returns (`W`). -/
theorem wp_callEndS (op : String) (v : val) (hv : v.isPanic = false) (R : Roots) (k s0 : Nat)
    (q : Qp) (F : IProp GF) (P : OsState → Prop) (W : val → Prop)
    (hF : ∀ st Γn, st.fs.roots = R → NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ F -∗ ⌜P st⌝)
    (hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 → P st →
      ∃ e', IsFsStep op v st e' (st.metaEnd k))
    (hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 → P st →
      IsFsStep op v st e' st' → st' = st.metaEnd k ∧ ∃ w, e' = Val w ∧ W w)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ F -∗ osCallS (L := L) k s0 q -∗
      (∀ w, ⌜W w⌝ -∗ osCallPerm (L := L) q -∗ F -∗ Φ w) -∗
      WP (ExternalOp fsExt.name op (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi HF Hk HΦ
  iapply wp_fs_stepM op _ Φ hv hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Ht
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
  icases hF st Γn hR hcoh.2 $$ HAn HF with %hP
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
  unfold osCallS
  icases gAuth_lookup _ _ _ _ _ _ $$ Hacs Hk with %hk
  have hcall : st.proc.calls !! k = some s0 := hc.calls k _ hk
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hs : FilesSame st (st.metaEnd k) := filesSame_metaEnd st k
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨e', hst⟩ := hprog st hw hR hcall hP
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 hs Hag
    exact ⟨e', h, _, hst, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  imod Hclose2
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  obtain ⟨rfl, w, rfl, hW⟩ := hpost st e' st' hw hR hcall hP Hst
  imod osWorld_filesSame (st := st) (st' := st.metaEnd k) hs Hr Hfr
    $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
  · unfold osWorld; iframe; ipureintro; exact Hwc
  unfold callResS
  icases (BigSepM.bigSepM_delete (M := GMap Nat)
    (Φ := fun (_t : Nat) (x : Nat × Qp) =>
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm () (DFrac.own x.2) ()) hk).1 $$ Hcr
    with ⟨Hq, Hcr⟩
  imod gAuth_delete _ _ _ _ _ $$ Hacs Hk with Hacs
  imodintro
  iexists Γb, Γm, Γf, Γt
  isplitl [Hw]
  · unfold osWorld; iexact Hw
  isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr HAg Hgr Hcm]
  · try unfold treeCtx
    isplitr [Hcm]
    rotate_left
    · iapply commitRes_grow (gooseOsGS (L := L)) (st := st) (st' := st.metaEnd k) (commitGrows_of_eq rfl) $$ Hcm
    iright
    simp only [OsState.metaEnd]
    try unfold treeShared
    iexists V0, s1, Γdf, GMap.delete k Γc, Γg
    iframe
    ipureintro; exact ⟨fsTreeWf_metaEnd hw k, treeCohS_metaEnd hc k hk⟩
  iapply wp_value'
  iapply HΦ $$ %w %hW [Hq] HF
  unfold osCallPerm; iexact Hq

end specs

end Fs
end Perennial

end
