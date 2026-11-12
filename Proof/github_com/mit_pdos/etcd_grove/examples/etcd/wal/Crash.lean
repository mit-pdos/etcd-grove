/-
Lean-first (no Rocq counterpart).

# The tester's crash (WAL W4c step 2; plan §2.4)

`tester_crash`: the crash obligation of `goose_crash_adequacy` for the tester. It runs at `⊤` and
cannot refute the crash, so it opens the old generation's invariant (`TInv`) and closes it again with
its contents, through the crash lemmas that keep the old generation's resources (decision Q1:
`durableOwnM_crash_keep`, `walDiskAt_crash_keep`, `walDiskAt_crash_any_keep0`, `walAbsent_crash_keep`,
`dirDurable_crash_keep`, `walArea_crash_keep`); the new generation's copies make its invariant, with
fresh ghost variables holding the same oracle and the crashed WAL state. The oracle does not change:
the crash image is an image of the old WAL state's history at its synced mark, so an image of the
accounting candidate's history (`walImg_trans`), and the crash only lowers `unl`, `pur`, `cut`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Defs
public import GooseLang.Ext.Durable.Crash

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The relation across a crash (pure) -/

section pure
variable [GooseExts]

/-- **The accounting survives the crash**: the crashed state (an image `I` of `d.H` at the
candidate's mark, `unl` and `pur` clamped, the read position `k ≤ min pur |I|`) is accounted for by
the same candidate. -/
theorem tCandOk_crash {o : TOracle} {c : TCand} {d : WalDur} {I : List (WalOpG WalEnt)} {k : Nat}
    (hc : tCandOk o c d) (hI : walImg d.H (tCandMark o c) I) (hk : k ≤ min d.pur I.length) :
    tCandOk o c { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length } := by
  obtain ⟨himg, hpur, -, hunl, hsz, hwf⟩ := hc
  refine ⟨?_, ?_, ?_, ?_, hsz, hwf⟩
  · exact walImg_trans himg (walImg_map WalOpG.toM WalEnt.toM (fun _ _ => rfl) hI)
  · exact Nat.le_trans (Nat.min_le_left _ _) hpur
  · exact Nat.le_trans (Nat.le_trans hk (Nat.min_le_left _ _)) hpur
  · exact Nat.le_trans (Nat.min_le_left _ _) hunl

/-- **`Create`'s fresh WAL survives the crash** (or vanishes): its crash image is empty, and the
clamped positions stay 0. -/
theorem tPreOk_crash {o : TOracle} {d : WalDur} {I : List (WalOpG WalEnt)} {k : Nat}
    (hd : d.H = [] ∧ d.unl = 0 ∧ d.pur = 0 ∧ d.cut = 0 ∧ d.sized = true)
    (hI : walImg d.H 0 I) (hk : k ≤ min d.pur I.length) (ho : o = tFreshOracle) :
    tPreOk o (some { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length }) := by
  obtain ⟨hH, hu, hp, -, hs⟩ := hd
  have hI0 : I = [] := by
    have := walImg_length_le hI
    rw [hH] at this
    exact List.eq_nil_of_length_eq_zero (Nat.le_zero.mp this)
  refine ⟨ho, Or.inr ⟨_, rfl, hI0, ?_, ?_, ?_, hs⟩⟩
  · simp only [hu, Nat.zero_min]
  · simp only [hp, Nat.zero_min]
  · rw [hp, Nat.zero_min] at hk; exact Nat.le_zero.mp hk

end pure

/-! ## The crash obligation -/

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt absDiskExt] [HasExt durableExt]
  [GoGlobalContext] [go.IntoValInj GoString]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable [AllG GF]

/-- The new generation's reservation, from its durable ownership in a reserving mode. -/
theorem durableOwnM_reserved (L' : GooseLocalGS GF) (r : GoString) (fs : DurableState) :
    ⊢@{IProp GF} durableOwnM (L := L') (some r) fs -∗
      durableOwnM (L := L') (some r) fs ∗ durableReserved (L := L') r := by
  simp only [durableOwnM, durableOwnR]
  iintro ⟨Hv, #Hr⟩
  iframe Hv Hr

/-- **The tester's crash** (plan §2.4): from the old generation's invariant and the extensions'
crash starts, the new generation's boot precondition (`TBoot`), with the oracle unchanged. -/
theorem tester_crash (L' : GooseLocalGS GF) (root : GoString) (γo γw : GName) :
    ⊢@{IProp GF} TInv (L := L) root γo γw -∗
      durable_crash_interp.crashStart (gooseDurableGS (L := L)) (gooseDurableGS (L := L')) -∗
      absDiskCrashStart (gooseAbsDiskGS (L := L)) (gooseAbsDiskGS (L := L')) ={⊤}=∗
      TBoot (L := L') root := by
  iintro #Hinv Hdc Hac
  icases (absDiskCrashStart_split (L := L) L').1 $$ Hac with ⟨Hcw, Htok⟩
  unfold TInv
  iinv Hinv with >Hb Hclose
  iunfold TInvBody at Hb
  icases Hb with ⟨%fs, %om, %o, %od, Hdur, %Hom, %Hfile, Ho, Hw, Hgw, HR, #Harea, #Hroot,
    Hda, Hres⟩
  -- the durable side: the old ownership kept, the new generation's in the same mode
  icases durableOwnM_crash_keep L L' om fs $$ Hdc Hdur with ⟨Hdur, Hdur'⟩
  -- the persistent facts of the abstract disk, keeping the crash start
  icases walArea_crash_keep (L := L) L' (tArea root) $$ Hcw Harea with ⟨Hcw, #Harea'⟩
  icases dirDurable_crash_keep (L := L) L' root $$ Hcw Hroot with ⟨Hcw, #Hroot'⟩
  -- the WAL, by phase, and the area's durability
  ihave HX : (iprop(∃ od' : Option WalDur, walDirIs (L := L) (tWalDir root) od ∗
      walDirIs (L := L') (tWalDir root) od' ∗ tRelI (L := L') root o od' ∗
      (if o.created ∨ od.isSome then dirDurable (L := L) (tArea root) else iprop(True)) ∗
      (if o.created ∨ od'.isSome then dirDurable (L := L') (tArea root) else iprop(True)) ∗
      tRelI (L := L) root o od) : IProp GF) $$ [Hcw Hw HR Hda]
  · cases hcr : o.created with
    | true =>
      simp only [tRelI, hcr, ite_true]
      icases HR with ⟨%d, %c, %hdc, #Hsy, #Hnm⟩
      obtain ⟨hod, hcm, hok⟩ := hdc
      subst hod
      simp only [true_or, ite_true]
      icases Hda with #Hda
      icases dirDurable_crash_keep (L := L) L' (tArea root) $$ Hcw Hda with ⟨Hcw, #Hda'⟩
      have hk := walDiskAt_crash_keep (L := L) L' (tWalDir root) d (tCandMark o c)
      unfold walDiskAt at hk
      icases hk $$ Hcw Hw Hsy Hnm
        with ⟨Hw, %I, %k, %hIk, Hw', #Hsy', #Hnm'⟩
      obtain ⟨hI, hk⟩ := hIk
      iexists some { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length }
      iframe Hw Hw' Hda Hda'
      isplitr
      · iexists _, c
        iframe Hsy' Hnm'
        ipureintro; exact ⟨rfl, hcm, tCandOk_crash hok hI hk⟩
      · iexists d, c
        iframe Hsy Hnm
        ipureintro; exact ⟨rfl, hcm, hok⟩
    | false =>
      simp only [tRelI, hcr, Bool.false_eq_true, ite_false]
      icases HR with %hpre
      obtain ⟨hfresh, hnone | ⟨d, hod, hd⟩⟩ := hpre
      · subst hnone
        have hk := walAbsent_crash_keep (L := L) L' (tWalDir root)
        unfold walAbsent at hk
        icases hk $$ Hcw Hw with ⟨Hw, Hw'⟩
        iexists none
        iframe Hw Hw'
        simp only [Bool.false_eq_true, Option.isSome_none, _root_.or_self, ite_false]
        isplitr; ipureintro; exact ⟨hfresh, Or.inl rfl⟩
        isplitr; itrivial
        isplitr; itrivial
        ipureintro; exact ⟨hfresh, Or.inl rfl⟩
      · subst hod
        simp only [Bool.false_eq_true, Option.isSome_some, _root_.false_or, ite_true]
        icases Hda with #Hda
        icases dirDurable_crash_keep (L := L) L' (tArea root) $$ Hcw Hda with ⟨Hcw, #Hda'⟩
        have hk := walDiskAt_crash_any_keep0 (L := L) L' (tWalDir root) d
        unfold walDiskAt walAbsent at hk
        icases hk $$ Hcw Hw with ⟨Hw, Hcr⟩
        icases Hcr with (⟨Hw', %-⟩ | ⟨%I, %k, %hIk, Hw'⟩)
        · iexists none
          simp only [Bool.false_eq_true, Option.isSome_none, _root_.or_self, ite_false]
          iframe Hw Hw' Hda
          isplitr; ipureintro; exact ⟨hfresh, Or.inl rfl⟩
          isplitr; itrivial
          ipureintro; exact ⟨hfresh, Or.inr ⟨d, rfl, hd⟩⟩
        · obtain ⟨hI, hk⟩ := hIk
          iexists some { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length }
          simp only [Option.isSome_some, or_true, ite_true]
          iframe Hw Hw' Hda Hda'
          isplitr; ipureintro; exact tPreOk_crash hd hI hk hfresh
          ipureintro; exact ⟨hfresh, Or.inr ⟨d, rfl, hd⟩⟩
  icases HX with ⟨%od', Hw, Hw', HR', Hda, Hda', HR⟩
  -- the reservation, in the new generation
  ihave HY : (iprop((if om.isSome then durableReserved (L := L) (tArea root) else iprop(True)) ∗
      durableOwnM (L := L') om fs ∗
      (if om.isSome then durableReserved (L := L') (tArea root) else iprop(True))) : IProp GF)
      $$ [Hres Hdur']
  · rcases Hom with rfl | rfl
    · simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
      iframe Hdur'
      try (isplitl <;> itrivial)
    · simp only [Option.isSome_some, ite_true]
      icases durableOwnM_reserved L' (tArea root) fs $$ Hdur' with ⟨Hdur', #Hr'⟩
      iframe Hres Hdur' Hr'
  icases HY with ⟨Hres, Hdur', Hres'⟩
  -- close the old invariant with its contents
  imod Hclose $$ [Hdur Ho Hw Hgw HR Hda Hres] with -
  · inext
    unfold TInvBody
    iexists fs, om, o, od
    iframe Hdur Ho Hw Hgw HR Hda Hres Harea Hroot
    ipureintro; exact ⟨Hom, Hfile⟩
  -- the new generation's invariant
  imod ghostVar_alloc (GF := GF) o with ⟨%γo', Ho'⟩
  icases (ghostVar_split_half (GF := GF) γo' 1 o).1 $$ Ho' with ⟨Ho1, Ho2⟩
  imod ghostVar_alloc (GF := GF) od' with ⟨%γw', Hw''⟩
  icases (ghostVar_split_half (GF := GF) γw' 1 od').1 $$ Hw'' with ⟨Hw1, Hw2⟩
  imod inv_alloc walN ⊤ (TInvBody (L := L') root γo' γw') $$ [Hdur' Ho1 Hw' Hw1 HR' Hda' Hres']
    with #Hinv'
  · inext
    unfold TInvBody
    iexists fs, om, o, od'
    iframe Hdur' Ho1 Hw' Hw1 HR' Hda' Hres' Harea' Hroot'
    ipureintro; exact ⟨Hom, Hfile⟩
  imodintro
  unfold TBoot TInv
  iexists γo', γw', o, od'
  iframe Hinv' Ho2 Hw2 Htok

end crash

end etcd_wal
end EtcdGrove
end Perennial
