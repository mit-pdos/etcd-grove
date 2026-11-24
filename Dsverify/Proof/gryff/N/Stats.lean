/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/Stats.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: `stats.(*StatsMap)` methods over `statsOk`'s body (`netN.statsOkB`)

`Max` / `Add` / `Increment` on a key outside `strIntKeys` (an `int` entry), `IncrementStrInt` on
a key of `strIntKeys` (a `map[string]int` entry): with the keys' kinds (hub request H1-R5 / N-3)
neither type assertion panics.
-/
module

public import Dsverify.Proof.gryff.N.NetDefs
public import Dsverify.Proof.gryff.Replica.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.netN

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [stA : src.stats.Assumptions]


set_option goose.wp.extras true

theorem wp_Max (st : Loc) (key : GoString) (v : w64) (hk : key ∉ strIntKeys) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.stats ∗ statsOkB st }}
      (App (App (Val (st @!! go.GoType.PointerType src.stats.StatsMap.ty @!! go!"Max"))
        (Val #key)) (Val #v))
    {{ (n : w64), RET #n; True }} := by
  wp_start as Hst
  iunfold statsOkB at Hst
  icases Hst with #⟨%sm, Hsm, Hmu⟩
  iStructNamed Hsm
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, ⟨%M, HM, Hvals⟩⟩
  wp_apply (wp_map_lookup2 (V := GoInterface) go.string _ sm.stats' M key (DFrac.own 1)) $$ HM as HM
  -- the entry is an `int`, or absent: `cur`
  ihave %Hcur : ⌜∃ cur : w64, (M !! key = none ∧ cur = W64 0) ∨
      M !! key = some (interface.mkOk go.int #cur)⌝ $$ [Hvals]
  · cases hx : M !! key with
    | none => ipureintro; exact ⟨W64 0, Or.inl ⟨rfl, rfl⟩⟩
    | some x =>
      ihave ⟨Hx, -⟩ := (BigSepM.bigSepM_lookup_acc hx).1 $$ Hvals
      unfold statValB
      rw [if_neg hk]
      icases Hx with %hn
      obtain ⟨n, hn⟩ := hn
      ipureintro; exact ⟨n, Or.inr (by rw [hn])⟩
  obtain ⟨cur, hcur⟩ := Hcur
  rcases hcur with ⟨hnone, rfl⟩ | hsome
  · rw [hnone]
    simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
    wp_auto
    wp_if_destruct <;>
    · (try wp_auto)
      wp_apply (wp_mapInsert (V := GoInterface) go.string sm.stats' M key _) $$ HM as HM
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HM Hvals]
      · iexists _
        iframe HM
        iapply BigSepM.bigSepM_insert_elim $$ [] Hvals
        unfold statValB; rw [if_neg hk]; ipureintro; exact ⟨_, rfl⟩
      (try wp_auto)
      iapply HΦ; itrivial
  · rw [hsome]
    simp only [Option.isSome_some, _root_.decide_true, Bool.not_true, Option.getD_some]
    wp_auto
    wp_if_destruct <;>
    · (try wp_auto)
      wp_apply (wp_mapInsert (V := GoInterface) go.string sm.stats' M key _) $$ HM as HM
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HM Hvals]
      · iexists _
        iframe HM
        iapply BigSepM.bigSepM_insert_elim $$ [] Hvals
        unfold statValB; rw [if_neg hk]; ipureintro; exact ⟨_, rfl⟩
      (try wp_auto)
      iapply HΦ; itrivial

theorem wp_Add (st : Loc) (key : GoString) (v : w64) (hk : key ∉ strIntKeys) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.stats ∗ statsOkB st }}
      (App (App (Val (st @!! go.GoType.PointerType src.stats.StatsMap.ty @!! go!"Add"))
        (Val #key)) (Val #v))
    {{ (n : w64), RET #n; True }} := by
  wp_start as Hst
  iunfold statsOkB at Hst
  icases Hst with #⟨%sm, Hsm, Hmu⟩
  iStructNamed Hsm
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, ⟨%M, HM, Hvals⟩⟩
  wp_apply (wp_map_lookup2 (V := GoInterface) go.string _ sm.stats' M key (DFrac.own 1)) $$ HM as HM
  ihave %Hcur : ⌜∃ cur : w64, (M !! key = none ∧ cur = W64 0) ∨
      M !! key = some (interface.mkOk go.int #cur)⌝ $$ [Hvals]
  · cases hx : M !! key with
    | none => ipureintro; exact ⟨W64 0, Or.inl ⟨rfl, rfl⟩⟩
    | some x =>
      ihave ⟨Hx, -⟩ := (BigSepM.bigSepM_lookup_acc hx).1 $$ Hvals
      unfold statValB
      rw [if_neg hk]
      icases Hx with %hn
      obtain ⟨n, hn⟩ := hn
      ipureintro; exact ⟨n, Or.inr (by rw [hn])⟩
  obtain ⟨cur, hcur⟩ := Hcur
  rcases hcur with ⟨hnone, rfl⟩ | hsome
  · rw [hnone]
    simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
    wp_auto
    wp_apply (wp_mapInsert (V := GoInterface) go.string sm.stats' M key _) $$ HM as HM
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HM Hvals]
    · iexists _
      iframe HM
      iapply BigSepM.bigSepM_insert_elim $$ [] Hvals
      unfold statValB; rw [if_neg hk]; ipureintro; exact ⟨_, rfl⟩
    (try wp_auto)
    iapply HΦ; itrivial
  · rw [hsome]
    simp only [Option.isSome_some, _root_.decide_true, Bool.not_true, Option.getD_some]
    wp_auto
    wp_apply (wp_mapInsert (V := GoInterface) go.string sm.stats' M key _) $$ HM as HM
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HM Hvals]
    · iexists _
      iframe HM
      iapply BigSepM.bigSepM_insert_elim $$ [] Hvals
      unfold statValB; rw [if_neg hk]; ipureintro; exact ⟨_, rfl⟩
    (try wp_auto)
    iapply HΦ; itrivial

theorem wp_Increment (st : Loc) (key : GoString) (hk : key ∉ strIntKeys) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.stats ∗ statsOkB st }}
      (App (Val (st @!! go.GoType.PointerType src.stats.StatsMap.ty @!! go!"Increment"))
        (Val #key))
    {{ (n : w64), RET #n; True }} := by
  wp_start as Hst
  wp_auto
  wp_apply wp_Add st key (W64 1) hk $$ [$Hst] as %n -
  iapply HΦ; itrivial

section strconvS
variable [strconv.Assumptions]

theorem wp_IncrementStrInt (st : Loc) (key : GoString) (idx : w64) (hk : key ∈ strIntKeys) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.stats ∗ statsOkB st }}
      (App (App (Val (st @!! go.GoType.PointerType src.stats.StatsMap.ty @!! go!"IncrementStrInt"))
        (Val #key)) (Val #idx))
    {{ (n : w64), RET #n; True }} := by
  wp_start as Hst
  iunfold statsOkB at Hst
  icases Hst with #⟨%sm, Hsm, Hmu⟩
  iStructNamed Hsm
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, ⟨%M, HM, Hvals⟩⟩
  wp_apply (wp_map_lookup2 (V := GoInterface) go.string _ sm.stats' M key (DFrac.own 1)) $$ HM as HM
  -- the entry is a `map[string]int`, or absent: its map `cm`
  ihave Hcm : ((⌜M !! key = none⌝ ∗ [∗map] k ↦ v ∈ M, statValB k v) ∨ ∃ (cm : Loc) (CM : GMap GoString w64),
      ⌜M !! key = some (interface.mkOk (go.GoType.MapType go.string go.int) #cm)⌝ ∗ cm ↦$ CM ∗
      [∗map] k ↦ v ∈ M.delete key, statValB k v) $$ [Hvals]
  · cases hx : M !! key with
    | none => ileft; iframe Hvals; ipureintro; rfl
    | some x =>
      iright
      ihave ⟨Hx, Hrest⟩ := BigSepM.bigSepM_delete hx $$ Hvals
      unfold statValB
      rw [if_pos hk]
      icases Hx with ⟨%cm, %hv, %CM, Hc⟩
      subst hv
      iexists cm, CM
      iframe
      ipureintro; rfl
  icases Hcm with (⟨%hnone, Hvals⟩ | ⟨%cm, %CM, %hsome, Hc, Hrest⟩)
  · rw [hnone]
    simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
    wp_auto
    wp_apply (wp_map_make1 (K := GoString) (V := w64) go.string go.int) as %cm Hc
    wp_apply (wp_mapInsert (V := GoInterface) go.string sm.stats' M key _) $$ HM as HM
    ihave #Hdeps := isPkgInit_unfold_deps pkg_id.gryff.src.stats $$ Hpkg
    isimp only [isPkgInitDeps] at Hdeps
    icases Hdeps with ⟨-, #Hsc, -⟩
    wp_apply strconv.wp_Itoa $$ [$Hsc]
    generalize internal.strconv.fmtInt idx (W64 10) = is
    wp_apply (wp_map_lookup2 (V := w64) go.string _ cm _ is (DFrac.own 1)) $$ Hc as Hc
    wp_apply (wp_mapInsert (V := w64) go.string cm _ is _) $$ Hc as Hc
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HM Hvals Hc]
    · iexists _
      iframe HM
      iapply BigSepM.bigSepM_insert_elim $$ [Hc] Hvals
      unfold statValB; rw [if_pos hk]
      iexists cm; isplitr; · ipureintro; rfl
      iexists _; iexact Hc
    iapply HΦ; itrivial
  · rw [hsome]
    simp only [Option.isSome_some, _root_.decide_true, Bool.not_true, Option.getD_some]
    wp_auto
    wp_apply (wp_mapInsert (V := GoInterface) go.string sm.stats' M key _) $$ HM as HM
    ihave #Hdeps := isPkgInit_unfold_deps pkg_id.gryff.src.stats $$ Hpkg
    isimp only [isPkgInitDeps] at Hdeps
    icases Hdeps with ⟨-, #Hsc, -⟩
    wp_apply strconv.wp_Itoa $$ [$Hsc]
    generalize internal.strconv.fmtInt idx (W64 10) = is
    wp_apply (wp_map_lookup2 (V := w64) go.string _ cm _ is (DFrac.own 1)) $$ Hc as Hc
    wp_if_destruct <;>
    · (try wp_auto)
      wp_apply (wp_mapInsert (V := w64) go.string cm _ is _) $$ Hc as Hc
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HM Hrest Hc]
      · iexists _
        iframe HM
        iapply (BigSepM.bigSepM_insert_delete).2
        iframe Hrest
        unfold statValB; rw [if_pos hk]
        iexists cm; isplitr; · ipureintro; rfl
        iexists _; iexact Hc
      (try wp_auto)
      iapply HΦ; itrivial

end strconvS

end

end Perennial.gryff.netN
