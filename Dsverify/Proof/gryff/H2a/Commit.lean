/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2a/Commit.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2a: `updateCommitted`
-/
module

public import Dsverify.Proof.gryff.H2a.AttrEnv
public import Dsverify.Proof.gryff.Wire.Proof.Lemmas
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)
open Perennial.gryff.replica (XS rowOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF] -- H1-R6 / N-1
variable [sortA : Perennial.gryff.replica2.SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

/-- `updateCommitted(replica)`. -/
theorem wp_updateCommitted' (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) (xs : XS) (s s' : RState)
    (q : w32) (hq : 0 ≤ sint.Z q ∧ sint.Z q < 3) (hres : model.updateCommitted s q = some s') :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ attrEnv k r gR h ∗
        epaxosOwn ρ h r xs s }}
      (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!! go!"updateCommitted"))
        (Val #q))
    {{ RET #(); epaxosOwn ρ h r xs s' }} := by
  unfold model.updateCommitted at hres
  cases hk : model.advanceCut s q (model.SLOTS.toNat + 1) (s.cut q) with
  | none => simp [hk] at hres
  | some kf =>
  simp only [hk] at hres
  have hs' : s' = { s with committedUpTo := s.committedUpTo.setAt q.toNat kf } := by
    simpa using hres.symm
  subst hs'
  clear hres
  wp_start as ⟨#Hae, Hep⟩
  unfold attrEnv
  icases Hae with ⟨#HR, #HgR, #HId, #HN, -⟩
  ihave #Hdpkg : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog $$ []
  · solve_pkg_init
  ihave #Hdlog := replica.dlog_init_access $$ Hdpkg
  icases (epaxosOwn_open ..).1 $$ Hep with ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M, %cu, %pm,
    #HR', #HnoC, #HispS, #Hisp, #HcrtS, #Hc1S, #Hcfs, #HmsR, #HpvtR, Hcu, Hcrt, HM, HMe, Hrows, Hinsts,
    Hmono, Hconfs, Hms, Hpm, Hrest, %Hf⟩
  wp_auto
  have hqn : (sint.Z q).toNat = q.toNat := by
    have h1 : uint.Z q = sint.Z q := by word
    have h2 : uint.Z q = (q.toNat : Int) := rfl
    omega
  ihave %Hcul := array_len _ _ _ _ $$ Hcu
  have hcu0 : depsOf cu = s.committedUpTo.setAt q.toNat (s.cut q) := by
    rw [Hf.2.2.2.1]
    simp only [model.RState.cut, model.Deps.at, model.Deps.setAt]
    rw [← Hf.2.2.2.1]
    simp only [depsOf]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp
  ihave IH : iprop(∃ (kk : w32) (f : Nat) (cu' : GoArray w32 5),
      h.[src.gryff.EPaxosRMWHandler, go!"CommittedUpTo"] ↦ cu' ∗
      ⌜depsOf cu' = s.committedUpTo.setAt q.toNat kk ∧ model.advanceCut s q f kk = some kf⌝)
    $$ [Hcu]
  · iexists s.cut q, model.SLOTS.toNat + 1, cu; iframe; ipureintro; exact ⟨hcu0, hk⟩
  wp_for IH
  icases IH with ⟨Hcu, %Hinv⟩
  obtain ⟨hcu', hadv⟩ := Hinv
  rcases f with _ | f
  · simp [model.advanceCut] at hadv
  have hbox : model.inBox q (kk + 1) = true := by
    cases hb : model.inBox q (kk + 1) with
    | true => rfl
    | false => unfold model.advanceCut at hadv; simp only [hb] at hadv; cases hadv
  have hq5 : 0 ≤ sint.Z (W64 (sint.Z q)) ∧ sint.Z (W64 (sint.Z q)) < 5 := by
    have : sint.Z (W64 (sint.Z q)) = sint.Z q := by word
    omega
  have hkk : cu'.arr.getD (sint.Z (W64 (sint.Z q))).toNat (W32 0) = kk := by
    have : sint.Z (W64 (sint.Z q)) = sint.Z q := by word
    rw [this, hqn]
    have h1 := congrArg (fun l => List.getD l q.toNat (W32 0)) hcu'
    simp only [depsOf] at h1; rw [h1]
    simp only [model.Deps.setAt]
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self]
    · rfl
    · rw [← Hf.2.2.2.1]; simp only [depsOf]; omega
  obtain ⟨sq, hsq⟩ : ∃ sq, isp[q.toNat]? = some sq :=
    ⟨_, List.getElem?_eq_getElem (by rw [Hf.1]; omega)⟩
  icases rows_acc' M isp q.toNat sq hsq $$ Hrows with ⟨Hrow, Hrowsc⟩
  icases (Perennial.gryff.replica.rowOwn_open ..).1 $$ Hrow with ⟨%ptrs, Hrow, %Hrowf⟩
  ihave %HispSlen := ownSlice_len _ _ _ $$ Hisp
  ihave %Hsqlen := ownSlice_len _ _ _ $$ Hrow
  have hvb : 0 ≤ sint.Z (kk + 1) ∧ sint.Z (kk + 1) < model.SLOTS := by
    simp only [model.inBox, decide_eq_true_eq] at hbox; exact ⟨hbox.2.2.1, hbox.2.2.2⟩
  have hjw : sint.Z (W64 (sint.Z (kk + 1))) = sint.Z (kk + 1) := by word
  obtain ⟨p, hp⟩ : ∃ p, ptrs[(sint.Z (W64 (sint.Z (kk + 1)))).toNat]? = some p :=
    ⟨_, List.getElem?_eq_getElem (by
      rw [Hrowf.1, hjw]; unfold Perennial.gryff.replica.nSlots; unfold model.SLOTS at hvb; omega)⟩
  have hqi : 0 ≤ sint.Z (W64 (sint.Z q)) ∧ sint.Z (W64 (sint.Z q)) < sint.Z ispS.len := by
    have : sint.Z (W64 (sint.Z q)) = sint.Z q := by word
    rw [this]; have := HispSlen.1; rw [Hf.1] at this; word
  have hji : 0 ≤ sint.Z (W64 (sint.Z (kk + 1))) ∧ sint.Z (W64 (sint.Z (kk + 1))) < sint.Z sq.len := by
    rw [hjw]; have := Hsqlen.1; rw [Hrowf.1] at this
    unfold Perennial.gryff.replica.nSlots at this; unfold model.SLOTS at hvb; word
  have hisq : isp[(sint.Z (W64 (sint.Z q))).toNat]? = some sq := by
    have : sint.Z (W64 (sint.Z q)) = sint.Z q := by word
    rw [this, hqn]; exact hsq
  rw [ite_eq_left hqi]
  wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType
    src.gryff.Instance.ty)) ispS _ isp _ sq hqi.1 $$ [$Hisp] as -
  · ipureintro; exact hisq
  rw [ite_eq_left hq5]
  wp_apply wire.wp_load_arr32 $$ [$Hcu] as Hcu
  · ipureintro; exact hq5
  rw [hkk, show (W32 1 : w32) = 1 from rfl, ite_eq_left hji]
  wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sq
    _ ptrs _ p hji.1 $$ [$Hrow] as Hrow
  · ipureintro; exact hp
  have hMp := Hrowf.2 _ p hp
  rw [hjw] at hMp
  have hbx := Hf.2.2.2.2.2.2.1 q (kk + 1) hbox
  have hqZ : ((q.toNat : Nat) : Int) = sint.Z q := by omega
  have hjZ : (((sint.Z (kk + 1)).toNat : Nat) : Int) = sint.Z (kk + 1) := by omega
  rw [hqZ, hjZ] at hMp
  rw [hMp] at hbx
  by_cases hpn : p = Loc.null
  · -- `nil`: the loop ends at `kk`
    subst hpn
    have hnone : s.inst q (kk + 1) = none := by simpa using hbx
    have hkf : kf = kk := by
      unfold model.advanceCut at hadv; simp only [hbox, Bool.not_true] at hadv
      have hnone' : s.inst q (kk + 1#32) = none := hnone
      simp [hnone'] at hadv; exact hadv.symm
    subst hkf
    wp_auto
    have hft : (#false : val) ≠ #true := fun h => by simpa using go.intoVal_inj h
    rw [decide_eq_false hft]; simp only [Bool.false_eq_true, ↓reduceIte, _root_.decide_true]
    wp_auto
    ihave Hrow := (Perennial.gryff.replica.rowOwn_open M _ sq).2 $$ [Hrow]
    · iexists ptrs; iframe; ipureintro; exact Hrowf
    ihave Hrows := Hrowsc $$ %M %(fun _ _ _ => rfl) Hrow
    iapply HΦ
    iapply (epaxosOwn_open ..).2
    iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu', pm
    have hco : committedOrExecuted { s with committedUpTo := s.committedUpTo.setAt q.toNat kf } =
        committedOrExecuted s := rfl
    have hcrt : ∀ q', ({ s with committedUpTo := s.committedUpTo.setAt q.toNat kf } : RState).crt q' =
        s.crt q' := fun _ => rfl
    have hcf : ∀ q', ({ s with committedUpTo := s.committedUpTo.setAt q.toNat kf } : RState).confAt q' =
        s.confAt q' := fun _ => rfl
    simp only [instsRep, hco, hcrt, hcf]
    iframe # ∗
    ipureintro
    exact ⟨Hf.1, Hf.2.1, Hf.2.2.1, hcu', Hf.2.2.2.2⟩
  · obtain ⟨c, hc⟩ : ∃ c, s.inst q (kk + 1) = some c := by
      simp only [hpn, ite_false, Option.isSome_some] at hbx
      exact Option.isSome_iff_exists.1 hbx
    have hMq : M.lookup (sint.Z q, sint.Z (kk + 1)) = some p := by rw [hMp, if_neg hpn]
    icases insts_update ρ xs s M q (kk + 1) p c hMq hc $$ Hinsts with ⟨Hc, Hiclose⟩
    icases (copyRep_open ..).1 $$ Hc with ⟨%iv, Hiv, Hcmds, Hlb, %Hivf⟩
    have hst : iv.Status' = c.status := Hivf.2.1
    rw [decide_eq_false hpn]
    wp_auto
    rw [ite_eq_left hqi]
    wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType
      src.gryff.Instance.ty)) ispS _ isp _ sq hqi.1 $$ [$Hisp] as -
    · ipureintro; exact hisq
    rw [ite_eq_left hq5]
    wp_apply wire.wp_load_arr32 $$ [$Hcu] as Hcu
    · ipureintro; exact hq5
    rw [hkk]; try rw [show (W32 1 : w32) = 1 from rfl]
    rw [ite_eq_left hji]
    wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sq
      _ ptrs _ p hji.1 $$ [$Hrow] as Hrow
    · ipureintro; exact hp
    rw [hst]
    have htt : decide ((#true : val) = #true) = true := by simp
    have hft : decide ((#false : val) = #true) = false := by
      simp only [decide_eq_false_iff_not]; intro h; simpa using go.intoVal_inj h
    have hcont : c.status = model.St.COMMITTED ∨ c.status = model.St.EXECUTED →
        model.advanceCut s q f (kk + 1) = some kf := by
      intro hce
      unfold model.advanceCut at hadv
      simp only [hbox, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hadv
      have hc' : s.inst q (kk + 1#32) = some c := hc
      simp only [hc, hce, ite_true] at hadv
      exact hadv
    wp_if_destruct
    · have hce : c.status = model.St.COMMITTED ∨ c.status = model.St.EXECUTED := Or.inl Hif
      ihave Hc := (copyRep_open ρ xs _ p c).2 $$ [Hiv Hcmds Hlb]
      · iexists iv; iframe; ipureintro; exact Hivf
      ihave Hinsts := Hiclose $$ %s %c [] Hc
      · ipureintro; exact ⟨hc, fun _ _ _ => rfl⟩
      ihave Hrow := (Perennial.gryff.replica.rowOwn_open M _ sq).2 $$ [Hrow]
      · iexists ptrs; iframe; ipureintro; exact Hrowf
      ihave Hrows := Hrowsc $$ %M %(fun _ _ _ => rfl) Hrow
      have hadv' := hcont hce
      rw [ite_eq_left hq5]
      wp_apply wire.wp_load_arr32 $$ [$Hcu] as Hcu
      · ipureintro; exact hq5
      rw [hkk, ite_eq_left hq5]
      wp_apply wire.wp_store_arr32 $$ [$Hcu] as Hcu
      · ipureintro; exact hq5
      rw [ite_eq_left hq5]
      wp_apply wire.wp_load_arr32 $$ [$Hcu] as Hcu
      · ipureintro; exact hq5
      wp_apply wp_slice_literal (V := GoInterface) _
      isplitr
      · ipureintro; rfl
      iintro %_ ⟨-, -⟩
      wp_auto
      wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
      wp_for_post
      iframe
      iexists (kk + 1), f, (array.mk 5 (cu'.arr.set (sint.Z (W64 (sint.Z q))).toNat (kk + 1)))
      iframe; ipureintro
      refine ⟨?_, hadv'⟩
      have : sint.Z (W64 (sint.Z q)) = sint.Z q := by word
      rw [this, hqn]
      have h1 := hcu'
      simp only [depsOf] at h1 ⊢
      rw [h1]
      simp only [model.Deps.setAt, List.set_set]
    · rw [ite_eq_left hqi]
      wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType
        src.gryff.Instance.ty)) ispS _ isp _ sq hqi.1 $$ [$Hisp] as -
      · ipureintro; exact hisq
      rw [ite_eq_left hq5]
      wp_apply wire.wp_load_arr32 $$ [$Hcu] as Hcu
      · ipureintro; exact hq5
      rw [hkk]; try rw [show (W32 1 : w32) = 1 from rfl]
      rw [ite_eq_left hji]
      wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sq
        _ ptrs _ p hji.1 $$ [$Hrow] as Hrow
      · ipureintro; exact hp
      rw [hst]
      by_cases h5 : c.status = W8 5
      · have hce : c.status = model.St.COMMITTED ∨ c.status = model.St.EXECUTED := Or.inr h5
        rw [decide_eq_true h5, htt]; simp only [ite_true]
        ihave Hc := (copyRep_open ρ xs _ p c).2 $$ [Hiv Hcmds Hlb]
        · iexists iv; iframe; ipureintro; exact Hivf
        ihave Hinsts := Hiclose $$ %s %c [] Hc
        · ipureintro; exact ⟨hc, fun _ _ _ => rfl⟩
        ihave Hrow := (Perennial.gryff.replica.rowOwn_open M _ sq).2 $$ [Hrow]
        · iexists ptrs; iframe; ipureintro; exact Hrowf
        ihave Hrows := Hrowsc $$ %M %(fun _ _ _ => rfl) Hrow
        have hadv' := hcont hce
        wp_auto
        rw [ite_eq_left hq5]
        wp_apply wire.wp_load_arr32 $$ [$Hcu] as Hcu
        · ipureintro; exact hq5
        rw [hkk, ite_eq_left hq5]
        wp_apply wire.wp_store_arr32 $$ [$Hcu] as Hcu
        · ipureintro; exact hq5
        rw [ite_eq_left hq5]
        wp_apply wire.wp_load_arr32 $$ [$Hcu] as Hcu
        · ipureintro; exact hq5
        wp_apply wp_slice_literal (V := GoInterface) _
        isplitr
        · ipureintro; rfl
        iintro %_ ⟨-, -⟩
        wp_auto
        wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
        wp_for_post
        iframe
        iexists (kk + 1), f, (array.mk 5 (cu'.arr.set (sint.Z (W64 (sint.Z q))).toNat (kk + 1)))
        iframe; ipureintro
        refine ⟨?_, hadv'⟩
        have : sint.Z (W64 (sint.Z q)) = sint.Z q := by word
        rw [this, hqn]
        have h1 := hcu'
        simp only [depsOf] at h1 ⊢
        rw [h1]
        simp only [model.Deps.setAt, List.set_set]
      · have hkf : kf = kk := by
          unfold model.advanceCut at hadv
          simp only [hbox, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hadv
          have hc' : s.inst q (kk + 1#32) = some c := hc
          simp only [hc] at hadv
          have hne : ¬ (c.status = model.St.COMMITTED ∨ c.status = model.St.EXECUTED) := by
            rintro (h | h)
            · exact Hif h
            · exact h5 h
          simp only [hne, ite_false] at hadv; exact (Option.some.inj hadv).symm
        rw [decide_eq_false h5, hft]; simp only [Bool.false_eq_true, ↓reduceIte]
        ihave Hc := (copyRep_open ρ xs _ p c).2 $$ [Hiv Hcmds Hlb]
        · iexists iv; iframe; ipureintro; exact Hivf
        ihave Hinsts := Hiclose $$ %s %c [] Hc
        · ipureintro; exact ⟨hc, fun _ _ _ => rfl⟩
        ihave Hrow := (Perennial.gryff.replica.rowOwn_open M _ sq).2 $$ [Hrow]
        · iexists ptrs; iframe; ipureintro; exact Hrowf
        ihave Hrows := Hrowsc $$ %M %(fun _ _ _ => rfl) Hrow
        try simp only [_root_.decide_true, ↓reduceIte]
        wp_auto
        iapply HΦ
        iapply (epaxosOwn_open ..).2
        iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu', pm
        have hco : committedOrExecuted { s with committedUpTo := s.committedUpTo.setAt q.toNat kf } =
            committedOrExecuted s := rfl
        have hcrt : ∀ q', ({ s with committedUpTo := s.committedUpTo.setAt q.toNat kf } : RState).crt q' =
            s.crt q' := fun _ => rfl
        have hcf : ∀ q', ({ s with committedUpTo := s.committedUpTo.setAt q.toNat kf } : RState).confAt q' =
            s.confAt q' := fun _ => rfl
        simp only [instsRep, hco, hcrt, hcf]
        iframe # ∗
        ipureintro
        rw [hkf]
        exact ⟨Hf.1, Hf.2.1, Hf.2.2.1, hcu', Hf.2.2.2.2⟩
