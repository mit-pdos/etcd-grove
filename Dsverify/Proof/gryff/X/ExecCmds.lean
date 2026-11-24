/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/X/ExecCmds.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit X: `executeCommands` (the executor goroutine; generic `GF`)
-/
module

public import Dsverify.Proof.gryff.X.Cmds
public import Dsverify.Proof.gryff.X.Slot

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.X

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open Perennial.gryff.model (RState Copy Msg Ev Out committedCopy executedB inBox depR)
open Perennial.gryff.replica (XS Node TInv Post TState XClosed stackOwn euOwn stackOwn_open
  euOwn_open stackElems stackOwn_intro rowOwn rowOwn_open rows_acc wp_dlog_Printf)
open Perennial.gryff.replica2 (Repl2Names rid32 scFacts2)
open Perennial.gryff.pure (stOf)
open github_com.goose_lang.primitive (ProphId)

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS]
variable [sem : go.Semantics] [gryff_sem : src.gryff.Assumptions]
variable [time_sem : time.Assumptions]
variable {k : Fin 3} {ρ : Repl2Names} {r h : Loc} {p : ProphId}

set_option goose.wp.extras true

/-- The executor's state between two scans: its search state (the visited instances executed;
the executed set closed under the dependencies at some earlier trace, or empty). -/
def ExecutorInv (L : ExecLaws (GF := GF) k ρ r h p) (xs : XS) : IProp GF :=
  iprop(execPrivG ρ h xs [] ∗ ⌜∀ u, xs.numF u ≠ 0 → u ∈ xs.1⌝ ∗
    (⌜xs.1 = []⌝ ∨ ∃ t0, L.TLb t0 ∗
      ⌜XClosed (depR (stOf k t0)) xs.1 ∧ ∀ u ∈ xs.1, (committedCopy (stOf k t0) u).isSome⌝))

theorem ExecutorInv_open (L : ExecLaws (GF := GF) k ρ r h p) (xs : XS) :
    ExecutorInv L xs ⊣⊢ execPrivG ρ h xs [] ∗ ⌜∀ u, xs.numF u ≠ 0 → u ∈ xs.1⌝ ∗
      (⌜xs.1 = []⌝ ∨ ∃ t0, L.TLb t0 ∗
        ⌜XClosed (depR (stOf k t0)) xs.1 ∧ ∀ u ∈ xs.1, (committedCopy (stOf k t0) u).isSome⌝) :=
  .rfl

set_option hygiene false in
/-- Load `e.InstanceSpace[q][inst]` (the slot opened by `LA_slot`, its facts in context). -/
macro "load_slot" : tactic => `(tactic| (
  try wp_auto;
  rw [ite_eq_left hql];
  wp_apply wp_load_slice_index
    (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
    ispS (sint.Z qv) isp _ sq hq0 $$ [Hisp] as -;
  (isplitr; iexact Hisp; ipureintro; exact hsq);
  rw [ite_eq_left hil];
  wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
    sq _ ptrs _ pw hil.1 $$ [Hrow] as Hrow;
  (isplitl [Hrow]; iexact Hrow; ipureintro; exact hpw)))

set_option hygiene false in
/-- Open the slot `InstanceSpace[q][inst]` of the lock's contents `HLA` (facts `hsq`, `hql`, `hil`,
`hpw` for `load_slot`). -/
macro "open_slot" : tactic => `(tactic| (
  icases ExecLaws.LA_slot L t xs (W32 (sint.Z qv)) iv hb $$ HLA with ⟨%ispS, %sq, %isp, %ptrs,
    %pw, #HIS, #Hisp, %Hsl, Hrow, Hv, HLAc⟩;
  ihave %HispSlen := ownSlice_len _ _ _ $$ Hisp;
  ihave %Hrowlen := ownSlice_len _ _ _ $$ Hrow;
  have hsq : isp[(sint.Z qv).toNat]? = some sq := by rw [← hq32]; exact Hsl.1;
  have hql : 0 ≤ sint.Z qv ∧ sint.Z qv < sint.Z ispS.len := by
    have := HispSlen.1; rw [Hsl.2.2.1] at this; simp only [sint.nat, sint.Z] at *; omega;
  have hil : 0 ≤ sint.Z (W64 (sint.Z iv)) ∧ sint.Z (W64 (sint.Z iv)) < sint.Z sq.len := by
    rw [hiw]; have := Hrowlen.1; rw [Hsl.2.2.2] at this; unfold replica.nSlots at this;
    unfold model.SLOTS at hcrt; simp only [sint.nat, sint.Z] at *; omega;
  have hpw : ptrs[(sint.Z (W64 (sint.Z iv))).toNat]? = some pw := by rw [hiw]; exact Hsl.2.1))

set_option hygiene false in
/-- Open the slot `InstanceSpace[q][inst]` of `HLA` again (primed names: `Hrow'`, `Hv'`, `HLAc'`,
the pointer `pw'`), its slices those of the first opening, and load `InstanceSpace[q][inst]`. -/
macro "reload_slot" : tactic => `(tactic| (
  icases ExecLaws.LA_slot L t xs (W32 (sint.Z qv)) iv hb $$ HLA with ⟨%ispS', %sq', %isp',
    %ptrs', %pw', #HIS', #Hisp', %Hsl', Hrow', Hv', HLAc'⟩;
  icombine HIS HIS' gives %HISe;
  subst HISe;
  ihave %Hispe := ownSlice_agree _ _ _ _ _ $$ Hisp Hisp';
  subst Hispe;
  have hsq' : sq = sq' := by
    have h1 := Hsl'.1; rw [hq32, hsq] at h1; exact Option.some.inj h1;
  subst hsq';
  have hpw' : ptrs'[(sint.Z (W64 (sint.Z iv))).toNat]? = some pw' := by rw [hiw]; exact Hsl'.2.1;
  try wp_auto;
  rw [ite_eq_left hql];
  wp_apply wp_load_slice_index
    (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
    ispS (sint.Z qv) isp _ sq hq0 $$ [Hisp] as -;
  (isplitr; iexact Hisp; ipureintro; exact hsq);
  rw [ite_eq_left hil];
  wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
    sq _ ptrs' _ pw' hil.1 $$ [Hrow'] as Hrow';
  (isplitl [Hrow']; iexact Hrow'; ipureintro; exact hpw')))

set_option maxHeartbeats 8000000 in
/-- `executeCommands()` (generic `GF`, internal: from a fresh search state). -/
theorem wp_executeCommands (L : ExecLaws (GF := GF) k ρ r h p) (gR mtx ex : Loc) (xs : XS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ L.isExecG gR mtx ex ∗
        r.[src.gryff.Replica, go!"Shutdown"] ↦□ false ∗
        execPrivG ρ h xs [] ∗ ⌜xs.1 = [] ∧ ∀ u, xs.numF u = 0⌝ }}
      (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"executeCommands")) (Val #()))
    {{ RET #(); True }} := by
  iintro %Φ Hpre HΦ
  icases Hpre with ⟨#Hpkg, #Hfix, #HrSd, Hpriv, %Hpre⟩
  wp_method_call
  wp_call
  icases (L.isExecG_open ..).1 $$ Hfix with ⟨#Hr, #Hh, #Hm, #Hpp, #HR, #Hex, #Hexr, #HId, #HN,
    #HSd, #Hlock, #Heo, #Hrec, #HInv, #Hdlog⟩
  wp_auto
  wp_apply wp_slice_make2 (V := w32) (t := go.int32) (W64 3) as %pis ⟨Hpis, -⟩
  · ipureintro; decide
  wp_apply wp_slice_make2 (V := w64) (t := go.uint64) (W64 3) as %tos ⟨Htos, -⟩
  · ipureintro; decide
  -- the slices' initialization
  ihave HI : (∃ (q : w64) (l1 : List w32) (l2 : List w64), "q" ∷ q_ptr ↦ q ∗
      "Hpis" ∷ pis ↦* l1 ∗ "Htos" ∷ tos ↦* l2 ∗
      "%HI" ∷ ⌜0 ≤ sint.Z q ∧ sint.Z q ≤ 3 ∧ l1.length = 3 ∧ l2.length = 3⌝ : IProp GF)
    $$ [q Hpis Htos]
  · iexists (W64 0), _, _; iframe; ipureintro; simp
  wp_for HI
  wp_if_destruct
  · ihave %Hl1 := ownSlice_len _ _ _ $$ Hpis
    ihave %Hl2 := ownSlice_len _ _ _ $$ Htos
    have hq3 : sint.Z q < 3 := by have := Hif; word
    rw [ite_eq_left (show 0 ≤ sint.Z q ∧ sint.Z q < sint.Z pis.len by
      have := Hl1.1; rw [HI.2.2.1] at this; simp only [sint.nat, sint.Z] at *; omega)]
    wp_apply wp_store_slice_index (t := go.int32) pis (sint.Z q) l1 _ $$ [$Hpis] as Hpis
    · ipureintro; rw [HI.2.2.1]; omega
    rw [ite_eq_left (show 0 ≤ sint.Z q ∧ sint.Z q < sint.Z tos.len by
      have := Hl2.1; rw [HI.2.2.2] at this; simp only [sint.nat, sint.Z] at *; omega)]
    wp_apply wp_store_slice_index (t := go.uint64) tos (sint.Z q) l2 _ $$ [$Htos] as Htos
    · ipureintro; rw [HI.2.2.2]; omega
    wp_for_post
    iframe
    iexists (q + W64 1), _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by simp [HI.2.2.1], by simp [HI.2.2.2]⟩
  · -- the main loop
    have hq3 : 3 ≤ sint.Z q := by have := Hif; word
    ihave %Hl1 := ownSlice_len _ _ _ $$ Hpis
    ihave %Hl2 := ownSlice_len _ _ _ $$ Htos
    ihave HM : (∃ (xs : XS) (l1 : List w32) (l2 : List w64), "Hpis" ∷ pis ↦* l1 ∗
        "Htos" ∷ tos ↦* l2 ∗ "%HM" ∷ ⌜l1.length = 3 ∧ l2.length = 3⌝ ∗
        "Hex" ∷ ExecutorInv L xs : IProp GF) $$ [Hpis Htos Hpriv]
    · iexists xs, l1, l2
      iframe
      isplitr
      · ipureintro; exact ⟨HI.2.2.1, HI.2.2.2⟩
      iapply (ExecutorInv_open ..).2
      isplitl [Hpriv]
      · iexact Hpriv
      isplitr
      · ipureintro; intro u hu; exact absurd (Hpre.2 u) hu
      ileft; ipureintro; exact Hpre.1
    wp_for HM
    icases (ExecutorInv_open ..).1 $$ Hex with ⟨Hpriv, %Hvis, Hcl⟩
    icases (execPrivG_open ..).1 $$ Hpriv with ⟨Hxs, Hstk, %euS, #HeuS, Heu⟩
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hown, HLI⟩
    icases L.li_open $$ [HInv HLI] with
      (⟨%t, %xs', HTH, HPr, HRs, HEP, Hxs1, HPO, HBt⟩ | ⟨%xs', HEP, Hxs1, HB⟩)
    · iframe; iframe #
    · -- after the boot
      icombine Hxs Hxs1 gives %Hxseq
      obtain ⟨-, hx⟩ := Hxseq
      subst hx
      imod L.closed_relock t xs $$ [HTH Hcl] with ⟨HTH, %HXc⟩
      · iframe; iframe #
      ihave HLA : L.LA t xs $$ [HTH HPr HRs HEP Hxs1 HPO HBt]
      · iapply (L.LA_open ..).2; iframe
      ihave Hpriv : execPrivG ρ h xs [] $$ [Hxs Hstk Heu]
      · iapply (execPrivG_open ..).2; iframe; iframe #
      ihave HQ : (∃ (qv : w64) (t : List Ev) (xs : XS) (b : Bool) (l1 : List w32)
          (l2 : List w64),
          "q" ∷ q_ptr ↦ qv ∗ "executed" ∷ executed_ptr ↦ b ∗ "Hpis" ∷ pis ↦* l1 ∗
          "Htos" ∷ tos ↦* l2 ∗ "Hown" ∷ sync.ownMutex mtx ∗ "HLA" ∷ L.LA t xs ∗
          "Hpriv" ∷ execPrivG ρ h xs [] ∗
          "%HQ" ∷ ⌜0 ≤ sint.Z qv ∧ sint.Z qv ≤ 3 ∧ l1.length = 3 ∧ l2.length = 3 ∧
            ExecInv (stOf k t) xs⌝ : IProp GF) $$ [q executed Hpis Htos Hown HLA Hpriv]
      · iexists (W64 0), t, xs, false, l1, l2
        iframe
        ipureintro
        exact ⟨by decide, by decide, HM.1, HM.2, Hvis, HXc⟩
      wp_for HQ
      wp_if_destruct
      · -- replica `q`'s instances
        obtain ⟨hq0, -, hl1, hl2, hinv⟩ := HQ
        have hq3' : sint.Z qv < 3 := by have := Hif; word
        ihave ⟨HLA, %Hok⟩ := L.LA_ok t xs $$ HLA
        icases (execPrivG_open ..).1 $$ Hpriv with ⟨Hxs, Hstk, %euS', #HeuS', Heu⟩
        icombine HeuS HeuS' gives %Heu'
        subst Heu'
        icases (euOwn_open ..).1 $$ Heu with ⟨%euv, Heuv, %Heuf⟩
        ihave %Heulen := ownSlice_len _ _ _ $$ Heuv
        obtain ⟨e0, he0⟩ : ∃ e0, euv[(sint.Z qv).toNat]? = some e0 :=
          ⟨_, List.getElem?_eq_getElem (by rw [Heuf.1]; omega)⟩
        rw [ite_eq_left (show 0 ≤ sint.Z qv ∧ sint.Z qv < sint.Z euS.len by
          have := Heulen.1; rw [Heuf.1] at this; simp only [sint.nat, sint.Z] at *; omega)]
        wp_apply wp_load_slice_index (t := go.int32) euS (sint.Z qv) euv _ e0 hq0 $$ [$Heuv]
          as Heuv
        · ipureintro; exact he0
        have he0f := Heuf.2 _ e0 he0
        have he0s : sint.Z e0 < model.SLOTS := by
          rcases Int.lt_or_le (sint.Z e0) 0 with hneg | hnn
          · unfold model.SLOTS; omega
          · have hX := he0f.2 (sint.Z e0) hnn (Int.le_refl _)
            have hb := committedCopy_box (executedB_isSome ((Hok.1 _).2 hX))
            have := hb.2.2.2; unfold model.SLOTS; simp only at this; omega
        ihave Hpriv : execPrivG ρ h xs [] $$ [Hxs Hstk Heuv]
        · iapply (execPrivG_open ..).2
          iframe
          iexists euS
          iframe #
          iapply (euOwn_open ..).2
          iexists euv
          iframe
          ipureintro; exact Heuf
        ihave HJ : (∃ (iv : w32) (t : List Ev) (xs : XS) (b : Bool) (l1 : List w32)
            (l2 : List w64),
            "inst" ∷ inst_ptr ↦ iv ∗ "q" ∷ q_ptr ↦ qv ∗ "executed" ∷ executed_ptr ↦ b ∗
            "Hpis" ∷ pis ↦* l1 ∗ "Htos" ∷ tos ↦* l2 ∗ "Hown" ∷ sync.ownMutex mtx ∗
            "HLA" ∷ L.LA t xs ∗ "Hpriv" ∷ execPrivG ρ h xs [] ∗
            "%HJ" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ model.SLOTS ∧ l1.length = 3 ∧ l2.length = 3 ∧
              ExecInv (stOf k t) xs⌝ : IProp GF) $$ [inst q executed Hpis Htos Hown HLA Hpriv]
        · iexists (e0 + W32 1), t, xs, b, l1, l2
          iframe
          ipureintro
          have he1 : sint.Z (e0 + W32 1) = sint.Z e0 + 1 := by
            unfold model.SLOTS at he0s; have := he0f.1; word
          rw [he1]
          exact ⟨by omega, by omega, hl1, hl2, hinv⟩
        wp_for HJ
        obtain ⟨hi0, hiS, hl1, hl2, hinv⟩ := HJ
        icases L.LA_crt t xs $$ HLA with ⟨%crtS, #Hcrt, Hcrtv, %Hcrtl, HLAc⟩
        ihave %Hcrtlen := ownSlice_len _ _ _ $$ Hcrtv
        obtain ⟨cv, hcv⟩ : ∃ cv, (stOf k t).crtInstance[(sint.Z qv).toNat]? = some cv :=
          ⟨_, List.getElem?_eq_getElem (by rw [Hcrtl]; omega)⟩
        wp_auto
        rw [ite_eq_left (show 0 ≤ sint.Z qv ∧ sint.Z qv < sint.Z crtS.len by
          have := Hcrtlen.1; rw [Hcrtl] at this; simp only [sint.nat, sint.Z] at *; omega)]
        wp_apply wp_load_slice_index (t := go.int32) crtS (sint.Z qv) _ _ cv hq0 $$ [$Hcrtv]
          as Hcrtv
        · ipureintro; exact hcv
        ihave HLA := HLAc $$ Hcrtv
        wp_if_destruct
        · -- an iteration: instance `inst` of replica `q`
          have hlt : sint.Z iv < sint.Z cv := of_decide_eq_true (go.intoVal_inj Hif)
          imod L.LA_deps t xs $$ [HInv HLA] with ⟨HLA, %Hd⟩
          · iframe; iframe #
          ihave ⟨HLA, %Hok'⟩ := L.LA_ok t xs $$ HLA
          have hq32 : sint.Z (W32 (sint.Z qv)) = sint.Z qv := by word
          have hcrt : sint.Z cv ≤ model.SLOTS := by
            have h1 := Hd.2 (W32 (sint.Z qv))
            have hq : (W32 (sint.Z qv) : w32).toNat = (sint.Z qv).toNat := by
              have := hq32; simp only [sint.Z] at this ⊢; word
            unfold model.RState.crt at h1
            rw [hq, List.getD_eq_getElem?_getD, hcv] at h1
            simpa using h1
          have hb : inBox (W32 (sint.Z qv)) iv = true := by
            unfold inBox; rw [hq32]; simp only [decide_eq_true_eq]; omega
          icases L.LA_slot t xs (W32 (sint.Z qv)) iv hb $$ HLA with ⟨%ispS, %sq, %isp, %ptrs, %pw,
            #HIS, #Hisp, %Hsl, Hrow, Hv, HLAc⟩
          ihave %HispSlen := ownSlice_len _ _ _ $$ Hisp
          ihave %Hrowlen := ownSlice_len _ _ _ $$ Hrow
          have hsq : isp[(sint.Z qv).toNat]? = some sq := by rw [← hq32]; exact Hsl.1
          have hql : 0 ≤ sint.Z qv ∧ sint.Z qv < sint.Z ispS.len := by
            have := HispSlen.1; rw [Hsl.2.2.1] at this; simp only [sint.nat, sint.Z] at *; omega
          wp_auto
          rw [ite_eq_left hql]
          wp_apply wp_load_slice_index
            (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
            ispS (sint.Z qv) isp _ sq hq0 $$ [$Hisp] as -
          · ipureintro; exact hsq
          have hiw : sint.Z (W64 (sint.Z iv)) = sint.Z iv := by
            unfold model.SLOTS at hiS; word
          have hil : 0 ≤ sint.Z (W64 (sint.Z iv)) ∧ sint.Z (W64 (sint.Z iv)) < sint.Z sq.len := by
            rw [hiw]; have := Hrowlen.1; rw [Hsl.2.2.2] at this; unfold replica.nSlots at this
            unfold model.SLOTS at hcrt; simp only [sint.nat, sint.Z] at *; omega
          have hpw : ptrs[(sint.Z (W64 (sint.Z iv))).toNat]? = some pw := by rw [hiw]; exact Hsl.2.1
          wp_join (Q := fun bv => iprop(∃ b1 : Bool, ⌜bv = #b1⌝ ∗ sq ↦* ptrs ∗
              slotView ρ xs (stOf k t) (W32 (sint.Z qv)) iv pw ∗ inst_ptr ↦ iv ∗ q_ptr ↦ qv ∗
              e_ptr ↦ h ∗ ⌜b1 = true ↔ ∃ c, (stOf k t).inst (W32 (sint.Z qv)) iv = some c ∧
                c.status = model.St.EXECUTED⌝)) at (if: (GoUnOp GoNot go.bool) _ then _ else _)
              with [Hrow Hv inst q e]
          · rw [ite_eq_left hil]
            wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
              sq _ ptrs _ pw (by omega) $$ [$Hrow] as Hrow
            · ipureintro; exact hpw
            wp_if_destruct
            · -- nil
              icases slotView_null ρ xs (stOf k t) (W32 (sint.Z qv)) iv $$ Hv with ⟨Hv, %Hnone⟩
              iexists false
              iframe
              ipureintro
              refine ⟨rfl, ?_⟩
              simp [Hnone]
            · load_slot
              wp_apply wp_slot_Status ρ xs (stOf k t) (W32 (sint.Z qv)) iv pw Hif $$ [$Hv]
                as %st ⟨Hv, %Hst⟩
              iexists (decide (st = W8 5))
              iframe
              ipureintro
              refine ⟨rfl, ?_⟩
              obtain ⟨c, hc, rfl, -⟩ := Hst
              constructor
              · intro hd; exact ⟨c, hc, of_decide_eq_true hd⟩
              · rintro ⟨c', hc', hs⟩; rw [hc] at hc'; cases hc'; exact decide_eq_true hs
          iintro ⟨%b1, %Hb1, Hrow, Hv, inst, q, e, %Hb1i⟩
          subst Hb1
          cases b1
          · -- not executed
            wp_auto
            wp_join (Q := fun bv => iprop(∃ b2 : Bool, ⌜bv = #b2⌝ ∗ sq ↦* ptrs ∗
                slotView ρ xs (stOf k t) (W32 (sint.Z qv)) iv pw ∗ inst_ptr ↦ iv ∗ q_ptr ↦ qv ∗
                e_ptr ↦ h ∗ ⌜(b2 = false ↔ ∃ c, (stOf k t).inst (W32 (sint.Z qv)) iv = some c ∧
                  c.status = model.St.COMMITTED) ∧ (pw = Loc.null → b2 = true)⌝))
              at (if: _ then #true else _) with [Hrow Hv inst q e]
            · load_slot
              wp_if_destruct
              · -- nil
                icases slotView_null ρ xs (stOf k t) (W32 (sint.Z qv)) iv $$ Hv with ⟨Hv, %Hnone⟩
                iexists true
                iframe
                ipureintro
                refine ⟨rfl, ?_, fun _ => rfl⟩
                simp [Hnone]
              · load_slot
                wp_apply wp_slot_Status ρ xs (stOf k t) (W32 (sint.Z qv)) iv pw Hif $$ [$Hv]
                  as %st ⟨Hv, %Hst⟩
                iexists (!decide (st = W8 4))
                iframe
                ipureintro
                refine ⟨rfl, ?_, fun h => absurd h Hif⟩
                obtain ⟨c, hc, rfl, -⟩ := Hst
                constructor
                · intro hd
                  have h' : c.status = W8 4 := by simpa using hd
                  exact ⟨c, hc, by rw [h']; rfl⟩
                · rintro ⟨c', hc', hs⟩; rw [hc] at hc'; cases hc'; rw [hs]; rfl
            iintro ⟨%b2, %Hb2, Hrow, Hv, inst, q, e, %Hb2i⟩
            subst Hb2
            cases b2
            · -- committed: the execution
              obtain ⟨c, hc, hcs⟩ := Hb2i.1.1 rfl
              have hnn : pw ≠ Loc.null := fun h => by have := Hb2i.2 h; cases this
              icases (slotView_some_open hc).1 $$ Hv with ⟨-, Hc⟩
              icases (copyRepG_open ..).1 $$ Hc with ⟨%iw, Hwp, Hwcm, Hwlb, %Hiw⟩
              load_slot
              wp_join iprop(pw ↦ iw ∗ lbRepG ρ iw.lb' c.lb ∗ sq ↦* ptrs ∗ inst_ptr ↦ iv ∗
                  q_ptr ↦ qv ∗ e_ptr ↦ h) at next with [Hwp Hwlb Hrow inst q e]
                as ⟨Hwp, Hwlb, Hrow, inst, q, e⟩
              · icases lbRepG_open_time ρ iw.lb' c.lb $$ Hwlb with
                  (⟨%Hnil, Hwlb⟩ | ⟨%g, Hg, Hgclose⟩)
                · simp only [Hnil, _root_.decide_true, Bool.not_true]
                  wp_auto
                  wp_join_done
                · ihave %hgn := typedPointsto_not_null _ _ _ $$ Hg
                  simp only [hgn, _root_.decide_false, Bool.not_false]
                  load_slot
                  wp_apply time.wp_Now as %tn _
                  wp_apply time.Time.wp_Sub as %d _
                  wp_apply wp_slice_literal (V := GoInterface) _
                  isplitr
                  · ipureintro; rfl
                  iintro %_ ⟨-, -⟩
                  wp_auto
                  wp_apply wp_dlog_Printf $$ [$Hdlog]
                  wp_join_done
                  iframe
                  simp only [lbTimes]
                  iapply Hgclose $$ %g.executedTime' %g.blockStartTime' Hg
              ihave Hc : copyRepG ρ xs (sint.Z (W32 (sint.Z qv)), sint.Z iv) pw c $$ [Hwp Hwcm Hwlb]
              · iapply (copyRepG_open ..).2; iexists iw; iframe; ipureintro; exact Hiw
              ihave Hv : slotView ρ xs (stOf k t) (W32 (sint.Z qv)) iv pw $$ [Hc]
              · iapply (slotView_some_open hc).2; iframe; ipureintro; exact hnn
              ihave HLA := HLAc $$ Hrow Hv
              wp_apply wp_executeCommand L gR mtx ex t xs (W32 (sint.Z qv)) iv $$ [Hown HLA Hpriv]
              · iframe; iframe #; ipureintro; exact ⟨hinv, hb⟩
              iintro %ok ⟨%t', %xs', Hown, HLA, Hpriv, %Hx⟩
              obtain ⟨-, -, hinv', hokx⟩ := Hx
              wp_auto
              wp_if_destruct
              · -- not executed
                wp_for_post
                iframe
                iexists (iv + W32 1), t', xs', b, l1, l2
                iframe
                ipureintro
                have hn := sint32_succ _
                  (by unfold model.SLOTS at hcrt; omega : sint.Z iv < 2 ^ 31 - 1)
                refine ⟨by omega, by rw [hn]; unfold model.SLOTS at hcrt ⊢; omega, hl1, hl2, hinv'⟩
              · -- executed: `ExecedUpTo[q]` advances over it
                have hX : (sint.Z qv, sint.Z iv) ∈ xs'.1 := by
                  have := hokx rfl; rwa [hq32] at this
                icases (execPrivG_open ..).1 $$ Hpriv with ⟨Hxs, Hstk, %euS', #HeuS', Heu⟩
                icombine HeuS HeuS' gives %Heu2
                subst Heu2
                icases (euOwn_open ..).1 $$ Heu with ⟨%euv, Heuv, %Heuf⟩
                ihave %Heulen := ownSlice_len _ _ _ $$ Heuv
                obtain ⟨e1, he1⟩ : ∃ e1, euv[(sint.Z qv).toNat]? = some e1 :=
                  ⟨_, List.getElem?_eq_getElem (by rw [Heuf.1]; omega)⟩
                have hqe : 0 ≤ sint.Z qv ∧ sint.Z qv < sint.Z euS.len := by
                  have := Heulen.1; rw [Heuf.1] at this; simp only [sint.nat, sint.Z] at *; omega
                rw [ite_eq_left hqe]
                wp_apply wp_load_slice_index (t := go.int32) euS (sint.Z qv) euv _ e1 hq0
                  $$ [$Heuv] as Heuv
                · ipureintro; exact he1
                wp_if_destruct
                · -- `ExecedUpTo[q] = inst`
                  rw [ite_eq_left hqe]
                  wp_apply wp_store_slice_index (t := go.int32) euS (sint.Z qv) euv _ $$ [$Heuv]
                    as Heuv
                  · ipureintro; rw [Heuf.1]; omega
                  have hs1 : sint.Z (e1 + W32 1) = sint.Z e1 + 1 := by
                    unfold model.SLOTS at hiS; have := (Heuf.2 _ e1 he1).1; word
                  ihave Hpriv : execPrivG ρ h xs' [] $$ [Hxs Hstk Heuv]
                  · iapply (execPrivG_open ..).2
                    iframe
                    iexists euS
                    iframe #
                    iapply (euOwn_open ..).2
                    iexists _
                    iframe
                    ipureintro
                    refine ⟨by simp [Heuf.1], euv_set_facts euv _ e1 _ he1 Heuf.2 hs1 ?_⟩
                    have hm : (((sint.Z qv).toNat : Nat) : Int) = sint.Z qv := by omega
                    rw [hm]; exact hX
                  wp_for_post
                  iframe
                  iexists (e1 + W32 1 + W32 1), t', xs', true, l1, l2
                  iframe
                  ipureintro
                  have hn := sint32_succ _
                    (by unfold model.SLOTS at hcrt; omega : sint.Z (e1 + W32 1) < 2 ^ 31 - 1)
                  refine ⟨by omega, by rw [hn]; unfold model.SLOTS at hcrt ⊢; omega, hl1, hl2, hinv'⟩
                · ihave Hpriv : execPrivG ρ h xs' [] $$ [Hxs Hstk Heuv]
                  · iapply (execPrivG_open ..).2
                    iframe
                    iexists euS
                    iframe #
                    iapply (euOwn_open ..).2
                    iexists _
                    iframe
                    ipureintro; exact Heuf
                  wp_for_post
                  iframe
                  iexists (iv + W32 1), t', xs', true, l1, l2
                  iframe
                  ipureintro
                  have hn := sint32_succ _
                    (by unfold model.SLOTS at hcrt; omega : sint.Z iv < 2 ^ 31 - 1)
                  refine ⟨by omega, by rw [hn]; unfold model.SLOTS at hcrt ⊢; omega, hl1, hl2, hinv'⟩
            · -- not committed (or no instance): a recovery's trigger, after a while
              ihave HLA := HLAc $$ Hrow Hv
              wp_auto
              ihave %Hpl := ownSlice_len _ _ _ $$ Hpis
              ihave %Htl := ownSlice_len _ _ _ $$ Htos
              have hqp : 0 ≤ sint.Z qv ∧ sint.Z qv < sint.Z pis.len := by
                have := Hpl.1; rw [hl1] at this; simp only [sint.nat, sint.Z] at *; omega
              have hqt : 0 ≤ sint.Z qv ∧ sint.Z qv < sint.Z tos.len := by
                have := Htl.1; rw [hl2] at this; simp only [sint.nat, sint.Z] at *; omega
              obtain ⟨pv1, hpv1⟩ : ∃ x, l1[(sint.Z qv).toNat]? = some x :=
                ⟨_, List.getElem?_eq_getElem (by rw [hl1]; omega)⟩
              obtain ⟨tv1, htv1⟩ : ∃ x, l2[(sint.Z qv).toNat]? = some x :=
                ⟨_, List.getElem?_eq_getElem (by rw [hl2]; omega)⟩
              wp_join iprop(∃ (l1' : List w32) (l2' : List w64), pis ↦* l1' ∗ tos ↦* l2' ∗
                  ⌜l1'.length = 3 ∧ l2'.length = 3⌝ ∗ L.LA t xs ∗ execPrivG ρ h xs [] ∗
                  inst_ptr ↦ iv ∗ q_ptr ↦ qv ∗ e_ptr ↦ h ∗ problemInstance_ptr ↦ pis ∗
                  timeout_ptr ↦ tos) at next
                with [Hpis Htos HLA Hpriv inst q e problemInstance timeout]
                as ⟨%l1', %l2', Hpis, Htos, %Hl', HLA, Hpriv, inst, q, e, problemInstance, timeout⟩
              · rw [ite_eq_left hqp]
                wp_apply wp_load_slice_index (t := go.int32) pis (sint.Z qv) l1 _ pv1 hq0 $$ [$Hpis]
                  as Hpis
                · ipureintro; exact hpv1
                wp_if_destruct
                · -- the same instance as the last time: the timeout grows
                  rw [ite_eq_left hqt]
                  wp_auto
                  rw [ite_eq_left hqt]
                  wp_apply wp_load_slice_index (t := go.uint64) tos (sint.Z qv) l2 _ tv1 hq0
                    $$ [$Htos] as Htos
                  · ipureintro; exact htv1
                  wp_apply wp_store_slice_index (t := go.uint64) tos (sint.Z qv) l2 _ $$ [$Htos]
                    as Htos
                  · ipureintro; rw [hl2]; omega
                  rw [ite_eq_left hqt]
                  wp_apply wp_load_slice_index (t := go.uint64) tos (sint.Z qv) _ _ _ hq0
                    $$ [$Htos] as Htos
                  · ipureintro
                    rw [List.getElem?_set_self (by rw [hl2]; omega)]
                  wp_if_destruct
                  · -- the grace period is over: a recovery's trigger
                    -- `crtInstance[q]`
                    icases L.LA_crt t xs $$ HLA with ⟨%crtS', #Hcrt', Hcrtv, %Hcrtl', HLAc⟩
                    icombine Hcrt Hcrt' gives %Hce
                    subst Hce
                    rw [ite_eq_left (show 0 ≤ sint.Z qv ∧ sint.Z qv < sint.Z crtS.len by
                      have := Hcrtlen.1; rw [Hcrtl] at this; simp only [sint.nat, sint.Z] at *; omega)]
                    wp_apply wp_load_slice_index (t := go.int32) crtS (sint.Z qv) _ _ cv hq0
                      $$ [$Hcrtv] as Hcrtv
                    · ipureintro; exact hcv
                    ihave HLA := HLAc $$ Hcrtv
                    -- `ExecedUpTo[q]`
                    icases (execPrivG_open ..).1 $$ Hpriv with ⟨Hxs, Hstk, %euS', #HeuS', Heu⟩
                    icombine HeuS HeuS' gives %Heu2
                    subst Heu2
                    icases (euOwn_open ..).1 $$ Heu with ⟨%euv, Heuv, %Heuf⟩
                    ihave %Heulen := ownSlice_len _ _ _ $$ Heuv
                    obtain ⟨e1, he1⟩ : ∃ e1, euv[(sint.Z qv).toNat]? = some e1 :=
                      ⟨_, List.getElem?_eq_getElem (by rw [Heuf.1]; omega)⟩
                    have hqe : 0 ≤ sint.Z qv ∧ sint.Z qv < sint.Z euS.len := by
                      have := Heulen.1; rw [Heuf.1] at this; simp only [sint.nat, sint.Z] at *; omega
                    try wp_auto
                    rw [ite_eq_left hqe]
                    wp_apply wp_load_slice_index (t := go.int32) euS (sint.Z qv) euv _ e1 hq0
                      $$ [$Heuv] as Heuv
                    · ipureintro; exact he1
                    ihave Hpriv : execPrivG ρ h xs [] $$ [Hxs Hstk Heuv]
                    · iapply (execPrivG_open ..).2
                      iframe
                      iexists euS
                      iframe #
                      iapply (euOwn_open ..).2
                      iexists _
                      iframe
                      ipureintro; exact Heuf
                    -- `problemInstance[q]`, `timeout[q]`
                    try wp_auto
                    rw [ite_eq_left hqp]
                    wp_apply wp_load_slice_index (t := go.int32) pis (sint.Z qv) l1 _ pv1 hq0
                      $$ [$Hpis] as Hpis
                    · ipureintro; exact hpv1
                    try wp_auto
                    rw [ite_eq_left hqt]
                    wp_apply wp_load_slice_index (t := go.uint64) tos (sint.Z qv) _ _ _ hq0
                      $$ [$Htos] as Htos
                    · ipureintro
                      rw [List.getElem?_set_self (by rw [hl2]; omega)]
                    -- `InstanceSpace[q][inst]`
                    reload_slot
                    ihave HLA := HLAc' $$ Hrow' Hv'
                    wp_apply wp_slice_literal (V := GoInterface) _
                    isplitr
                    · ipureintro; rfl
                    iintro %_ ⟨-, -⟩
                    wp_auto
                    wp_apply wp_dlog_Printf $$ [$Hdlog]
                    icases (bagAtG_open ..).1 $$ Hrec with ⟨%ch, #Hch, #Hbag⟩
                    ihave ⟨HLA, #Hlb⟩ := L.LA_crtLb t xs ⟨(sint.Z qv).toNat, by omega⟩ $$ HLA
                    wp_auto
                    have hcrtv : (sint.Z ((stOf k t).crt (rid32 ⟨(sint.Z qv).toNat, by omega⟩))).toNat =
                        (sint.Z cv).toNat := by
                      unfold model.RState.crt rid32
                      have h1 : (W32 ((sint.Z qv).toNat : Nat) : w32).toNat = (sint.Z qv).toNat := by
                        have := hq0; have := hq3'; word
                      rw [h1, List.getD_eq_getElem?_getD, hcv]; rfl
                    wp_apply wp_bag_send (ρ.chans "recover") ch _ (recoverChanPG ρ) $$ [$Hbag «$v»]
                    · iapply recover_elem ρ _ (W32 (sint.Z qv)) iv ⟨(sint.Z qv).toNat, by omega⟩
                        (sint.Z ((stOf k t).crt (rid32 ⟨(sint.Z qv).toNat, by omega⟩))).toNat
                        (by simp [hq32]) (by omega) hi0 (by rw [hcrtv]; omega)
                      iframe
                      iexact Hlb
                    rw [ite_eq_left hqt]
                    wp_apply wp_store_slice_index (t := go.uint64) tos (sint.Z qv) _ _ $$ [$Htos]
                      as Htos
                    · ipureintro; simp [hl2]; omega
                    wp_join_done
                    iexists _, _
                    iframe
                    ipureintro; simp [hl1, hl2]
                  · wp_join_done
                    iexists _, _
                    iframe
                    ipureintro; simp [hl1, hl2]
                · -- a new problem instance
                  rw [ite_eq_left hqp]
                  wp_apply wp_store_slice_index (t := go.int32) pis (sint.Z qv) l1 _ $$ [$Hpis]
                    as Hpis
                  · ipureintro; rw [hl1]; omega
                  rw [ite_eq_left hqt]
                  wp_apply wp_store_slice_index (t := go.uint64) tos (sint.Z qv) l2 _ $$ [$Htos]
                    as Htos
                  · ipureintro; rw [hl2]; omega
                  wp_join_done
                  iexists _, _
                  iframe
                  ipureintro; simp [hl1, hl2]
              -- `if InstanceSpace[q][inst] == nil { continue }; break`
              reload_slot
              ihave HLA := HLAc' $$ Hrow' Hv'
              wp_if_destruct
              · -- `continue`
                wp_for_post
                iframe
                iexists (iv + W32 1), t, xs, b, l1', l2'
                iframe
                ipureintro
                have hn := sint32_succ _
                  (by unfold model.SLOTS at hcrt; omega : sint.Z iv < 2 ^ 31 - 1)
                refine ⟨by omega, by rw [hn]; unfold model.SLOTS at hcrt ⊢; omega, Hl'.1, Hl'.2,
                  hinv⟩
              · -- `break`
                wp_for_post
                wp_for_post
                iframe
                iexists (qv + W64 1), t, xs, b, l1', l2'
                iframe
                ipureintro
                exact ⟨by word, by word, Hl'.1, Hl'.2, hinv⟩
          · -- executed already (through a dependent's search)
            obtain ⟨c, hc, hcs⟩ := Hb1i.1 rfl
            have hX : (sint.Z qv, sint.Z iv) ∈ xs.1 := by
              have := executedB_of hb hc hcs; rw [hq32] at this; exact (Hok'.1 _).1 this
            icases (execPrivG_open ..).1 $$ Hpriv with ⟨Hxs, Hstk, %euS', #HeuS', Heu⟩
            icases (euOwn_open ..).1 $$ Heu with ⟨%euv, Heuv, %Heuf⟩
            ihave %Heulen := ownSlice_len _ _ _ $$ Heuv
            obtain ⟨e1, he1⟩ : ∃ e1, euv[(sint.Z qv).toNat]? = some e1 :=
              ⟨_, List.getElem?_eq_getElem (by rw [Heuf.1]; omega)⟩
            have hqe : 0 ≤ sint.Z qv ∧ sint.Z qv < sint.Z euS'.len := by
              have := Heulen.1; rw [Heuf.1] at this; simp only [sint.nat, sint.Z] at *; omega
            wp_auto
            rw [ite_eq_left hqe]
            wp_apply wp_load_slice_index (t := go.int32) euS' (sint.Z qv) euv _ e1 hq0 $$ [$Heuv]
              as Heuv
            · ipureintro; exact he1
            wp_apply wp_slice_literal (V := GoInterface) _
            isplitr
            · ipureintro; rfl
            iintro %_ ⟨-, -⟩
            wp_auto
            wp_apply wp_dlog_Printf $$ [$Hdlog]
            rw [ite_eq_left hqe]
            wp_apply wp_load_slice_index (t := go.int32) euS' (sint.Z qv) euv _ e1 hq0 $$ [$Heuv]
              as Heuv
            · ipureintro; exact he1
            ihave HLA := HLAc $$ Hrow Hv
            wp_if_destruct
            · -- `ExecedUpTo[q] = inst`
              rw [ite_eq_left hqe]
              wp_apply wp_store_slice_index (t := go.int32) euS' (sint.Z qv) euv _ $$ [$Heuv]
                as Heuv
              · ipureintro; rw [Heuf.1]; omega
              have hs1 : sint.Z (e1 + W32 1) = sint.Z e1 + 1 := by
                unfold model.SLOTS at he0s hiS; have := he0f.1; have := (Heuf.2 _ e1 he1).1; word
              ihave Hpriv : execPrivG ρ h xs [] $$ [Hxs Hstk Heuv]
              · iapply (execPrivG_open ..).2
                iframe
                iexists euS'
                iframe #
                iapply (euOwn_open ..).2
                iexists _
                iframe
                ipureintro
                refine ⟨by simp [Heuf.1], euv_set_facts euv _ e1 _ he1 Heuf.2 hs1 ?_⟩
                have hm : (((sint.Z qv).toNat : Nat) : Int) = sint.Z qv := by omega
                rw [hm]; exact hX
              wp_for_post
              iframe
              iexists (e1 + W32 1 + W32 1), t, xs, b, l1, l2
              iframe
              ipureintro
              have hn := sint32_succ _ (by unfold model.SLOTS at hcrt; omega : sint.Z (e1 + W32 1) < 2 ^ 31 - 1)
              refine ⟨by omega, by rw [hn]; unfold model.SLOTS at hcrt ⊢; omega, hl1, hl2, hinv⟩
            · ihave Hpriv : execPrivG ρ h xs [] $$ [Hxs Hstk Heuv]
              · iapply (execPrivG_open ..).2
                iframe
                iexists euS'
                iframe #
                iapply (euOwn_open ..).2
                iexists _
                iframe
                ipureintro; exact Heuf
              wp_for_post
              iframe
              iexists (iv + W32 1), t, xs, b, l1, l2
              iframe
              ipureintro
              have hn := sint32_succ _ (by unfold model.SLOTS at hcrt; omega : sint.Z iv < 2 ^ 31 - 1)
              refine ⟨by omega, by rw [hn]; unfold model.SLOTS at hcrt ⊢; omega, hl1, hl2, hinv⟩
        · -- replica `q` done
          have hlt : ¬ sint.Z iv < sint.Z cv := fun h => Hif (by rw [decide_eq_true h])
          rw [if_neg (by simp [hlt])]
          wp_for_post
          iframe
          iexists (qv + W64 1), t, xs, b, l1, l2
          iframe
          ipureintro
          exact ⟨by word, by word, hl1, hl2, hinv⟩
      · -- the scan's end: `Unlock`, the sleep
        obtain ⟨-, -, hl1, hl2, hinv⟩ := HQ
        ihave ⟨HLA, %Hok⟩ := L.LA_ok t xs $$ HLA
        imod L.LA_lb t xs $$ HLA with ⟨HLA, #HTLb⟩
        ihave HLI := L.li_closeA t xs $$ [HLA]
        · iapply (L.LA_open ..).1 $$ HLA
        wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hown $HLI]
        ihave Hex : ExecutorInv L xs $$ [Hpriv]
        · iapply (ExecutorInv_open ..).2
          isplitl [Hpriv]
          · iexact Hpriv
          isplitr
          · ipureintro; exact hinv.1
          iright
          iexists t
          isplitr
          · iexact HTLb
          ipureintro
          exact ⟨hinv.2, fun u hu => executedB_isSome ((Hok.1 u).2 hu)⟩
        cases b
        · try wp_auto
          wp_apply time.wp_Sleep
          wp_for_post
          iframe
          iexists xs, l1, l2
          iframe
          ipureintro; exact ⟨hl1, hl2⟩
        · try wp_auto
          wp_for_post
          iframe
          iexists xs, l1, l2
          iframe
          ipureintro; exact ⟨hl1, hl2⟩
    · -- the boot state: `crtInstance` is all 0, nothing is scanned
      icombine Hxs Hxs1 gives %Hxseq
      obtain ⟨-, hx⟩ := Hxseq
      subst hx
      ihave ⟨HEP, %Hok⟩ := epaxosOwnG_ok ρ h r xs (model.RState.init k.val) $$ HEP
      have hX0 : ∀ n, n ∉ xs.1 := by
        intro n hn
        have h1 := (Hok.1 n).2 hn
        unfold executedB committedCopy at h1
        split at h1 <;> simp_all [model.RState.init]
      ihave HQB : (∃ (qv : w64) (b : Bool), "q" ∷ q_ptr ↦ qv ∗ "executed" ∷ executed_ptr ↦ b ∗
          "HEP" ∷ epaxosOwnG ρ h r xs (model.RState.init k.val) ∗ "Heu" ∷ euOwn euS xs.1 ∗
          "%HQB" ∷ ⌜0 ≤ sint.Z qv ∧ sint.Z qv ≤ 3⌝ : IProp GF) $$ [q executed HEP Heu]
      · iexists (W64 0), false
        iframe
        ipureintro; exact ⟨by decide, by decide⟩
      wp_for HQB
      wp_if_destruct
      · -- replica `q`: `inst := ExecedUpTo[q] + 1 = 0`, not below `crtInstance[q] = 0`
        have hq3' : sint.Z qv < 3 := by have := Hif; word
        icases (euOwn_open ..).1 $$ Heu with ⟨%euv, Heuv, %Heuf⟩
        ihave %Heulen := ownSlice_len _ _ _ $$ Heuv
        obtain ⟨e1, he1⟩ : ∃ e1, euv[(sint.Z qv).toNat]? = some e1 :=
          ⟨_, List.getElem?_eq_getElem (by rw [Heuf.1]; omega)⟩
        have he1m : sint.Z e1 = -1 := by
          have h1 := Heuf.2 _ e1 he1
          rcases Int.lt_or_le (sint.Z e1) 0 with hneg | hnn
          · omega
          · exact absurd (h1.2 0 (Int.le_refl _) hnn) (hX0 _)
        have hqe : 0 ≤ sint.Z qv ∧ sint.Z qv < sint.Z euS.len := by
          have := Heulen.1; rw [Heuf.1] at this; simp only [sint.nat, sint.Z] at *; omega
        try wp_auto
        rw [ite_eq_left hqe]
        wp_apply wp_load_slice_index (t := go.int32) euS (sint.Z qv) euv _ e1 HQB.1 $$ [$Heuv]
          as Heuv
        · ipureintro; exact he1
        ihave Heu : euOwn euS xs.1 $$ [Heuv]
        · iapply (euOwn_open ..).2; iexists euv; iframe; ipureintro; exact Heuf
        have he0 : sint.Z (e1 + W32 1) = 0 := by
          have := sint32_succ e1 (by omega); omega
        ihave HJB : (∃ iv : w32, "inst" ∷ inst_ptr ↦ iv ∗ "%HJB" ∷ ⌜sint.Z iv = 0⌝ : IProp GF)
          $$ [inst]
        · iexists _; iframe; ipureintro; exact he0
        wp_for HJB
        icases EP_crt xs (model.RState.init k.val) $$ HEP with ⟨%crtS, #Hcrt, Hcrtv, %Hcrtl, HEPc⟩
        rw [show (model.RState.init k.val).crtInstance = [W32 0, W32 0, W32 0] from rfl] at Hcrtl ⊢
        ihave %Hcrtlen := ownSlice_len _ _ _ $$ Hcrtv
        try wp_auto
        rw [ite_eq_left (show 0 ≤ sint.Z qv ∧ sint.Z qv < sint.Z crtS.len by
          have := Hcrtlen.1; rw [Hcrtl] at this; simp only [sint.nat, sint.Z] at *; omega)]
        wp_apply wp_load_slice_index (t := go.int32) crtS (sint.Z qv)
          [W32 0, W32 0, W32 0] _ (W32 0) HQB.1 $$ [$Hcrtv] as Hcrtv
        · ipureintro
          have hn : (sint.Z qv).toNat = 0 ∨ (sint.Z qv).toNat = 1 ∨ (sint.Z qv).toNat = 2 := by
            omega
          rcases hn with hn | hn | hn <;> rw [hn] <;> rfl
        ihave HEP := HEPc $$ Hcrtv
        wp_if_destruct
        · exfalso
          have hlt : sint.Z iv < sint.Z (W32 0) := of_decide_eq_true (go.intoVal_inj Hif)
          have : sint.Z (W32 0) = 0 := by decide
          omega
        · rw [if_neg (by
            have hlt : ¬ sint.Z iv < sint.Z (W32 0) := fun h => Hif (by rw [decide_eq_true h])
            exact fun h => hlt (of_decide_eq_true h))]
          wp_for_post
          iframe
          iexists (qv + W64 1), b
          iframe
          ipureintro
          exact ⟨by word, by word⟩
      · -- the boot scan's end: `Unlock`, the sleep
        ihave HLI := L.li_closeB xs $$ [HEP Hxs1 HB]
        · iframe; iframe #
        wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hown $HLI]
        ihave Hex : ExecutorInv L xs $$ [Hxs Hstk Heu Hcl]
        · iapply (ExecutorInv_open ..).2
          isplitl [Hxs Hstk Heu]
          · iapply (execPrivG_open ..).2
            iframe
            iframe #
          iframe
          ipureintro; exact Hvis
        cases b
        · try wp_auto
          wp_apply time.wp_Sleep
          wp_for_post
          iframe
          iexists xs, l1, l2
          iframe
          ipureintro; exact HM
        · try wp_auto
          wp_for_post
          iframe
          iexists xs, l1, l2
          iframe
          ipureintro; exact HM

end

end Perennial.gryff.X
