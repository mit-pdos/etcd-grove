/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2a/Conf.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2a: `updateConflicts` (the conflict tables)
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

/-- The three operation types' entries (`PUT`, `GET`, `CAS`). -/
def opsAll : List w8 := [W8 1, W8 2, W8 6]

/-- A conflict entry with all three operation types (hub request H2a-R1's body of `confRep`). -/
def confRepS (mR : Loc) (o : Option w32) : IProp GF :=
  iprop(∃ m : GMap w64 Loc, mR ↦$ m ∗ ⌜∀ kk, kk ≠ W64 0 → m.lookup kk = none⌝ ∗
    match o with
    | none => iprop(⌜m.lookup (W64 0) = none⌝)
    | some v => iprop(∃ (ir : Loc) (im : GMap w8 w32), ⌜m.lookup (W64 0) = some ir⌝ ∗ ir ↦$ im ∗
        ⌜∀ op, im.lookup op = if op ∈ opsAll then some v else none⌝))

theorem confRepS_open (mR : Loc) (o : Option w32) : confRepS (GF := GF) mR o ⊣⊢
    ∃ m : GMap w64 Loc, mR ↦$ m ∗ ⌜∀ kk, kk ≠ W64 0 → m.lookup kk = none⌝ ∗
      match o with
      | none => iprop(⌜m.lookup (W64 0) = none⌝)
      | some v => iprop(∃ (ir : Loc) (im : GMap w8 w32), ⌜m.lookup (W64 0) = some ir⌝ ∗ ir ↦$ im ∗
          ⌜∀ op, im.lookup op = if op ∈ opsAll then some v else none⌝) := .rfl

/-- **H2a-R1**: `confRep` is `confRepS` (the request strengthens `confRep`'s body to it). -/
theorem confRep_S (mR : Loc) (o : Option w32) : confRep (GF := GF) mR o ⊣⊢ confRepS mR o := by
  unfold confRep confRepS; exact .rfl -- H2a-R1

/-- Go's update of one entry (`!ok || old < x` → `x`). -/
def updE (o : Option w32) (x : w32) : w32 :=
  match o with
  | some hi => if model.slt hi x then x else hi
  | none => x

theorem updE_idem (o : Option w32) (x : w32) : updE (some (updE o x)) x = updE o x := by
  cases o with
  | none => simp [updE, model.slt]
  | some hi =>
    simp only [updE, model.slt]
    by_cases h : sint.Z hi < sint.Z x <;> simp [h]

/-- An inner map (`map[Operation]int32`) after `j` of the three operation types are updated. -/
def imAt (o : Option w32) (x : w32) (j : Nat) (op : w8) : Option w32 :=
  if op ∈ opsAll.take j then some (updE o x) else if op ∈ opsAll then o else none

theorem imAt_zero (o : Option w32) (x : w32) (op : w8) :
    imAt o x 0 op = if op ∈ opsAll then o else none := by
  simp [imAt]

theorem imAt_at (o : Option w32) (x : w32) (j : Nat) (op : w8) (hj : opsAll[j]? = some op) :
    imAt o x j op = o := by
  rcases j with _ | _ | _ | j <;> simp [opsAll] at hj <;> subst hj <;>
    simp (config := {decide := true}) [imAt, opsAll]

theorem imAt_succ (o : Option w32) (x : w32) (j : Nat) (op : w8) (hj : opsAll[j]? = some op)
    (op' : w8) :
    imAt o x (j + 1) op' = if op = op' then some (updE o x) else imAt o x j op' := by
  rcases j with _ | _ | _ | j <;> simp [opsAll] at hj <;> subst hj <;>
    by_cases h1 : op' = 1#8 <;> by_cases h2 : op' = 2#8 <;> by_cases h6 : op' = 6#8 <;>
    simp (config := {decide := true}) [imAt, opsAll, h1, h2, h6, eq_comm]

theorem imAt_succ_ins (o : Option w32) (x : w32) (j : Nat) (opj : w8) (hj : opsAll[j]? = some opj)
    (im : GMap w8 w32) (him : ∀ op, im.lookup op = imAt o x j op) (h : updE o x = x) :
    ∀ op, (GMap.insert opj x im).lookup op = imAt o x (j + 1) op := by
  intro op
  rw [imAt_succ _ _ _ _ hj, GMap.lookup_insert_eq_iff, ← him, h]

theorem imAt_succ_keep (o : Option w32) (x : w32) (j : Nat) (opj : w8) (hj : opsAll[j]? = some opj)
    (im : GMap w8 w32) (him : ∀ op, im.lookup op = imAt o x j op) (h : some (updE o x) = o) :
    ∀ op, im.lookup op = imAt o x (j + 1) op := by
  intro op
  rw [imAt_succ _ _ _ _ hj, h, him]
  by_cases hop : opj = op
  · subst hop; simp [imAt_at _ _ _ _ hj]
  · simp [hop]

theorem imAt_three (o : Option w32) (x : w32) (op : w8) :
    imAt o x 3 op = if op ∈ opsAll then some (updE o x) else none := by
  have : opsAll.take 3 = opsAll := rfl
  simp only [imAt, this]; split <;> rfl

theorem cur_upd (c : Prop) [Decidable c] (o : Option w32) (x : w32) :
    updE (if c then o else some (updE o x)) x = updE o x := by
  split
  · rfl
  · exact updE_idem o x

/-- The entry after an iteration: key 0 mapped to the updated inner map. -/
theorem confRepS_close (mR ir : Loc) (m : GMap w64 Loc) (im : GMap w8 w32) (o : Option w32)
    (x : w32) (hm : ∀ kk, kk ≠ W64 0 → m.lookup kk = none)
    (him : ∀ op, im.lookup op = imAt o x 3 op) :
    (mR ↦$ (GMap.insert (W64 0) ir m) ∗ ir ↦$ im : IProp GF) ⊢ confRepS mR (some (updE o x)) := by
  iintro ⟨Hm, Hi⟩
  iapply (confRepS_open ..).2
  iexists (GMap.insert (W64 0) ir m)
  iframe Hm
  isplitr
  · ipureintro; intro kk hkk
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hkk)]; exact hm kk hkk
  · iexists ir, im
    iframe Hi
    ipureintro
    exact ⟨GMap.lookup_insert _ _ _, fun op => by rw [him, imAt_three]⟩

/-- Go's condition `!ok || old < x`. -/
def updC (o : Option w32) (x : w32) : Bool :=
  match o with
  | some hi => model.slt hi x
  | none => true

theorem updE_true (o : Option w32) (x : w32) (h : updC o x = true) : updE o x = x := by
  cases o <;> simp_all [updC, updE]

theorem updE_false (o : Option w32) (x : w32) (h : updC o x = false) : some (updE o x) = o := by
  cases o <;> simp_all [updC, updE]

/-- One command's iteration of `updateConflicts` in the model. -/
def ucStep (replica islot seq : w32) (s : RState) : RState :=
  { s with conf := s.conf.set replica.toNat (some (updE (s.confAt replica.toNat) islot)),
           maxSeqK0 := some (updE s.maxSeqK0 seq) }

theorem ucStep_idem (replica islot seq : w32) (t : RState) :
    ucStep replica islot seq (ucStep replica islot seq t) = ucStep replica islot seq t := by
  simp only [ucStep, model.RState.confAt]
  by_cases hi : replica.toNat < t.conf.length
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self hi, Option.getD_some,
      updE_idem, List.set_set]
  · have hle : t.conf.length ≤ replica.toNat := by omega
    simp [List.set_eq_of_length_le hle, updE_idem]

theorem forIn_id_yield' {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (g : α → β → β) (hf : ∀ a b, f a b = pure (.yield (g a b))) :
    forIn l init f = pure (l.foldl (fun b a => g a b) init) := by
  have : f = fun a b => pure (.yield (g a b)) := funext fun a => funext fun b => hf a b
  subst this
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => simp only [List.forIn_cons, List.foldl_cons]; exact ih _

/-- `updateConflicts` in the model: one update, repeated (idempotent) per command. -/
theorem updateConflicts_eq (s : RState) (cmds : List Cmd) (replica islot seq : w32) :
    model.updateConflicts s cmds replica islot seq =
      if cmds = [] then s else ucStep replica islot seq s := by
  have hfold : ∀ (l : List Cmd) (t : RState), l ≠ [] →
      l.foldl (fun r _ => ucStep replica islot seq r) t = ucStep replica islot seq t := by
    intro l
    induction l with
    | nil => intro t h; exact absurd rfl h
    | cons a l ih =>
      intro t _
      simp only [List.foldl_cons]
      cases l with
      | nil => rfl
      | cons b l' => rw [ih _ (by simp), ucStep_idem]
  unfold model.updateConflicts
  simp only [Id.run]
  rw [forIn_id_yield' (g := fun _ r => ucStep replica islot seq r)]
  · by_cases hc : cmds = []
    · subst hc; rfl
    · rw [if_neg hc, ← hfold cmds s hc]; rfl
  · intro a b; rfl

/-- `state.AllOpTypes()`. -/
theorem wp_AllOpTypes :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.state }}
      (App (Val (@! src.state.AllOpTypes)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* opsAll }} := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal (V := w8) [W8 1, W8 2, W8 6] _
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  unfold opsAll
  iapply HΦ $$ Hsl

/-- `state.OpTypesConflict(CAS, op)`: a CAS conflicts with every operation. -/
theorem wp_OpTypesConflict_CAS (o2 : w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.state }}
      (App (App (Val (@! src.state.OpTypesConflict)) (Val #(W8 6))) (Val #o2))
    {{ RET #true; True }} := by
  wp_start
  wp_auto
  wp_end

/-- `updateConflicts`'s effect on the two entries it writes (row `replica` of `conflicts1`, and
`maxSeqPerKey1`), key 0. -/
theorem wp_updateConflicts_core (h r gR st : Loc) (c1S : GoSlice) (cfs : List Loc) (cr msR : Loc)
    (sl : GoSlice) (gs : List src.state.Command) (replica inst seq : w32) (o1 o2 : Option w32)
    (hcs : model.cmdsOk (gs.map cmdOf) = true) (hrep : 0 ≤ sint.Z replica ∧ sint.Z replica < 3)
    (hcr : cfs[(sint.Z replica).toNat]? = some cr) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗ r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
        gR.[src.genericsmr.Replica, go!"Stats"] ↦□ st ∗ statsOk st ∗
        h.[src.gryff.EPaxosRMWHandler, go!"noConflicts"] ↦□ false ∗
        h.[src.gryff.EPaxosRMWHandler, go!"conflicts1"] ↦□ c1S ∗ c1S ↦*□ cfs ∗
        h.[src.gryff.EPaxosRMWHandler, go!"maxSeqPerKey1"] ↦□ msR ∗
        confRepS cr o1 ∗ confRepS msR o2 ∗ sl ↦*□ gs }}
      (App (App (App (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"updateConflicts")) (Val #sl)) (Val #replica)) (Val #inst)) (Val #seq))
    {{ RET #(); confRepS cr (if gs = [] then o1 else some (updE o1 inst)) ∗
        confRepS msR (if gs = [] then o2 else some (updE o2 seq)) }} := by
  wp_start as ⟨#HR, #HgR, #Hst, #Hsok, #HnoC, #Hc1, #Hcfs, #HmsR, Hc, Hm, #Hsl⟩
  wp_auto
  ihave %Hsllen := ownSlice_len _ _ _ $$ Hsl
  ihave IH : iprop(∃ iv : w64, i_ptr ↦ iv ∗
      confRepS cr (if sint.Z iv = 0 then o1 else some (updE o1 inst)) ∗
      confRepS msR (if sint.Z iv = 0 then o2 else some (updE o2 seq)) ∗
      ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ sint.Z sl.len⌝) $$ [i Hc Hm]
  · iexists W64 0; iframe; ipureintro; word
  irename «instance» => Hinst
  wp_for IH
  icases IH with ⟨i, Hc, Hm, %Hi⟩
  wp_auto
  wp_if_destruct
  · have hilt : sint.Z iv < sint.Z sl.len := by simpa using go.intoVal_inj Hif
    obtain ⟨c, hc⟩ : ∃ c, gs[(sint.Z iv).toNat]? = some c :=
      ⟨_, List.getElem?_eq_getElem (by have := Hsllen.1; word)⟩
    have hcok : c.K' = W64 0 ∧ c.Op' = W8 6 := by
      have := hcs
      simp only [model.cmdsOk, List.all_eq_true, List.mem_map] at this
      have h1 := this (cmdOf c) ⟨c, List.mem_of_getElem? hc, rfl⟩
      simp [model.Cmd.ok, cmdOf, model.opCAS] at h1
      exact ⟨h1.2, h1.1⟩
    have hib : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z sl.len := ⟨Hi.1, hilt⟩
    rw [ite_eq_left hib]
    icases ownSlice_elem_acc (sint.Z iv) c sl DFrac.discard gs hib.1 hc $$ Hsl with ⟨#Hc0, -⟩
    iStructNamed Hc0
    wp_apply (IntoValTyped.wp_load (t := src.state.Key.ty) _ _ _) $$ [$K] as -
    rw [hcok.1]
    have hqw : sint.Z (W64 (sint.Z replica)) = sint.Z replica := by word
    ihave %Hcfslen := ownSlice_len _ _ _ $$ Hcfs
    have hcfsl := (List.getElem?_eq_some_iff.1 hcr).1
    have hrb : 0 ≤ sint.Z (W64 (sint.Z replica)) ∧ sint.Z (W64 (sint.Z replica)) < sint.Z c1S.len := by
      rw [hqw]; have := Hcfslen.1; word
    rw [ite_eq_left hrb]
    wp_apply wp_load_slice_index (t := go.GoType.MapType src.state.Key.ty
        (go.GoType.MapType src.state.Operation.ty go.int32)) c1S (sint.Z (W64 (sint.Z replica)))
        cfs _ cr hrb.1 $$ [$Hcfs] as -
    · ipureintro; rw [hqw]; exact hcr
    generalize hcur1 : (if sint.Z iv = 0 then o1 else some (updE o1 inst)) = cur1
    generalize hcur2 : (if sint.Z iv = 0 then o2 else some (updE o2 seq)) = cur2
    icases (confRepS_open ..).1 $$ Hc with ⟨%m1, Hm1, %Hm1o, Hc⟩
    wp_apply (wp_map_lookup2 _ _ cr m1 (W64 0) (DFrac.own 1)) $$ [$Hm1] as Hm1
    wp_join iprop(∃ (ir : Loc) (im : GMap w8 w32), opMapDep_ptr ↦ ir ∗ ir ↦$ im ∗
        ⌜∀ op, im.lookup op = if op ∈ opsAll then cur1 else none⌝)
      with [opMapDep Hc] as ⟨%ir1, %im1, opMapDep, Him1, %Him1⟩
    · cases cur1 with
      | none =>
        icases Hc with %Hn
        rw [show (W64 0 : w64) = 0#64 from rfl] at Hn; simp [Hn] at Hif
      | some v =>
        icases Hc with ⟨%ir, %im, %Hir, Him, %Him⟩
        iexists ir, im; rw [Hir]; iframe; ipureintro; simpa using Him
    · cases cur1 with
      | none =>
        wp_apply (wp_map_make1 (K := w8) (V := w32) _ _) as %ir Hir
        wp_join_done
        iexists ir, ∅; iframe; ipureintro; intro op; simp
      | some v =>
        icases Hc with ⟨%ir, %im, %Hir, Him, %Him⟩
        rw [show (W64 0 : w64) = 0#64 from rfl] at Hir; simp [Hir] at Hif
    rw [ite_eq_left hib]
    wp_apply (IntoValTyped.wp_load (t := src.state.Key.ty) _ _ _) $$ [$K] as -
    icases (confRepS_open ..).1 $$ Hm with ⟨%m2, Hm2, %Hm2o, Hm⟩
    wp_apply (wp_map_lookup2 _ _ msR m2 (W64 0) (DFrac.own 1)) $$ [$Hm2] as Hm2
    wp_join iprop(∃ (ir : Loc) (im : GMap w8 w32), opMapSeq_ptr ↦ ir ∗ ir ↦$ im ∗
        ⌜∀ op, im.lookup op = if op ∈ opsAll then cur2 else none⌝)
      with [opMapSeq Hm] as ⟨%ir2, %im2, opMapSeq, Him2, %Him2⟩
    · cases cur2 with
      | none =>
        icases Hm with %Hn
        rw [show (W64 0 : w64) = 0#64 from rfl] at Hn; simp [Hn] at Hif
      | some v =>
        icases Hm with ⟨%ir, %im, %Hir, Him, %Him⟩
        iexists ir, im; rw [Hir]; iframe; ipureintro; simpa using Him
    · cases cur2 with
      | none =>
        wp_apply (wp_map_make1 (K := w8) (V := w32) _ _) as %ir Hir
        wp_join_done
        iexists ir, ∅; iframe; ipureintro; intro op; simp
      | some v =>
        icases Hm with ⟨%ir, %im, %Hir, Him, %Him⟩
        rw [show (W64 0 : w64) = 0#64 from rfl] at Hir; simp [Hir] at Hif
    wp_apply wp_AllOpTypes as %ops Hops
    ihave %Hopslen := ownSlice_len _ _ _ $$ Hops
    ihave IJ : iprop(∃ (jv : w64) (ima imb : GMap w8 w32), j_ptr ↦ jv ∗ ir1 ↦$ ima ∗ ir2 ↦$ imb ∗
        ⌜0 ≤ sint.Z jv ∧ sint.Z jv ≤ 3 ∧ (∀ op, ima.lookup op = imAt cur1 inst (sint.Z jv).toNat op) ∧
          (∀ op, imb.lookup op = imAt cur2 seq (sint.Z jv).toNat op)⌝) $$ [j Him1 Him2]
    · iexists W64 0, im1, im2; iframe; ipureintro
      refine ⟨by word, by word, fun op => ?_, fun op => ?_⟩
      · rw [Him1]; simp [imAt]
      · rw [Him2]; simp [imAt]
    wp_for IJ
    icases IJ with ⟨j, Hima, Himb, %Hj⟩
    wp_auto
    wp_if_destruct
    · have hj3 : sint.Z jv < 3 := by
        have := go.intoVal_inj Hif; simp at this; have := Hopslen.1; simp [opsAll] at *; word
      obtain ⟨opj, hopj⟩ : ∃ opj, opsAll[(sint.Z jv).toNat]? = some opj :=
        ⟨_, List.getElem?_eq_getElem (by simp [opsAll]; word)⟩
      have hjb : 0 ≤ sint.Z jv ∧ sint.Z jv < sint.Z ops.len := by
        have := Hopslen.1; simp [opsAll] at this; word
      rw [ite_eq_left hib]
      wp_apply (IntoValTyped.wp_load (t := src.state.Operation.ty) _ _ _) $$ [$Op] as -
      rw [hcok.2, ite_eq_left hjb]
      wp_apply (wp_load_slice_index (t := src.state.Operation.ty) ops (sint.Z jv) opsAll _ opj
        hjb.1) $$ [$Hops] as Hops
      · ipureintro; exact hopj
      wp_apply wp_OpTypesConflict_CAS
      rw [ite_eq_left hjb]
      wp_apply (wp_load_slice_index (t := src.state.Operation.ty) ops (sint.Z jv) opsAll _ opj
        hjb.1) $$ [$Hops] as Hops
      · ipureintro; exact hopj
      wp_apply (wp_map_lookup2 _ _ ir1 ima opj (DFrac.own 1)) $$ [$Hima] as Hima
      rw [Hj.2.2.1 opj, imAt_at _ _ _ _ hopj]
      wp_join iprop(∃ ima' : GMap w8 w32, ir1 ↦$ ima' ∗
          ⌜∀ op, ima'.lookup op = imAt cur1 inst ((sint.Z jv).toNat + 1) op⌝ ∗
          highestInterf_ptr ↦ cur1.getD (zero_val w32) ∗ instance_ptr ↦ inst ∗
          opMapDep_ptr ↦ ir1 ∗ allOpTypes_ptr ↦ ops ∗ j_ptr ↦ jv ∗ ops ↦* opsAll)
        with [Hima highestInterf Hinst opMapDep allOpTypes j Hops]
        as ⟨%ima', Hima, %Hima', highestInterf, Hinst, opMapDep, allOpTypes, j, Hops⟩
      · cases cur1 with
        | none => simp at Hif
        | some hi =>
          wp_if_destruct
          · rw [ite_eq_left hjb]
            wp_apply (wp_load_slice_index (t := src.state.Operation.ty) ops (sint.Z jv) opsAll _ opj
              hjb.1) $$ [$Hops] as Hops
            · ipureintro; exact hopj
            wp_apply (wp_mapInsert _ ir1 ima opj inst) $$ [$Hima] as Hima
            wp_join_done
            iexists _; iframe; ipureintro
            exact imAt_succ_ins _ _ _ _ hopj _ Hj.2.2.1 (updE_true _ _ (by simp only [updC, model.slt, decide_eq_true_eq]; exact Hif))
          · wp_join_done
            iexists _; iframe; ipureintro
            exact imAt_succ_keep _ _ _ _ hopj _ Hj.2.2.1 (updE_false _ _ (by simp only [updC, model.slt, decide_eq_false_iff_not]; exact Hif))
      · cases cur1 with
        | some hi => simp at Hif
        | none =>
          rw [ite_eq_left hjb]
          wp_apply (wp_load_slice_index (t := src.state.Operation.ty) ops (sint.Z jv) opsAll _ opj
            hjb.1) $$ [$Hops] as Hops
          · ipureintro; exact hopj
          wp_apply (wp_mapInsert _ ir1 ima opj inst) $$ [$Hima] as Hima
          wp_join_done
          iexists _; iframe; ipureintro
          exact imAt_succ_ins _ _ _ _ hopj _ Hj.2.2.1 (updE_true _ _ rfl)
      rw [ite_eq_left hjb]
      wp_apply (wp_load_slice_index (t := src.state.Operation.ty) ops (sint.Z jv) opsAll _ opj
        hjb.1) $$ [$Hops] as Hops
      · ipureintro; exact hopj
      wp_apply (wp_map_lookup2 _ _ ir2 imb opj (DFrac.own 1)) $$ [$Himb] as Himb
      rw [Hj.2.2.2 opj, imAt_at _ _ _ _ hopj]
      wp_join iprop(∃ imb' : GMap w8 w32, ir2 ↦$ imb' ∗
          ⌜∀ op, imb'.lookup op = imAt cur2 seq ((sint.Z jv).toNat + 1) op⌝ ∗
          maxSeq_ptr ↦ cur2.getD (zero_val w32) ∗ seq_ptr ↦ seq ∗
          opMapSeq_ptr ↦ ir2 ∗ allOpTypes_ptr ↦ ops ∗ j_ptr ↦ jv ∗ ops ↦* opsAll)
        with [Himb maxSeq seq opMapSeq allOpTypes j Hops]
        as ⟨%imb', Himb, %Himb', maxSeq, seq, opMapSeq, allOpTypes, j, Hops⟩
      · cases cur2 with
        | none => simp at Hif
        | some hi =>
          wp_if_destruct
          · rw [ite_eq_left hjb]
            wp_apply (wp_load_slice_index (t := src.state.Operation.ty) ops (sint.Z jv) opsAll _ opj
              hjb.1) $$ [$Hops] as Hops
            · ipureintro; exact hopj
            wp_apply (wp_mapInsert _ ir2 imb opj seq) $$ [$Himb] as Himb
            wp_join_done
            iexists _; iframe; ipureintro
            exact imAt_succ_ins _ _ _ _ hopj _ Hj.2.2.2 (updE_true _ _ (by simp only [updC, model.slt, decide_eq_true_eq]; exact Hif))
          · wp_join_done
            iexists _; iframe; ipureintro
            exact imAt_succ_keep _ _ _ _ hopj _ Hj.2.2.2 (updE_false _ _ (by simp only [updC, model.slt, decide_eq_false_iff_not]; exact Hif))
      · cases cur2 with
        | some hi => simp at Hif
        | none =>
          rw [ite_eq_left hjb]
          wp_apply (wp_load_slice_index (t := src.state.Operation.ty) ops (sint.Z jv) opsAll _ opj
            hjb.1) $$ [$Hops] as Hops
          · ipureintro; exact hopj
          wp_apply (wp_mapInsert _ ir2 imb opj seq) $$ [$Himb] as Himb
          wp_join_done
          iexists _; iframe; ipureintro
          exact imAt_succ_ins _ _ _ _ hopj _ Hj.2.2.2 (updE_true _ _ rfl)
      wp_for_post
      iframe
      iexists (jv + W64 1), ima', imb'
      have hj1 : (sint.Z (jv + W64 1)).toNat = (sint.Z jv).toNat + 1 := by word
      rw [hj1]
      iframe; ipureintro
      exact ⟨by word, by word, Hima', Himb'⟩
    · have hj3 : ¬ sint.Z jv < sint.Z ops.len := fun h' => Hif (by rw [decide_eq_true h'])
      rw [decide_eq_false hj3]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hjv : (sint.Z jv).toNat = 3 := by have := Hopslen.1; simp [opsAll] at this; word
      rw [hjv] at Hj
      wp_auto
      rw [ite_eq_left hib]
      wp_apply (IntoValTyped.wp_load (t := src.state.Key.ty) _ _ _) $$ [$K] as -
      rw [ite_eq_left hrb]
      wp_apply wp_load_slice_index (t := go.GoType.MapType src.state.Key.ty
          (go.GoType.MapType src.state.Operation.ty go.int32)) c1S (sint.Z (W64 (sint.Z replica)))
          cfs _ cr hrb.1 $$ [$Hcfs] as -
      · ipureintro; rw [hqw]; exact hcr
      wp_apply (wp_mapInsert _ cr m1 (W64 0) ir1) $$ [$Hm1] as Hm1
      rw [ite_eq_left hib]
      wp_apply (IntoValTyped.wp_load (t := src.state.Key.ty) _ _ _) $$ [$K] as -
      wp_apply (wp_mapInsert _ msR m2 (W64 0) ir2) $$ [$Hm2] as Hm2
      wp_for_post
      have e1 : updE cur1 inst = updE o1 inst := by rw [← hcur1]; exact cur_upd _ _ _
      have e2 : updE cur2 seq = updE o2 seq := by rw [← hcur2]; exact cur_upd _ _ _
      ihave Hc : confRepS cr (some (updE o1 inst)) $$ [Hm1 Hima]
      · rw [← e1]; iapply confRepS_close cr ir1 m1 ima cur1 inst Hm1o Hj.2.2.1; iframe
      ihave Hm : confRepS msR (some (updE o2 seq)) $$ [Hm2 Himb]
      · rw [← e2]; iapply confRepS_close msR ir2 m2 imb cur2 seq Hm2o Hj.2.2.2; iframe
      iframe
      iexists (iv + W64 1)
      have hi1 : sint.Z (iv + W64 1) = sint.Z iv + 1 := by word
      rw [hi1, if_neg (by omega), if_neg (by omega)]
      iframe; ipureintro; word
  · have hi3 : ¬ sint.Z iv < sint.Z sl.len := fun h' => Hif (by rw [decide_eq_true h'])
    rw [decide_eq_false hi3]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hiv : sint.Z iv = sint.Z sl.len := by omega
    wp_auto
    have hqw : sint.Z (W64 (sint.Z replica)) = sint.Z replica := by word
    ihave %Hcfslen := ownSlice_len _ _ _ $$ Hcfs
    have hcfsl := (List.getElem?_eq_some_iff.1 hcr).1
    have hrb : 0 ≤ sint.Z (W64 (sint.Z replica)) ∧ sint.Z (W64 (sint.Z replica)) < sint.Z c1S.len := by
      rw [hqw]; have := Hcfslen.1; word
    rw [ite_eq_left hrb]
    wp_apply wp_load_slice_index (t := go.GoType.MapType src.state.Key.ty
        (go.GoType.MapType src.state.Operation.ty go.int32)) c1S (sint.Z (W64 (sint.Z replica)))
        cfs _ cr hrb.1 $$ [$Hcfs] as -
    · ipureintro; rw [hqw]; exact hcr
    icases (confRepS_open ..).1 $$ Hc with ⟨%m1, Hm1, %Hm1o, Hc⟩
    wp_apply (wp_map_len (V := Loc) cr m1 (DFrac.own 1)) $$ [$Hm1] as Hm1
    wp_apply (StatsMap.Max.wp _ go!"conflicts_map_size" _
      (by left; simp only [statsIntKeys]; decide)) $$ [$Hsok] as %n - -- H1-R5
    ihave Hc := (confRepS_open ..).2 $$ [Hm1 Hc]
    · iexists m1; iframe; ipureintro; exact Hm1o
    iapply HΦ
    by_cases hgs : gs = []
    · subst hgs
      have : sint.Z iv = 0 := by rw [hiv]; simp at Hsllen; word
      simp only [this, ite_true]
      iframe
    · have : sint.Z iv ≠ 0 := by
        rw [hiv]; intro h0; apply hgs; apply List.eq_nil_of_length_eq_zero; have := Hsllen.1; word
      simp only [this, hgs, ite_false]
      iframe


theorem ucStep_confAt (replica islot seq : w32) (s : RState) (q : Nat)
    (hlen : replica.toNat < s.conf.length) :
    (ucStep replica islot seq s).confAt q =
      if q = replica.toNat then some (updE (s.confAt replica.toNat) islot) else s.confAt q := by
  simp only [ucStep, model.RState.confAt, List.getD_eq_getElem?_getD]
  split
  · subst q; rw [List.getElem?_set_self hlen]; rfl
  · rw [List.getElem?_set_ne (Ne.symm ‹_›)]

/-- `updateConflicts(cmds, replica, instance, seq)` (the statement of `H2/Attr.lean`). -/
theorem wp_updateConflicts' (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) (xs : XS) (s : RState)
    (sl : GoSlice) (gs : List src.state.Command) (replica inst seq : w32)
    (hcs : model.cmdsOk (gs.map cmdOf) = true) (hrep : 0 ≤ sint.Z replica ∧ sint.Z replica < 3) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ attrEnv k r gR h ∗
        epaxosOwn ρ h r xs s ∗ sl ↦*□ gs }}
      (App (App (App (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"updateConflicts")) (Val #sl)) (Val #replica)) (Val #inst)) (Val #seq))
    {{ RET #(); epaxosOwn ρ h r xs (model.updateConflicts s (gs.map cmdOf) replica inst seq) }} := by
  iintro %Φ ⟨#Hpkg, #Hae, Hep, #Hsl⟩ HΦ
  unfold attrEnv
  icases Hae with ⟨#HR, #HgR, #HId, #HN, #Hfix⟩
  unfold h2Fixed
  icases Hfix with ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
    -, -, -, -, -, -, -, #Hst, #Hsok, -⟩
  icases (epaxosOwn_open ..).1 $$ Hep with ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M, %cu, %pm,
    #HR', #HnoC, #HispS, #Hisp, #HcrtS, #Hc1S, #Hcfs, #HmsR, #HpvtR, Hcu, Hcrt, HM, HMe, Hrows, Hinsts,
    Hmono, Hconfs, Hms, Hpm, Hrest, %Hf⟩
  have hconf : s.conf.length = 3 := Hf.2.2.2.2.2.2.2.2.2.2 -- H2a-R2
  have hcfs : cfs.length = 3 := Hf.2.1
  have hrn : (sint.Z replica).toNat = replica.toNat := by
    have h1 : uint.Z replica = sint.Z replica := by word
    have h2 : uint.Z replica = (replica.toNat : Int) := rfl
    omega
  obtain ⟨cr, hcr⟩ : ∃ cr, cfs[(sint.Z replica).toNat]? = some cr :=
    ⟨_, List.getElem?_eq_getElem (by rw [hcfs]; omega)⟩
  icases (BigSepL.bigSepL_lookup_acc_impl (Φ := fun k cr => confRep cr (s.confAt k)) hcr) $$ Hconfs with ⟨Hc, Hcclose⟩
  icases (confRep_S ..).1 $$ Hc with Hc
  icases (confRep_S ..).1 $$ Hms with Hms
  wp_apply (wp_updateConflicts_core h r gR st c1S cfs cr msR sl gs replica inst seq
    (s.confAt (sint.Z replica).toNat) s.maxSeqK0 hcs hrep hcr) $$ [$Hc $Hms] as ⟨Hc, Hms⟩
  · iframe #
  iapply HΦ
  rw [updateConflicts_eq]
  by_cases hgs : gs.map cmdOf = []
  · have hgs' : gs = [] := List.map_eq_nil_iff.1 hgs
    simp only [hgs, ite_true]
    simp only [hgs', ite_true]
    icases (confRep_S ..).2 $$ Hc with Hc
    icases (confRep_S ..).2 $$ Hms with Hms
    ihave Hconfs := Hcclose $$ %(fun k cr => confRep cr (s.confAt k)) [] Hc
    · iintro !> %k %y %_ %_ H; dsimp only; iexact H
    iapply (epaxosOwn_open ..).2
    iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
    iframe # ∗
    ipureintro; exact Hf
  · have hgs' : gs ≠ [] := fun h => hgs (by simp [h])
    simp only [hgs, ite_false]
    simp only [hgs', ite_false]
    icases (confRep_S ..).2 $$ Hc with Hc
    icases (confRep_S ..).2 $$ Hms with Hms
    have hlen : replica.toNat < s.conf.length := by rw [hconf]; omega
    ihave Hconfs := Hcclose $$ %(fun k cr => confRep cr ((ucStep replica inst seq s).confAt k)) [] [Hc]
    · iintro !> %k %y %_ %hk H
      dsimp only
      rw [ucStep_confAt _ _ _ _ _ hlen, if_neg (by rw [← hrn]; exact hk)]
      iexact H
    · dsimp only
      rw [ucStep_confAt _ _ _ _ _ hlen, if_pos hrn, hrn]
      iexact Hc
    iapply (epaxosOwn_open ..).2
    iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
    have hinst : (ucStep replica inst seq s).inst = s.inst := rfl
    have hco : committedOrExecuted (ucStep replica inst seq s) = committedOrExecuted s := rfl
    have hcrt : (ucStep replica inst seq s).crtInstance = s.crtInstance := rfl
    have hcrt' : ∀ q, (ucStep replica inst seq s).crt q = s.crt q := fun _ => rfl
    have hms : (ucStep replica inst seq s).maxSeqK0 = some (updE s.maxSeqK0 seq) := rfl
    simp only [instsRep, hinst, hco, hcrt, hcrt', hms]
    iframe # ∗
    ipureintro
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, -⟩ := Hf
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, by simp [ucStep, hconf]⟩ -- H2a-R2

end

end Perennial.gryff.replica2
