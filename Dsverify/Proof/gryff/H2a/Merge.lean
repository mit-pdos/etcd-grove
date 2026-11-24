/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2a/Merge.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2a: `mergeAttributes`
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

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem forIn_id_yield {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (g : α → β → β) (hf : ∀ a b, f a b = pure (.yield (g a b))) :
    forIn l init f = pure (l.foldl (fun b a => g a b) init) := by
  have : f = fun a b => pure (.yield (g a b)) := funext fun a => funext fun b => hf a b
  subst this
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => simp only [List.forIn_cons, List.foldl_cons]; exact ih _

/-- One iteration (`q`) of `mergeAttributes`'s loop over the dependencies (`(equal, deps1)`). -/
def mergeIter (myId : w32) (d2 : Deps) (q : Nat) (st : Bool × Deps) : Bool × Deps :=
  if BitVec.ofNat 32 q = myId then st
  else if st.2.at q ≠ d2.at q then
    (false, if model.sgt (d2.at q) (st.2.at q) then st.2.setAt q (d2.at q) else st.2)
  else st

theorem mergeAttributes_eq (s : RState) (seq1 : w32) (d1 : Deps) (seq2 : w32) (d2 : Deps) :
    model.mergeAttributes s seq1 d1 seq2 d2 =
      (if seq1 ≠ seq2 then (if model.sgt seq2 seq1 then seq2 else seq1) else seq1,
        ((List.range 3).foldl (fun b a => mergeIter s.id d2 a b) (decide (seq1 = seq2), d1)).2,
        ((List.range 3).foldl (fun b a => mergeIter s.id d2 a b) (decide (seq1 = seq2), d1)).1) := by
  unfold model.mergeAttributes
  simp only [Id.run]
  have hb : ∀ (a : Nat) (b : Bool × Deps),
      (if BitVec.ofNat 32 a = s.id then Pure.pure (ForInStep.yield (b.fst, b.snd))
        else if b.snd.at a ≠ d2.at a then
          if model.sgt (d2.at a) (b.snd.at a) = true then
            Pure.pure (ForInStep.yield (false, b.snd.setAt a (d2.at a)))
          else Pure.pure (ForInStep.yield (false, b.snd))
        else Pure.pure (ForInStep.yield (b.fst, b.snd)) : Id (ForInStep (Bool × Deps))) =
      pure (.yield (mergeIter s.id d2 a b)) := by
    intro a b; unfold mergeIter
    by_cases h1 : BitVec.ofNat 32 a = s.id <;> by_cases h2 : b.2.at a = d2.at a <;>
      by_cases h3 : model.sgt (d2.at a) (b.snd.at a) = true <;> simp [h1, h2, h3]
  rw [forIn_id_yield _ _ _ (mergeIter s.id d2) hb, forIn_id_yield _ _ _ (mergeIter s.id d2) hb]
  by_cases h : seq1 = seq2
  · subst h; simp [List.range_succ]; rfl
  · by_cases h' : model.sgt seq2 seq1 = true <;> simp [h, h', List.range_succ] <;> rfl

theorem range_fold_succ {β : Type} (f : β → Nat → β) (init : β) (qv : w64)
    (h : 0 ≤ sint.Z qv ∧ sint.Z qv < 5) :
    (List.range (sint.Z (qv + W64 1)).toNat).foldl f init =
      f ((List.range (sint.Z qv).toNat).foldl f init) (sint.Z qv).toNat := by
  have : (sint.Z (qv + W64 1)).toNat = (sint.Z qv).toNat + 1 := by word
  rw [this, List.range_succ, List.foldl_append]; rfl

theorem ofNat_toNat_sint (qv : w64) (h : 0 ≤ sint.Z qv ∧ sint.Z qv < 5) :
    BitVec.ofNat 32 (sint.Z qv).toNat = W32 (sint.Z qv) := by
  obtain ⟨n, hn⟩ : ∃ n : Nat, sint.Z qv = n := ⟨_, (Int.toNat_of_nonneg h.1).symm⟩
  rw [hn, Int.toNat_natCast]
  simp only [W32, BitVec.ofInt_natCast]

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF] -- H1-R6 / N-1
variable [sortA : Perennial.gryff.replica2.SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

/-- `mergeAttributes(seq1, deps1, seq2, deps2)`. -/
theorem wp_mergeAttributes (k : Fin 3) (r gR h : Loc) (s : RState) (hid : s.id = rid32 k)
    (seq1 : w32) (d1 : GoArray w32 5) (seq2 : w32) (d2 : GoArray w32 5) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ attrEnv k r gR h }}
      (App (App (App (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"mergeAttributes")) (Val #seq1)) (Val #d1)) (Val #seq2)) (Val #d2))
    {{ (seq' : w32) (d' : GoArray w32 5) (eq : Bool), RET (PairV (PairV #seq' #d') #eq);
        ⌜model.mergeAttributes s seq1 (depsOf d1) seq2 (depsOf d2) = (seq', depsOf d', eq)⌝ }} := by
  wp_start as #Henv
  unfold attrEnv
  icases Henv with ⟨#HR, #HgR, #HId, #HN, -⟩
  ihave #Hdpkg : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog $$ []
  · solve_pkg_init
  ihave #Hdlog := replica.dlog_init_access $$ Hdpkg
  wp_auto
  wp_join iprop(seq1_ptr ↦ (if seq1 ≠ seq2 then (if model.sgt seq2 seq1 then seq2 else seq1) else seq1) ∗
      equal_ptr ↦ decide (seq1 = seq2) ∗ e_ptr ↦ h ∗ seq2_ptr ↦ seq2)
    with [seq1 equal e seq2] as ⟨seq1, equal, e, seq2⟩
  · subst Hif
    simp only [ne_eq, not_true_eq_false, ite_false, decide_true]
    iframe
  · wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %_ ⟨-, -⟩
    wp_auto
    wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
    wp_if_destruct
    · have h1 : model.sgt seq2 seq1 = true := by simp [model.sgt, model.slt, Hif]
      simp only [ne_eq, ‹¬seq1 = seq2›, not_false_eq_true, ite_true, h1]
      iframe
    · have h1 : model.sgt seq2 seq1 = false := by simp [model.sgt, model.slt, Hif]
      simp only [ne_eq, ‹¬seq1 = seq2›, not_false_eq_true, ite_true, h1, Bool.false_eq_true, ite_false]
      iframe
  ihave IH : iprop(∃ qv : w64, q_ptr ↦ qv ∗
      deps1_ptr ↦ (array.mk 5 ((List.range (sint.Z qv).toNat).foldl
        (fun b a => mergeIter s.id (depsOf d2) a b) (decide (seq1 = seq2), depsOf d1)).2 : GoArray w32 5) ∗
      equal_ptr ↦ ((List.range (sint.Z qv).toNat).foldl
        (fun b a => mergeIter s.id (depsOf d2) a b) (decide (seq1 = seq2), depsOf d1)).1 ∗
      ⌜0 ≤ sint.Z qv ∧ sint.Z qv ≤ 3⌝) $$ [q deps1 equal]
  · iexists W64 0
    iframe
    ipureintro; word
  wp_for IH
  icases IH with ⟨q, D, E, %Hq⟩
  generalize hst : List.foldl (fun b a => mergeIter s.id (depsOf d2) a b)
    (decide (seq1 = seq2), depsOf d1) (List.range (sint.Z qv).toNat) = st
  wp_auto
  wp_if_destruct
  · have hq3 : sint.Z qv < 3 := by have := go.intoVal_inj Hif; simp at this; word
    have hq5 : 0 ≤ sint.Z qv ∧ sint.Z qv < 5 := by omega
    have hstep := range_fold_succ (fun b a => mergeIter s.id (depsOf d2) a b)
      (decide (seq1 = seq2), depsOf d1) qv hq5
    rw [hst] at hstep
    have hn := ofNat_toNat_sint qv hq5
    wp_if_destruct
    · wp_for_post
      have : mergeIter s.id (depsOf d2) (sint.Z qv).toNat st = st := by
        simp [mergeIter, hn, Hif, hid]
      iframe; iexists (qv + W64 1)
      rw [hstep, this]
      iframe; ipureintro; word
    · have hne := Hif
      ihave %Hdl := array_len _ _ _ _ $$ D
      ihave %Hd2l := array_len _ _ _ _ $$ deps2
      rw [ite_eq_left hq5]
      wp_apply wire.wp_load_arr32 $$ [$D] as D
      · ipureintro; word
      rw [ite_eq_left hq5]
      wp_apply wire.wp_load_arr32 $$ [$deps2] as deps2
      · ipureintro; word
      wp_if_destruct
      · wp_for_post
        have : mergeIter s.id (depsOf d2) (sint.Z qv).toNat st = st := by
          simp only [List.getD_eq_getElem?_getD] at Hif
          simp [mergeIter, hn, hne, hid, model.Deps.at, depsOf, List.getD_eq_getElem?_getD]
          intro h; exact absurd Hif h
        iframe; iexists (qv + W64 1)
        rw [hstep, this]
        iframe; ipureintro; word
      · have hneq := Hif
        simp only [List.getD_eq_getElem?_getD] at hneq
        wp_apply wp_slice_literal (V := GoInterface) _
        isplitr
        · ipureintro; rfl
        iintro %_ ⟨-, -⟩
        wp_auto
        wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
        rw [ite_eq_left hq5]
        wp_apply wire.wp_load_arr32 $$ [$deps2] as deps2
        · ipureintro; word
        rw [ite_eq_left hq5]
        wp_apply wire.wp_load_arr32 $$ [$D] as D
        · ipureintro; word
        wp_if_destruct
        · rw [ite_eq_left hq5]
          wp_apply wire.wp_load_arr32 $$ [$deps2] as deps2
          · ipureintro; word
          rw [ite_eq_left hq5]
          wp_apply wire.wp_store_arr32 $$ [$D] as D
          · ipureintro; word
          wp_for_post
          have : mergeIter s.id (depsOf d2) (sint.Z qv).toNat st = (false,
              st.2.set (sint.Z qv).toNat (d2.arr.getD (sint.Z qv).toNat (W32 0))) := by
            have hW : (W32 0 : w32) = 0#32 := rfl
            simp only [List.getD_eq_getElem?_getD, hW] at Hif hneq
            simp [mergeIter, hn, hne, hid, model.Deps.at, depsOf, List.getD_eq_getElem?_getD,
              model.sgt, model.slt, model.Deps.setAt, hneq, Hif]
          iframe; iexists (qv + W64 1)
          rw [hstep, this]
          iframe; ipureintro; word
        · wp_for_post
          have : mergeIter s.id (depsOf d2) (sint.Z qv).toNat st = (false, st.2) := by
            have hW : (W32 0 : w32) = 0#32 := rfl
            simp only [List.getD_eq_getElem?_getD, hW] at Hif hneq
            simp [mergeIter, hn, hne, hid, model.Deps.at, depsOf, List.getD_eq_getElem?_getD,
              model.sgt, model.slt, hneq, Hif]
          iframe; iexists (qv + W64 1)
          rw [hstep, this]
          iframe; ipureintro; word
  · have hq3 : ¬ sint.Z qv < sint.Z (W64 3) := fun h' => Hif (by rw [decide_eq_true h'])
    rw [decide_eq_false hq3]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hqv : (sint.Z qv).toNat = 3 := by word
    rw [hqv] at hst
    wp_auto
    iapply HΦ
    ipureintro
    rw [mergeAttributes_eq, hst]
    rfl

end

end Perennial.gryff.replica2
