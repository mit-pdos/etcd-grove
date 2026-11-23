/-
Package `proposer`: the maximum of the replies (`getMaxFromResponses`, `isGreaterThan`) and the
comparison of proposals (`isEqualProposal`, `isEqualClientBatches`, `isEqual`).
-/
module

public import Dsverify.Proof.raxos.Proposer.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

namespace prop

section max
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
  [raxos.examples.quepaxanet.Assumptions]

theorem set_self_of_get {A : Type} (l : List A) (i : Nat) (a : A) (h : l[i]? = some a) :
    l.set i a = l := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 h
  exact List.set_getElem_self hi

theorem maxOf_snoc (f : RecSt → pure.Val) (l : List RecSt) (a : RecSt) (hl : l ≠ []) :
    maxOf f (l ++ [a]) = if (maxOf f l).tagLt (f a) then f a else maxOf f l := by
  match l, hl with
  | b :: l', _ =>
    simp only [maxOf, List.cons_append]
    rw [List.foldl_append]; rfl

/-- The reply values `xs` hold the slot states `sts` (persistent). -/
def repliesRep (xs : List RecorderResponse) (sts : List RecSt) : IProp GF :=
  iprop(⌜xs.length = sts.length⌝ ∗ [∗list] k ↦ x ∈ xs, ∃ st, ⌜sts[k]? = some st⌝ ∗ rrVal x st)

instance repliesRep_persistent (xs : List RecorderResponse) (sts : List RecSt) :
    Persistent (repliesRep (GF := GF) xs sts) := by
  unfold repliesRep; infer_instance

set_option maxHeartbeats 2000000 in
/-- `isGreaterThan(ele1, ele2, set)` for `set` "F" or "M". -/
theorem wp_isGreaterThan (p : Loc) (isF : Bool) (x : RecorderResponse) (l : Loc) (v1 v2 : pure.Val) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗
        rpRep (if isF then x.F' else x.M') v1 ∗ rpRep l v2 }}
      (App (App (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"isGreaterThan"))
        (Val #x)) (Val #l)) (Val #(if isF then go!"F" else go!"M")))
    {{ (b : Bool), RET #b; ⌜b = decide (v2.tagLt v1)⌝ }} := by
  wp_start as ⟨#H1, #H2⟩
  iunfold rpRep at H1 H2
  icases H1 with ⟨%y1, #Hy1, %Hy1f, -⟩
  icases H2 with ⟨%y2, #Hy2, %Hy2f, -⟩
  iStructNamed Hy1
  iStructNamed Hy2
  obtain ⟨a1, a2, a3⟩ := Hy1f
  obtain ⟨b1, b2, b3⟩ := Hy2f
  have inj : ∀ a b : w64, a = b ↔ sint.Z a = sint.Z b := fun a b =>
    ⟨fun h => h ▸ rfl, fun h => BitVec.eq_of_toInt_eq h⟩
  cases isF <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;>
  (repeat' (first | wp_if_destruct | wp_auto | (wp_bind (If (Val _) _ _); wp_if_destruct))) <;>
  (iapply HΦ; ipureintro) <;>
  (try simp only [inj] at *) <;>
  first
    | (exact (_root_.decide_eq_true (by unfold Val.tagLt; omega)).symm)
    | (exact (_root_.decide_eq_false (by unfold Val.tagLt; omega)).symm)

theorem wp_isGreaterThan_F (p : Loc) (x : RecorderResponse) (l : Loc) (v1 v2 : pure.Val) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ rpRep x.F' v1 ∗ rpRep l v2 }}
      (App (App (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"isGreaterThan"))
        (Val #x)) (Val #l)) (Val #(go!"F")))
    {{ (b : Bool), RET #b; ⌜b = decide (v2.tagLt v1)⌝ }} :=
  wp_isGreaterThan p true x l v1 v2

theorem wp_isGreaterThan_M (p : Loc) (x : RecorderResponse) (l : Loc) (v1 v2 : pure.Val) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ rpRep x.M' v1 ∗ rpRep l v2 }}
      (App (App (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"isGreaterThan"))
        (Val #x)) (Val #l)) (Val #(go!"M")))
    {{ (b : Bool), RET #b; ⌜b = decide (v2.tagLt v1)⌝ }} :=
  wp_isGreaterThan p false x l v1 v2

set_option maxHeartbeats 2000000 in
/-- `getMaxFromResponses(array, set)` for `set` "F" or "M". -/
theorem wp_getMaxFromResponses (γ : QNames) (isF : Bool) (p : Loc) (sl : GoSlice)
    (xs : List RecorderResponse) (sts : List RecSt) (hne : sts ≠ []) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ sl ↦*□ xs ∗ repliesRep xs sts }}
      (App (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"getMaxFromResponses"))
        (Val #sl)) (Val #(if isF then go!"F" else go!"M")))
    {{ (pr : ProposerMessage_Proposal), RET #pr;
        ⌜pr.ClientBatches' = slice.nil⌝ ∗ propRep γ pr (maxOf (if isF then RecSt.F else RecSt.M) sts) }} := by
  wp_start as ⟨#Hsl, #Hrep⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  iunfold repliesRep at Hrep
  icases Hrep with ⟨%Hlen, #Hrep⟩
  ihave #Hel : (∀ (k : Nat) (x : RecorderResponse) (st : RecSt), ⌜xs[k]? = some x⌝ →
      ⌜sts[k]? = some st⌝ → rpRep (if isF then x.F' else x.M') ((if isF then RecSt.F else RecSt.M) st)) $$ []
  · iintro %k %x %st %hx %hst
    ihave ⟨%st', %hst', #Hv⟩ := BigSepL.bigSepL_lookup (Φ := fun k x => iprop(∃ st, ⌜sts[k]? = some st⌝ ∗
      rrVal x st)) hx $$ Hrep
    rw [hst] at hst'; cases hst'
    iunfold rrVal at Hv
    icases Hv with ⟨-, #HF, #HM⟩
    cases isF <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · iexact HM
    · iexact HF
  have hne' : xs ≠ [] := by
    intro h; subst h; apply hne; apply List.eq_nil_of_length_eq_zero; simp at Hlen; omega
  obtain ⟨x0, hx0⟩ : ∃ x0, xs[0]? = some x0 := by
    rcases xs with _ | ⟨x0, _⟩
    · exact absurd rfl hne'
    · exact ⟨x0, rfl⟩
  obtain ⟨st0, hst0⟩ : ∃ st0, sts[0]? = some st0 := by
    rcases sts with _ | ⟨st0, _⟩
    · exact absurd rfl hne
    · exact ⟨st0, rfl⟩
  wp_auto
  rw [_root_.decide_eq_false (show ¬ sl.len = W64 0 by
    intro h; rw [h] at Hsll; exact hne' (List.eq_nil_of_length_eq_zero Hsll.1))]
  wp_auto
  have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
    refine ⟨by decide, ?_⟩
    have : 0 < xs.length := by rcases xs with _ | _; exact absurd rfl hne'; simp
    word
  ihave #H0 := Hel $$ %0 %x0 %st0 %hx0 %hst0
  have Hlen' : xs.length = sts.length := Hlen
  have Hsl2 : (sts.length : Int) = sint.Z sl.len := by rw [← Hlen']; word
  have htk1 : sts.take 1 = [st0] := by
    rcases sts with _ | ⟨a, l⟩; · simp at hst0
    · simp at hst0; subst hst0; simp
  cases isF <;> simp only [Bool.false_eq_true, ↓reduceIte] at *
  · wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]
    icases ownSlice_elem_acc (sint.Z (W64 0)) x0 sl _ _ (by decide) hx0 $$ Hsl with ⟨Hx0, -⟩
    iStructNamed Hx0
    wp_auto
    ihave HI : (∃ (i : w64) (m : Loc), "i" ∷ i_ptr ↦ i ∗ "max" ∷ max_ptr ↦ m ∗
        "#Hm" ∷ rpRep m (maxOf RecSt.M (sts.take (sint.nat i))) ∗
        "%Hi" ∷ ⌜1 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len⌝ : IProp GF) $$ [i max]
    · iexists W64 1, _
      iframe
      rw [show sint.nat (W64 1) = 1 from rfl, htk1]
      isplitr
      · simp only [maxOf, List.foldl_nil]; iexact H0
      ipureintro; constructor <;> word
    wp_for HI
    by_cases hi2 : sint.Z i < sint.Z sl.len
    · rw [_root_.decide_eq_true hi2]
      list_elem xs (sint.nat i) as y
      list_elem sts (sint.nat i) as sti
      simp only [_root_.decide_true, ↓reduceIte]
      have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨by word, hi2⟩
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
      wp_apply wp_load_slice_index sl (sint.Z i) xs _ y hb.1 $$ [Hsl] as -
      · iframe #; ipureintro; exact Hy_lookup
      ihave #Hy := Hel $$ %(sint.nat i) %y %sti %Hy_lookup %Hsti_lookup
      wp_apply wp_isGreaterThan_M p y m (RecSt.M sti) _ $$ [] as %b %Hb
      · iframe #
      have Hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      have Htk : sts.take (sint.nat i + 1) = sts.take (sint.nat i) ++ [sti] := by
        rw [List.take_add_one, Hsti_lookup]; rfl
      have Htne : sts.take (sint.nat i) ≠ [] := by
        have h1 : 1 ≤ sint.nat i := by word
        have h2 : 0 < sts.length := by
          rcases sts with _ | _; · exact absurd rfl hne
          · simp
        intro h; rw [List.take_eq_nil_iff] at h
        rcases h with h | h
        · omega
        · exact hne h
      cases b
      · wp_auto
        wp_for_post
        iframe
        iexists i + W64 1, m
        iframe
        rw [Hi1, Htk, maxOf_snoc _ _ _ Htne, if_neg (by simpa using Hb.symm)]
        iframe #
        ipureintro; constructor <;> word
      · wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
        icases ownSlice_elem_acc (sint.Z i) y sl _ _ hb.1 Hy_lookup $$ Hsl with ⟨Hyp, -⟩
        iStructNamed Hyp
        wp_auto
        wp_for_post
        iframe
        iexists i + W64 1, _
        iframe
        rw [Hi1, Htk, maxOf_snoc _ _ _ Htne, if_pos (by simpa using Hb.symm)]
        iframe #
        ipureintro; constructor <;> word
    · rw [_root_.decide_eq_false hi2]
      simp only [intoVal_eq_iff, Bool.false_eq_true, _root_.decide_false, ↓reduceIte,
        _root_.decide_true]
      have Hie : sint.nat i = sts.length := by word
      rw [Hie, List.take_length]
      iunfold rpRep at Hm
      icases Hm with ⟨%z, #Hz, %Hzf, #Hzids⟩
      iStructNamed Hz
      wp_auto
      ihave #Hnil := ownSlice_nil (V := Loc) (GF := GF) DFrac.discard
      iapply HΦ
      isplitr
      · ipureintro; rfl
      unfold propRep
      iexists [], []
      dsimp only
      iframe #
      isplitr
      · ipureintro; exact Hzf
      isplitr
      · iapply repList_nil
      isplitr
      · iapply BigSepL.bigSepL_nil.2; iempintro
      ipureintro; simp
  · wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]
    icases ownSlice_elem_acc (sint.Z (W64 0)) x0 sl _ _ (by decide) hx0 $$ Hsl with ⟨Hx0, -⟩
    iStructNamed Hx0
    wp_auto
    ihave HI : (∃ (i : w64) (m : Loc), "i" ∷ i_ptr ↦ i ∗ "max" ∷ max_ptr ↦ m ∗
        "#Hm" ∷ rpRep m (maxOf RecSt.F (sts.take (sint.nat i))) ∗
        "%Hi" ∷ ⌜1 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len⌝ : IProp GF) $$ [i max]
    · iexists W64 1, _
      iframe
      rw [show sint.nat (W64 1) = 1 from rfl, htk1]
      isplitr
      · simp only [maxOf, List.foldl_nil]; iexact H0
      ipureintro; constructor <;> word
    wp_for HI
    by_cases hi2 : sint.Z i < sint.Z sl.len
    · rw [_root_.decide_eq_true hi2]
      list_elem xs (sint.nat i) as y
      list_elem sts (sint.nat i) as sti
      simp only [_root_.decide_true, ↓reduceIte]
      have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨by word, hi2⟩
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
      wp_apply wp_load_slice_index sl (sint.Z i) xs _ y hb.1 $$ [Hsl] as -
      · iframe #; ipureintro; exact Hy_lookup
      ihave #Hy := Hel $$ %(sint.nat i) %y %sti %Hy_lookup %Hsti_lookup
      wp_apply wp_isGreaterThan_F p y m (RecSt.F sti) _ $$ [] as %b %Hb
      · iframe #
      have Hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      have Htk : sts.take (sint.nat i + 1) = sts.take (sint.nat i) ++ [sti] := by
        rw [List.take_add_one, Hsti_lookup]; rfl
      have Htne : sts.take (sint.nat i) ≠ [] := by
        have h1 : 1 ≤ sint.nat i := by word
        have h2 : 0 < sts.length := by
          rcases sts with _ | _; · exact absurd rfl hne
          · simp
        intro h; rw [List.take_eq_nil_iff] at h
        rcases h with h | h
        · omega
        · exact hne h
      cases b
      · wp_auto
        wp_for_post
        iframe
        iexists i + W64 1, m
        iframe
        rw [Hi1, Htk, maxOf_snoc _ _ _ Htne, if_neg (by simpa using Hb.symm)]
        iframe #
        ipureintro; constructor <;> word
      · wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
        icases ownSlice_elem_acc (sint.Z i) y sl _ _ hb.1 Hy_lookup $$ Hsl with ⟨Hyp, -⟩
        iStructNamed Hyp
        wp_auto
        wp_for_post
        iframe
        iexists i + W64 1, _
        iframe
        rw [Hi1, Htk, maxOf_snoc _ _ _ Htne, if_pos (by simpa using Hb.symm)]
        iframe #
        ipureintro; constructor <;> word
    · rw [_root_.decide_eq_false hi2]
      simp only [intoVal_eq_iff, Bool.false_eq_true, _root_.decide_false, ↓reduceIte,
        _root_.decide_true]
      have Hie : sint.nat i = sts.length := by word
      rw [Hie, List.take_length]
      iunfold rpRep at Hm
      icases Hm with ⟨%z, #Hz, %Hzf, #Hzids⟩
      iStructNamed Hz
      wp_auto
      ihave #Hnil := ownSlice_nil (V := Loc) (GF := GF) DFrac.discard
      iapply HΦ
      isplitr
      · ipureintro; rfl
      unfold propRep
      iexists [], []
      dsimp only
      iframe #
      isplitr
      · ipureintro; exact Hzf
      isplitr
      · iapply repList_nil
      isplitr
      · iapply BigSepL.bigSepL_nil.2; iempintro
      ipureintro; simp


/-- `getMaxFromResponses(array, "F")`. -/
theorem wp_getMaxFromResponses_F (γ : QNames) (p : Loc) (sl : GoSlice)
    (xs : List RecorderResponse) (sts : List RecSt) (hne : sts ≠ []) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ sl ↦*□ xs ∗ repliesRep xs sts }}
      (App (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"getMaxFromResponses"))
        (Val #sl)) (Val #(go!"F")))
    {{ (pr : ProposerMessage_Proposal), RET #pr;
        ⌜pr.ClientBatches' = slice.nil⌝ ∗ propRep γ pr (maxOf RecSt.F sts) }} := by
  exact wp_getMaxFromResponses γ true p sl xs sts hne

/-- `getMaxFromResponses(array, "M")`. -/
theorem wp_getMaxFromResponses_M (γ : QNames) (p : Loc) (sl : GoSlice)
    (xs : List RecorderResponse) (sts : List RecSt) (hne : sts ≠ []) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ sl ↦*□ xs ∗ repliesRep xs sts }}
      (App (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"getMaxFromResponses"))
        (Val #sl)) (Val #(go!"M")))
    {{ (pr : ProposerMessage_Proposal), RET #pr;
        ⌜pr.ClientBatches' = slice.nil⌝ ∗ propRep γ pr (maxOf RecSt.M sts) }} := by
  exact wp_getMaxFromResponses γ false p sl xs sts hne

/-- `isEqualProposal(p1, p2)`: equal tags if true. -/
theorem wp_isEqualProposal (γ : QNames) (p : Loc) (x1 x2 : ProposerMessage_Proposal)
    (v1 v2 : pure.Val) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ propRep γ x1 v1 ∗ propRep γ x2 v2 ∗
        ⌜x2.ClientBatches' = slice.nil⌝ }}
      (App (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"isEqualProposal"))
        (Val #x1)) (Val #x2))
    {{ (b : Bool), RET #b; ⌜b = true → v1.tagEq v2⌝ }} := by
  wp_start as ⟨#H1, #H2, %Hnil⟩
  iunfold propRep at H1 H2
  icases H1 with ⟨%bps1, %bs1, %Hf1, #Hids1, #Hcb1, #Hr1, -⟩
  icases H2 with ⟨%bps2, %bs2, %Hf2, #Hids2, #Hcb2, #Hr2, -⟩
  wp_auto
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals first | (iapply HΦ; ipureintro; intro h; cases h) | skip
  have Htag : v1.tagEq v2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← Hf1.1, ← Hf2.1, ‹x1.Priority' = x2.Priority'›]
    · rw [← Hf1.2.1, ← Hf2.2.1, ‹x1.ProposerId' = x2.ProposerId'›]
    · rw [← Hf1.2.2, ← Hf2.2.2, ‹x1.ThreadId' = x2.ThreadId'›]
  have hl0 : x1.ClientBatches'.len = W64 0 := by rw [Hif, Hnil]; rfl
  wp_method_call
  unfold Proposer.isEqualClientBatches.impl
  wp_auto
  rw [_root_.decide_eq_true Hif]
  wp_auto
  wp_for
  wp_if_destruct
  · exfalso; rw [hl0] at Hif; revert Hif; decide
  · iapply HΦ
    ipureintro; intro _; exact Htag

end max

end prop

end Perennial.raxos
