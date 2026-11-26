/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/Tag.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1: `gryffproto.Tag`'s comparisons (`Compare`, `LessThan`, `GreaterThan`, `Equals`) against
the model's `Tag.cmp`, `Tag.lt`, `Tag.gt`, `Tag.eqT`.
-/
module

public import Dsverify.Proof.gryff.Replica2.Specs
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [strconvA : strconv.Assumptions] -- N-5

theorem cmp_cases (a b : model.Tag) :
    a.cmp b = if (sint.Z a.ts < sint.Z b.ts ∨ (sint.Z a.ts = sint.Z b.ts ∧ sint.Z a.cid < sint.Z b.cid)) ∨
      ((sint.Z a.ts = sint.Z b.ts ∧ sint.Z a.cid = sint.Z b.cid) ∧ sint.Z a.rmwc < sint.Z b.rmwc) then -1
    else if (sint.Z a.ts = sint.Z b.ts ∧ sint.Z a.cid = sint.Z b.cid) ∧ sint.Z a.rmwc = sint.Z b.rmwc then 0
    else 1 := by
  unfold model.Tag.cmp model.slt
  simp only [Bool.or_eq_true, Bool.and_eq_true, _root_.decide_eq_true_eq, beq_iff_eq, sint.Z,
    BitVec.toInt_inj]

theorem cmp_neg (a b : model.Tag)
    (h : (sint.Z a.ts < sint.Z b.ts ∨ (sint.Z a.ts = sint.Z b.ts ∧ sint.Z a.cid < sint.Z b.cid)) ∨
      ((sint.Z a.ts = sint.Z b.ts ∧ sint.Z a.cid = sint.Z b.cid) ∧ sint.Z a.rmwc < sint.Z b.rmwc)) :
    a.cmp b = -1 := by
  rw [cmp_cases, if_pos h]

theorem cmp_zero (a b : model.Tag)
    (h : (sint.Z a.ts = sint.Z b.ts ∧ sint.Z a.cid = sint.Z b.cid) ∧ sint.Z a.rmwc = sint.Z b.rmwc) :
    a.cmp b = 0 := by
  rw [cmp_cases, if_neg (by omega), if_pos h]

theorem cmp_pos (a b : model.Tag)
    (h : ¬ ((sint.Z a.ts < sint.Z b.ts ∨ (sint.Z a.ts = sint.Z b.ts ∧ sint.Z a.cid < sint.Z b.cid)) ∨
      ((sint.Z a.ts = sint.Z b.ts ∧ sint.Z a.cid = sint.Z b.cid) ∧ sint.Z a.rmwc < sint.Z b.rmwc)))
    (h' : ¬ ((sint.Z a.ts = sint.Z b.ts ∧ sint.Z a.cid = sint.Z b.cid) ∧
      sint.Z a.rmwc = sint.Z b.rmwc)) :
    a.cmp b = 1 := by
  rw [cmp_cases, if_neg h, if_neg h']

theorem Tag.wp_Compare (a : Loc) (dq : DFrac) (ga gb : src.gryffproto.Tag) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗ a ↦{dq} ga }}
      (App (Val (a @!! go.GoType.PointerType src.gryffproto.Tag.ty @!! go!"Compare")) (Val #gb))
    {{ RET #(W64 (model.Tag.cmp (tagOf ga) (tagOf gb))); a ↦{dq} ga }} := by
  wp_start as Ha
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ha
  iStructNamed Ha
  wp_auto
  repeat' wp_if_destruct
  all_goals
    ihave H := HΦ $$ [Ts Cid Rmwc]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    iExactEq H
    congr 2
    simp only [sint.Z, ← BitVec.toInt_inj] at *
    first
    | (exfalso; omega)
    | rw [cmp_neg (tagOf ga) (tagOf gb) (by simp only [tagOf, sint.Z]; omega)]
    | rw [cmp_zero (tagOf ga) (tagOf gb) (by simp only [tagOf, sint.Z]; omega)]
    | rw [cmp_pos (tagOf ga) (tagOf gb) (by simp only [tagOf, sint.Z]; omega)
        (by simp only [tagOf, sint.Z]; omega)]


theorem cmp_sint (a b : model.Tag) : sint.Z (W64 (a.cmp b)) = a.cmp b := by
  rw [cmp_cases]
  split
  · rfl
  · split <;> rfl

theorem lt_val (a b : model.Tag) :
    decide (sint.Z (W64 (a.cmp b)) < sint.Z (W64 0)) = a.lt b := by
  rw [cmp_sint]; rfl

theorem gt_val (a b : model.Tag) :
    decide (sint.Z (W64 0) < sint.Z (W64 (a.cmp b))) = a.gt b := by
  rw [cmp_sint]; unfold model.Tag.gt; simp only [gt_iff_lt]; rfl

theorem eqT_val (a b : model.Tag) :
    decide (W64 (a.cmp b) = W64 0) = a.eqT b := by
  unfold model.Tag.eqT
  rw [cmp_cases]
  split
  · rfl
  · split <;> rfl

theorem Tag.wp_LessThan (a : Loc) (dq : DFrac) (ga gb : src.gryffproto.Tag) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗ a ↦{dq} ga }}
      (App (Val (a @!! go.GoType.PointerType src.gryffproto.Tag.ty @!! go!"LessThan")) (Val #gb))
    {{ RET #((tagOf ga).lt (tagOf gb)); a ↦{dq} ga }} := by
  wp_start as Ha
  wp_auto
  wp_apply Tag.wp_Compare $$ [$Ha] as Ha
  rw [lt_val]
  iapply HΦ $$ Ha

theorem Tag.wp_GreaterThan (a : Loc) (dq : DFrac) (ga gb : src.gryffproto.Tag) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗ a ↦{dq} ga }}
      (App (Val (a @!! go.GoType.PointerType src.gryffproto.Tag.ty @!! go!"GreaterThan")) (Val #gb))
    {{ RET #((tagOf ga).gt (tagOf gb)); a ↦{dq} ga }} := by
  wp_start as Ha
  wp_auto
  wp_apply Tag.wp_Compare $$ [$Ha] as Ha
  rw [gt_val]
  iapply HΦ $$ Ha

theorem Tag.wp_Equals (a : Loc) (dq : DFrac) (ga gb : src.gryffproto.Tag) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗ a ↦{dq} ga }}
      (App (Val (a @!! go.GoType.PointerType src.gryffproto.Tag.ty @!! go!"Equals")) (Val #gb))
    {{ RET #((tagOf ga).eqT (tagOf gb)); a ↦{dq} ga }} := by
  wp_start as Ha
  wp_auto
  wp_apply Tag.wp_Compare $$ [$Ha] as Ha
  rw [eqT_val]
  iapply HΦ $$ Ha

end

end Perennial.gryff.replica2
