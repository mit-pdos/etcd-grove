/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2a/Equal.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2a: `equal`
-/
module

public import Dsverify.Proof.gryff.H2.Base
public import Dsverify.Proof.gryff.Wire.Proof.Lemmas
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF] -- H1-R6 / N-1
variable [strconvA : strconv.Assumptions] -- N-5
variable [sortA : Perennial.gryff.replica2.SortSliceHyp GF]


set_option goose.wp.extras true

theorem depsEqual_iff (a b : Deps) :
    model.depsEqual a b = true ↔ ∀ q : Nat, q < 5 → a.at q = b.at q := by
  simp [model.depsEqual, List.all_eq_true]

/-- `equal(&deps1, &deps2)`. -/
theorem wp_equal (p1 p2 : Loc) (a b : GoArray w32 5) (dq1 dq2 : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ p1 ↦{dq1} a ∗ p2 ↦{dq2} b }}
      (App (App (Val (@! src.gryff.equal)) (Val #p1)) (Val #p2))
    {{ RET #(model.depsEqual (depsOf a) (depsOf b)); p1 ↦{dq1} a ∗ p2 ↦{dq2} b }} := by
  wp_start as ⟨Ha, Hb⟩
  wp_auto
  ihave IH : iprop(∃ j : w64, i_ptr ↦ j ∗ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 5 ∧
      ∀ q : Nat, q < (sint.Z j).toNat → (depsOf a).at q = (depsOf b).at q⌝) $$ [i]
  · iexists W64 0; iframe; ipureintro; refine ⟨by word, by word, fun q hq => ?_⟩; simp at hq
  wp_for IH
  icases IH with ⟨i, %Hi⟩
  wp_auto
  wp_if_destruct
  · ihave %Hal := array_len _ _ _ _ $$ Ha
    ihave %Hbl := array_len _ _ _ _ $$ Hb
    have hj : 0 ≤ sint.Z j ∧ sint.Z j < 5 := by
      have : sint.Z j < sint.Z (W64 5) := by simpa using go.intoVal_inj Hif
      word
    rw [ite_eq_left hj]
    wp_apply wire.wp_load_arr32 $$ [$Ha] as Ha
    · ipureintro; word
    rw [ite_eq_left hj]
    wp_apply wire.wp_load_arr32 $$ [$Hb] as Hb
    · ipureintro; word
    wp_if_destruct
    · wp_for_post
      iframe
      iexists (j + W64 1); iframe; ipureintro
      refine ⟨by word, by word, fun q hq => ?_⟩
      have hj1 : (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 := by word
      rw [hj1] at hq
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | rfl
      · exact Hi.2.2 q hq
      · simpa [model.Deps.at, depsOf, List.getD_eq_getElem?_getD] using Hif
    · wp_for_post
      have : model.depsEqual (depsOf a) (depsOf b) = false := by
        rw [← Bool.not_eq_true, depsEqual_iff]; intro h
        apply Hif
        have := h (sint.Z j).toNat (by omega)
        simpa [model.Deps.at, depsOf, List.getD_eq_getElem?_getD] using this
      rw [this]
      iapply HΦ; iframe
  · have hj5 : ¬ sint.Z j < sint.Z (W64 5) := fun h => Hif (by rw [decide_eq_true h])
    rw [decide_eq_false hj5]; simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    have : model.depsEqual (depsOf a) (depsOf b) = true := by
      rw [depsEqual_iff]; intro q hq; apply Hi.2.2
      have : sint.Z j = 5 := by word
      rw [this]; simpa using hq
    rw [this]
    iapply HΦ; iframe

end

end Perennial.gryff.replica2
