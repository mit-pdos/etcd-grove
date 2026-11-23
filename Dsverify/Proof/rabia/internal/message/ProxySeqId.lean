/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/ProxySeqId.lean`, run `rabia-r1wake-1`.)

`ProxySeqIdEqual`, `ProxySeqIdLessThan` (message.go 95-117): pure comparisons (prover C1).
Proved for any program extensions and package instance (`*.wp_gen`), then at the run's
instances (the frozen specs').
-/
module

public import Dsverify.Proof.rabia.internal.message.SpecPure

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.message

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model bufio

section gen
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.message.Assumptions]
variable [IsPkgInit (IProp GF) pkg_id.rabia.internal.message]

theorem ProxySeqIdEqual.wp_gen (l1 l2 : Loc) (v1 v2 : ConsensusObj) (dq1 dq2 : DFrac) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ l1 ↦{dq1} v1 ∗ l2 ↦{dq2} v2 }}
    (App (App (Val (@! ProxySeqIdEqual)) (Val #l1)) (Val #l2))
  {{ RET #(decide (v1.ProSeq' = v2.ProSeq' ∧ v1.ProId' = v2.ProId'));
      l1 ↦{dq1} v1 ∗ l2 ↦{dq2} v2 }} := by
  wp_start as ⟨H1, H2⟩
  ihave %Hnn1 := typedPointsto_not_null _ _ _ $$ H1
  ihave %Hnn2 := typedPointsto_not_null _ _ _ $$ H2
  iStructNamedSuffix H1 "1"
  iStructNamedSuffix H2 "2"
  wp_auto
  repeat' wp_if_destruct
  all_goals
    ihave H1 := typedPointsto_combine l1 v1 dq1 Hnn1 $$
      [ProId1 ProSeq1 SvrSeq1 IsNull1 CliIds1 CliSeqs1 Commands1]
    · simp only [TypedPointsto.typedPointstoDef]; iframe
    ihave H2 := typedPointsto_combine l2 v2 dq2 Hnn2 $$
      [ProId2 ProSeq2 SvrSeq2 IsNull2 CliIds2 CliSeqs2 Commands2]
    · simp only [TypedPointsto.typedPointstoDef]; iframe
    by_cases hP : (v1.ProSeq' = v2.ProSeq' ∧ v1.ProId' = v2.ProId')
    · rw [decide_eq_true hP]
      first
        | (iapply HΦ; iframe; done)
        | (exfalso; simp_all; done)
        | (exfalso; simp at *; omega)
        | (exfalso; simp at *; word)
    · rw [decide_eq_false hP]
      first
        | (iapply HΦ; iframe; done)
        | (exfalso; simp_all; done)
        | (exfalso; simp at *; omega)
        | (exfalso; simp at *; word)

theorem ProxySeqIdLessThan.wp_gen (l1 l2 : Loc) (v1 v2 : ConsensusObj) (dq1 dq2 : DFrac) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ l1 ↦{dq1} v1 ∗ l2 ↦{dq2} v2 }}
    (App (App (Val (@! ProxySeqIdLessThan)) (Val #l1)) (Val #l2))
  {{ RET #(decide (v1.ProSeq'.toNat < v2.ProSeq'.toNat ∨
        (v1.ProSeq' = v2.ProSeq' ∧ v1.ProId'.toNat < v2.ProId'.toNat)));
      l1 ↦{dq1} v1 ∗ l2 ↦{dq2} v2 }} := by
  wp_start as ⟨H1, H2⟩
  ihave %Hnn1 := typedPointsto_not_null _ _ _ $$ H1
  ihave %Hnn2 := typedPointsto_not_null _ _ _ $$ H2
  iStructNamedSuffix H1 "1"
  iStructNamedSuffix H2 "2"
  wp_auto
  repeat' wp_if_destruct
  all_goals
    ihave H1 := typedPointsto_combine l1 v1 dq1 Hnn1 $$
      [ProId1 ProSeq1 SvrSeq1 IsNull1 CliIds1 CliSeqs1 Commands1]
    · simp only [TypedPointsto.typedPointstoDef]; iframe
    ihave H2 := typedPointsto_combine l2 v2 dq2 Hnn2 $$
      [ProId2 ProSeq2 SvrSeq2 IsNull2 CliIds2 CliSeqs2 Commands2]
    · simp only [TypedPointsto.typedPointstoDef]; iframe
    by_cases hP : (v1.ProSeq'.toNat < v2.ProSeq'.toNat ∨ (v1.ProSeq' = v2.ProSeq' ∧ v1.ProId'.toNat < v2.ProId'.toNat))
    · rw [decide_eq_true hP]
      first
        | (iapply HΦ; iframe; done)
        | (exfalso; simp_all; done)
        | (exfalso; simp at *; omega)
        | (exfalso; simp at *; word)
    · rw [decide_eq_false hP]
      first
        | (iapply HΦ; iframe; done)
        | (exfalso; simp_all; done)
        | (exfalso; simp at *; omega)
        | (exfalso; simp at *; word)

end gen

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.message.Assumptions]

theorem ProxySeqIdEqual.wp_proof : ProxySeqIdEqual.spec (GF := GF) :=
  ProxySeqIdEqual.wp_gen

theorem ProxySeqIdLessThan.wp_proof : ProxySeqIdLessThan.spec (GF := GF) :=
  ProxySeqIdLessThan.wp_gen

end proof
end Perennial.rabia.internal.message
