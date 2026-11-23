module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.State

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
  [TH : TreemapHyp GF]

theorem state.Conflict.spec_holds : state.Conflict.spec (GF := GF) := by
  intro g d dqg dqd gv dv wg wd hg hd
  wp_start as ⟨Hg, Hd, Hgc, Hdc⟩
  unfold cmdOk
  icases Hgc with ⟨%Hgc, -⟩
  icases Hdc with ⟨%Hdc, -⟩
  ihave %Hgn := typedPointsto_not_null _ _ _ $$ Hg
  ihave %Hdn := typedPointsto_not_null _ _ _ $$ Hd
  iStructNamedSuffix Hg "g"
  iStructNamedSuffix Hd "d"
  have hg3 : decide (gv.Op' = W8 3) = false := by
    rw [Hgc.1]; exact decide_eq_false hg
  have hd3 : decide (dv.Op' = W8 3) = false := by
    rw [Hdc.1]; exact decide_eq_false hd
  wp_auto
  repeat (first | rw [hg3] | rw [hd3] | wp_auto)
  have hc : conflict wg wd =
      (decide (sint.Z gv.K' ≤ sint.Z dv.K' ∧ sint.Z dv.K' ≤ sint.Z gv.K') &&
        (decide (gv.Op' = W8 1) || decide (dv.Op' = W8 1))) := by
    unfold conflict opPUT
    rw [← Hgc.1, ← Hgc.2, ← Hdc.1, ← Hdc.2]
    congr 1
    have : (gv.K' == dv.K') = decide (gv.K' = dv.K') := rfl
    rw [this]
    apply decide_eq_decide.mpr
    constructor
    · intro h; rw [h]; omega
    · intro h; exact BitVec.eq_of_toInt_eq (by unfold sint.Z at h; omega)
  repeat' wp_if_destruct
  all_goals
    cases hcv : conflict wg wd
  all_goals
    first
    | (exfalso; rw [hc] at hcv; simp_all; done)
    | (exfalso; rw [hc] at hcv; simp_all; omega)
    | skip
  all_goals
    iapply HΦ
    isplitl [Opg Kg Vg _g]
    · iapply typedPointsto_combine _ _ _ Hgn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    · iapply typedPointsto_combine _ _ _ Hdn
      simp only [TypedPointsto.typedPointstoDef]
      iframe


end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
