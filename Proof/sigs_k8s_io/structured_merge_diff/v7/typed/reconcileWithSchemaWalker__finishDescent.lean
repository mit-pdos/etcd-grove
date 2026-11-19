/-
`typed.reconcileWithSchemaWalker.finishDescent`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__finishDescent
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Union

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

theorem isSetO_null (r : Loc) (o : Option PathSet) :
    isSetO (GF := GF) r o ⊢ ⌜r = null ↔ o = none⌝ := by
  rcases o with _ | s
  · unfold isSetO; iintro %h; ipureintro; simp [h]
  · unfold isSetO; iintro H
    ihave %h := isSet_not_null _ _ $$ H
    ipureintro; simp [h]

theorem typed.reconcileWithSchemaWalker.finishDescent.wp_proof
    (h_Set_Union : fieldpath.Set.Union.spec (GF := GF)) :
    typed.reconcileWithSchemaWalker.finishDescent.spec (GF := GF) :=
    fun w w2 sc S st st2 ps ps2 fs tv rem add fs2 tv2 rem2 add2 sp R A R2 A2 => by
  wp_start as ⟨Hcore, Hcore2, #HR, #HA, #HR2, #HA2, Hsp, %Hspnn, %Hcap⟩
  unfold rwCore
  icases Hcore with ⟨%tr0, Hw, #Htr, #Hsc, %HWF⟩
  icases Hcore2 with ⟨%tr2, Hw2, -⟩
  unfold spareWalkers
  icases Hsp with (%Hn | ⟨%sl, %ws, Hspp, Hws, Hwsc, Hwl⟩)
  · exact absurd Hn Hspnn
  ihave %HRn := isSetO_null _ _ $$ HR
  ihave %HAn := isSetO_null _ _ $$ HA
  ihave %HR2n := isSetO_null _ _ $$ HR2
  ihave %HA2n := isSetO_null _ _ $$ HA2
  have hR2 : rem2 = null ∨ (rem2 ≠ null ∧ ∃ s, R2 = some s) := by
    rcases R2 with _ | s
    · exact Or.inl (HR2n.2 rfl)
    · exact Or.inr ⟨fun h => by simpa using HR2n.1 h, s, rfl⟩
  have hA2 : add2 = null ∨ (add2 ≠ null ∧ ∃ s, A2 = some s) := by
    rcases A2 with _ | s
    · exact Or.inl (HA2n.2 rfl)
    · exact Or.inr ⟨fun h => by simpa using HA2n.1 h, s, rfl⟩
  have hR : rem = null ∨ (rem ≠ null ∧ ∃ s, R = some s) := by
    rcases R with _ | s
    · exact Or.inl (HRn.2 rfl)
    · exact Or.inr ⟨fun h => by simpa using HRn.1 h, s, rfl⟩
  have hA : add = null ∨ (add ≠ null ∧ ∃ s, A = some s) := by
    rcases A with _ | s
    · exact Or.inl (HAn.2 rfl)
    · exact Or.inr ⟨fun h => by simpa using HAn.1 h, s, rfl⟩
  wp_auto
  wp_if_destruct
  all_goals (try rw [ite_eq_left (show (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧
      sint.Z (W64 0) ≤ sint.Z ps2.cap) from ⟨by word, by word, by word⟩)])
  all_goals (try wp_auto)
  all_goals (rcases hR2 with h2 | ⟨h2, s2, rfl⟩ <;> rcases hR with h1 | ⟨h1, s1, rfl⟩)
  all_goals (try subst h1); all_goals (try subst h2)
  -- toRemove
  all_goals (try (wp_if_destruct <;> try contradiction))
  all_goals (try wp_auto)
  all_goals (try (wp_if_destruct <;> try contradiction))
  all_goals (try wp_auto)
  all_goals (try (
    wp_apply h_Set_Union _ _ _ _ as %r1 #Hr1
    · iframe #))
  all_goals (try wp_auto)
  all_goals trace_state
  all_goals sorry

end proof

end smd
end EtcdGrove
end Perennial
