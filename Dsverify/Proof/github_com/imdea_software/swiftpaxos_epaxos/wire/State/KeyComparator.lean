module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.State

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- `KeyComparator`'s result on two keys (signed order). -/
def keyCmp (a b : w64) : w64 :=
  if sint.Z b < sint.Z a then W64 1 else if sint.Z a < sint.Z b then W64 (-1) else W64 0

theorem keyCmp_lt (a b : w64) (h : sint.Z a < sint.Z b) : keyCmp a b = W64 (-1) := by
  unfold keyCmp; simp only [show ¬ sint.Z b < sint.Z a by omega, h, ite_true, ite_false]

theorem keyCmp_gt (a b : w64) (h : sint.Z b < sint.Z a) : keyCmp a b = W64 1 := by
  unfold keyCmp; simp only [h, ite_true]

theorem keyCmp_self (a : w64) : keyCmp a a = W64 0 := by
  unfold keyCmp; simp

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]

theorem state.wp_KeyComparator (a b : w64) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state }}
    (App (App (Val (@! state.KeyComparator)) (Val #(keyIface a))) (Val #(keyIface b)))
  {{ RET #(keyCmp a b); True }} := by
  wp_start
  unfold keyIface
  wp_auto
  wp_if_destruct
  · rw [show keyCmp a b = W64 1 by simp_all [keyCmp]]
    wp_end
  have h1 : ¬ sint.Z b < sint.Z a := by simpa using Hif
  wp_if_destruct
  · have h2 : sint.Z a < sint.Z b := by simpa using Hif
    rw [show keyCmp a b = W64 (-1) by unfold keyCmp; simp only [h1, h2, ite_true, ite_false]]
    wp_end
  · have h2 : ¬ sint.Z a < sint.Z b := by simpa using Hif
    rw [show keyCmp a b = W64 0 by unfold keyCmp; simp only [h1, h2, ite_false]]
    wp_end

/-- `KeyComparator` compares the treemap's keys (gods' `cmpOk`, for `StateTreemap.ofGods`). -/
theorem state.keyComparator_cmpOk :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state ⊢
      github_com.emirpasic.gods.maps.treemap.cmpOk (GF := GF)
        (functions state.KeyComparator []) keyIface := by
  iintro #Hst
  iunfold github_com.emirpasic.gods.maps.treemap.cmpOk
  iintro !> %a %b %Φ HΦ
  wp_apply state.wp_KeyComparator a b as -
  iapply HΦ
  ipureintro
  by_cases h1 : sint.Z b < sint.Z a
  · rw [keyCmp_gt a b h1]
    have hne : a ≠ b := by rintro rfl; omega
    exact ⟨⟨fun h => absurd h (by decide), fun h => by omega⟩,
      ⟨fun h => absurd h (by decide), fun h => absurd h hne⟩⟩
  · by_cases h2 : sint.Z a < sint.Z b
    · rw [keyCmp_lt a b h2]
      have hne : a ≠ b := by rintro rfl; omega
      exact ⟨⟨fun _ => h2, fun _ => by decide⟩, ⟨fun h => absurd h (by decide), fun h => absurd h hne⟩⟩
    · have hab : a = b := BitVec.eq_of_toInt_eq (by omega)
      subst hab
      rw [keyCmp_self]
      exact ⟨⟨fun h => absurd h (by decide), fun h => absurd h h2⟩, ⟨fun _ => rfl, fun _ => rfl⟩⟩

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
