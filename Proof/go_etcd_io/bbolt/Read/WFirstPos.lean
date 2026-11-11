/-
Where a writer's `first` lands (U6aa, `notes/bbolt-proof-plan.md`, "Writer reads at a fraction";
for `Cursor.first_w`), pure: a first path (every index `0`) is at position `0`; on a non-empty leaf
the cursor is there (`wCurAt … (some 0)`), on an empty one `next`'s stack is (at the end only if the
bucket is empty); either way `keyValue` reads entry `0`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.WCur
import all Proof.go_etcd_io.bbolt.Model.Cursor

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace WFirst

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

theorem sFirst_of_sAllFirst (els : List elemRef) (h : sAllFirst els) : sFirst els := by
  intro e he; rw [h e he]; rfl

/-- **A first path is at position `0`**, its leaf index `0`. -/
theorem stackPos_allFirst (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef)
    (h : sAllFirst els) : stackPos v es pids els = 0 ∧ leafIdx els = 0 := by
  have hf := sFirst_of_sAllFirst els h
  refine ⟨stackPos_first v es pids els hf, ?_⟩
  unfold leafIdx
  cases hl : els.getLast? with
  | none => rfl
  | some e => simp [hf e (List.mem_of_getLast? hl)]

/-- **`first` on a non-empty first leaf**: the cursor at `0`, `keyValue` reads entry `0`. -/
theorem first_landed (nl : Loc → Option (Loc × Nat)) (v : View) (es : List BoltEnt) (b : Loc)
    (rt : Nat) (ipg : List w8) (els : List elemRef) (pids : List Nat)
    (hp : sPathR nl v b rt els pids) (hlo : sLeafOK v ipg es pids els) (hall : sAllFirst els)
    (hcnt : leafCnt v es pids els ≠ 0) :
    wCurAt nl v es b rt ipg els (some 0) ∧
    (if leafIdx els < leafCnt v es pids els then stackPos v es pids els else es.length) = 0 ∧
    (leafIdx els ≤ leafCnt v es pids els ∨ wEndAt v es pids els) := by
  obtain ⟨hs, hl⟩ := stackPos_allFirst v es pids els hall
  have hlt : leafIdx els < leafCnt v es pids els := by omega
  exact ⟨⟨pids, hp, hlo, Or.inl ⟨hlt, hs.symm⟩⟩, by rw [if_pos hlt, hs], Or.inl (by omega)⟩

/-- **`first` on an empty first leaf**: `next`'s precondition, and where its stack is. -/
theorem first_next (nl : Loc → Option (Loc × Nat)) (v : View) (es : List BoltEnt) (b : Loc)
    (rt : Nat) (ipg : List w8) (els : List elemRef) (pids : List Nat)
    (hp : sPathR nl v b rt els pids) (hlo : sLeafOK v ipg es pids els) (hall : sAllFirst els)
    (hcnt : leafCnt v es pids els = 0) :
    wStk nl v es b rt ipg els pids ∧
    ∀ nl' els', wNextPost nl' v es b rt ipg els pids (wNextTo v es pids els) els' →
      ∃ pids', sPathR nl' v b rt els' pids' ∧ sLeafOK v ipg es pids' els' ∧
        (leafIdx els' ≤ leafCnt v es pids' els' ∨ wEndAt v es pids' els') ∧
        wCurAt nl' v es b rt ipg els' (some 0) ∧
        (if leafIdx els' < leafCnt v es pids' els' then stackPos v es pids' els' else es.length) = 0 := by
  obtain ⟨hs, hl⟩ := stackPos_allFirst v es pids els hall
  refine ⟨⟨hp, hlo, by omega⟩, fun nl' els' hnp => ?_⟩
  have ht : wNextTo v es pids els = 0 := by
    unfold wNextTo; rw [if_neg (by omega), hs]
  rw [ht] at hnp
  obtain ⟨pids', hp', hlo', hcase⟩ := hnp
  rcases hcase with ⟨-, hlt, hs'⟩ | ⟨hle, ⟨-, -, hlt⟩ | hend⟩
  · exact ⟨pids', hp', hlo', Or.inl (by omega), ⟨pids', hp', hlo', Or.inl ⟨hlt, hs'.symm⟩⟩,
      by rw [if_pos hlt, hs']⟩
  · omega
  · have he0 : es = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hc0 : leafCnt v es pids' els' = 0 := by subst he0; rfl
    exact ⟨pids', hp', hlo', Or.inr hend, ⟨pids', hp', hlo', Or.inr ⟨hend, Or.inl (by omega)⟩⟩,
      by rw [if_neg (by omega)]; omega⟩

end pure

end WFirst

end bbolt
end EtcdGrove
end Perennial
