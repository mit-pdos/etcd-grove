/-
A meta read from its own bytes is itself (`metaOf_metaBytes`): the bytes of a meta determine
it, so two metas with the same bytes are equal (`metaBytes_inj`).
-/
module

public import Proof.go_etcd_io.bbolt.PageView
public import Proof.go_etcd_io.bbolt.internal.common.Inodes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

theorem leInt_leBytes : ∀ (n z : Nat), z < 2 ^ (8 * n) → leInt (leBytes n (z : Int)) = z
  | 0, z, h => by
    have : z = 0 := by rw [Nat.mul_zero, Nat.pow_zero] at h; omega
    subst this; rfl
  | n + 1, z, h => by
    simp only [leBytes]
    rw [leInt_cons]
    have hz : ((z : Int) / 256) = ((z / 256 : Nat) : Int) := by omega
    rw [hz, leInt_leBytes n (z / 256) (by
      rw [show 8 * (n + 1) = 8 * n + 8 by omega, Nat.pow_add] at h; omega)]
    have : (BitVec.ofInt 8 (z : Int)).toNat = z % 256 := by
      rw [BitVec.toNat_ofInt]; omega
    rw [this]; omega

theorem leAt_leBytes_app (A B : List w8) (n z : Nat) (hz : z < 2 ^ (8 * n)) :
    leAt (A ++ leBytes n (z : Int) ++ B) A.length n = z := by
  unfold leAt
  rw [List.append_assoc, List.drop_left, List.take_left' (leBytes_length' n _)]
  rw [leInt_leBytes n z hz]; rfl

theorem leAt_app_right (A L : List w8) (k w : Nat) (h : A.length ≤ k) :
    leAt (A ++ L) k w = leAt L (k - A.length) w := by
  obtain ⟨d, rfl⟩ : ∃ d, k = A.length + d := ⟨k - A.length, by omega⟩
  unfold leAt
  rw [← List.drop_drop, List.drop_left, Nat.add_sub_cancel_left]

theorem leAt_app_left (A L : List w8) (k w : Nat) (h : k + w ≤ A.length) :
    leAt (A ++ L) k w = leAt A k w := by
  unfold leAt
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem leAt_leBytes (n z : Nat) (hz : z < 2 ^ (8 * n)) : leAt (leBytes n (z : Int)) 0 n = z := by
  unfold leAt
  rw [List.drop_zero, List.take_of_length_le (by rw [leBytes_length']; omega), leInt_leBytes n z hz]; rfl

theorem w32_of_toNat (x : w32) : W32 ((x.toNat : Nat) : Int) = x := by word
theorem w64_of_toNat (x : w64) : W64 ((x.toNat : Nat) : Int) = x := by word

theorem metaOf_metaBytes (m : Meta) : metaOf (metaBytes m) = m := by
  unfold metaOf metaBytes inBucketBytes
  simp (disch := (simp only [List.length_append, leBytes_length']; omega)) only
    [leAt_app_right, leAt_app_left, leBytes_length', List.length_append, Nat.sub_self]
  simp only [leAt_leBytes _ _ (BitVec.isLt _), w32_of_toNat, w64_of_toNat]

theorem metaBytes_inj (a b : Meta) (h : metaBytes a = metaBytes b) : a = b := by
  rw [← metaOf_metaBytes a, h, metaOf_metaBytes]

end pure

end bbolt
end EtcdGrove
end Perennial
