module
public import Spec.go_etcd_io.bbolt.DB__mmapSize
public import Perennial.Proof.errors
public import Proof.go_etcd_io.bbolt.ErrShape
public import Proof.go_etcd_io.bbolt.Words

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem find?_range_none (p : Nat → Bool) (n : Nat) (h : ∀ j < n, p j = false) :
    (List.range n).find? p = none := by
  rw [List.find?_eq_none]
  intro x hx
  have := h x (List.mem_range.1 hx)
  simp [this]

theorem find?_range_some (p : Nat → Bool) (n k : Nat) (hk : k < n) (hp : p k = true)
    (hb : ∀ j < k, p j = false) : (List.range n).find? p = some k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.find?_append]
    by_cases hkn : k < n
    · rw [ih hkn]; rfl
    · have hk' : k = n := by omega
      subst hk'
      rw [find?_range_none p k hb]
      simp [hp]

set_option maxHeartbeats 400000 in
theorem DB.mmapSize.wp_proof : DB.mmapSize.spec (GF := GF) (hG := hG) := by
  intro dbl ps dq size Hps Hps2
  wp_start as Hdb
  wp_auto
  ihave IH : iprop(∃ (n : w64), "i" ∷ i_ptr ↦ n ∗
      "%Hn" ∷ ⌜15 ≤ uint.Z n ∧ uint.Z n ≤ 31 ∧
        ∀ j : Nat, 15 ≤ j → (j : Int) < uint.Z n → 2 ^ j < sint.Z size⌝) $$ [i]
  · iexists _; iframe; ipureintro
    refine ⟨by decide, by decide, fun j h1 h2 => ?_⟩
    exfalso; simp at h2; omega
  wp_for IH
  wp_if_destruct
  · have Hn30 : uint.Z n ≤ 30 := by word
    rw [shl_one_sint n Hn30]
    wp_if_destruct
    · try wp_auto
      wp_for_post
      ispecialize HΦ $$ %(W64 1 <<< n) %GoInterface.nil
      iapply HΦ
      iframe
      ipureintro
      have hk : n.toNat - 15 < 16 := by unfold uint.Z at Hn30; omega
      unfold mmapSizeOf
      rw [find?_range_some _ 16 (n.toNat - 15) hk
        (by simp only [decide_eq_true_eq]; rw [show 15 + (n.toNat - 15) = n.toNat by
              unfold uint.Z at Hn; omega]; exact Hif)
        (fun j hj => by
          simp only [decide_eq_false_iff_not, Int.not_le]
          exact Hn.2.2 (15 + j) (by omega) (by unfold uint.Z; omega))]
      refine ⟨rfl, ?_⟩
      rw [shl_one_sint n Hn30, show 15 + (n.toNat - 15) = n.toNat by unfold uint.Z at Hn; omega]
    · wp_for_post
      iframe
      iexists _; iframe; ipureintro
      refine ⟨by word, by word, fun j h1 h2 => ?_⟩
      by_cases hj : (j : Int) < uint.Z n
      · exact Hn.2.2 j h1 hj
      · have : (j : Int) = uint.Z n := by word
        have hjn : j = n.toNat := by unfold uint.Z at this; omega
        subst hjn
        have := shl_one_sint n Hn30
        omega
  · have Hn31 : uint.Z n = 31 := by word
    have Hnone : mmapSizeOf (sint.Z size) (sint.Z ps) =
        (if sint.Z size > 281474976710655 then none else
          let sz := if sint.Z size % 1073741824 > 0
            then sint.Z size + 1073741824 - sint.Z size % 1073741824 else sint.Z size
          let sz := if sz % sint.Z ps ≠ 0
            then (sz / sint.Z ps + 1) * sint.Z ps else sz
          some (min sz 281474976710655)) := by
      unfold mmapSizeOf
      rw [find?_range_none _ 16 (fun j hj => by
        simp only [decide_eq_false_iff_not, Int.not_le]
        exact Hn.2.2 (15 + j) (by omega) (by omega))]
    rw [Hnone]
    wp_if_destruct
    · wp_apply wp_New_ptr as %e ⟨%He, -⟩
      ispecialize HΦ $$ %(W64 0) %(GoInterface.ok e)
      iapply HΦ
      iframe
      ipureintro
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
      exact ⟨fun h => (by cases h), He⟩
    · try wp_auto
      have HS : 2 ^ 30 < sint.Z size := Hn.2.2 30 (by omega) (by omega)
      have HM : sint.Z size ≤ 281474976710655 := by word
      have Hr := sint_srem size (W64 1073741824) (by omega) (by word)
      rw [show sint.Z (W64 1073741824) = 1073741824 by rfl] at Hr
      have Hr0 := Int.emod_nonneg (sint.Z size) (by decide : (1073741824:Int) ≠ 0)
      have Hr1 := Int.emod_lt_of_pos (sint.Z size) (by decide : (0:Int) < 1073741824)
      rw [Hr]
      have h00 : sint.Z (W64 0) = 0 := rfl
      wp_if_destruct
      · try wp_auto
        generalize hz : size + (W64 1073741824 - BitVec.srem size (W64 1073741824)) = z
        have Hz : sint.Z z = (if sint.Z size % 1073741824 > 0 then sint.Z size + 1073741824 - sint.Z size % 1073741824 else sint.Z size) := by
          subst hz
          rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
          word
        have Hzb : sint.Z z ≤ 2 ^ 49 := by rw [Hz]; split <;> omega
        have Hz0' : 0 < sint.Z z := by rw [Hz]; split <;> omega
        have Hr2 := sint_srem z ps (by omega) Hps
        have Hq := sint_sdiv z ps (by omega) Hps
        have Hq0 := Int.ediv_nonneg (by omega : 0 ≤ sint.Z z) (by omega : 0 ≤ sint.Z ps)
        have Hqle := Int.ediv_le_self (sint.Z ps) (by omega : 0 ≤ sint.Z z)
        have Hqm := Int.ediv_mul_le (sint.Z z) (by omega : sint.Z ps ≠ 0)
        wp_if_destruct
        · -- the size is a whole number of pages
          have Hz0 := Hif
          try wp_auto
          wp_if_destruct
          · try wp_auto
            ispecialize HΦ $$ %(W64 281474976710655) %GoInterface.nil
            iapply HΦ; iframe; ipureintro
            rw [ite_eq_right_of_eq_false _ _ (eq_false (by word))]
            simp only []
            rw [← Hz]
            have he : ¬ (sint.Z z % sint.Z ps ≠ 0) := by
              rw [← Hr2, Hz0]; decide
            rw [ite_eq_right_of_eq_false _ _ (eq_false he)]
            refine ⟨by trivial, ?_⟩
            word
          · try wp_auto
            ispecialize HΦ $$ %z %GoInterface.nil
            iapply HΦ; iframe; ipureintro
            rw [ite_eq_right_of_eq_false _ _ (eq_false (by word))]
            simp only []
            rw [← Hz]
            have he : ¬ (sint.Z z % sint.Z ps ≠ 0) := by
              rw [← Hr2, Hz0]; decide
            rw [ite_eq_right_of_eq_false _ _ (eq_false he)]
            refine ⟨by trivial, ?_⟩
            word
        · -- rounded up to a whole page
          have Hnz := Hif
          try wp_auto
          have HQ1 : sint.Z (BitVec.sdiv z ps + W64 1) = sint.Z z / sint.Z ps + 1 := by
            rw [← Hq] at Hq0 Hqle ⊢; word
          have Hprod : (sint.Z z / sint.Z ps + 1) * sint.Z ps < 2 ^ 63 := by
            rw [Int.add_mul, Int.one_mul]; omega
          generalize hz2 : (BitVec.sdiv z ps + W64 1) * ps = z2
          have Hz2 : sint.Z z2 = (sint.Z z / sint.Z ps + 1) * sint.Z ps := by
            subst hz2
            rw [sint_mul _ _ (by rw [HQ1]; omega) (by omega) (by rw [HQ1]; exact Hprod), HQ1]
          wp_if_destruct
          · try wp_auto
            ispecialize HΦ $$ %(W64 281474976710655) %GoInterface.nil
            iapply HΦ; iframe; ipureintro
            rw [ite_eq_right_of_eq_false _ _ (eq_false (by word))]
            simp only []
            rw [← Hz]
            have hne : sint.Z z % sint.Z ps ≠ 0 := by
              intro h; apply Hnz; rw [← Hr2] at h; word
            rw [ite_eq_left_of_eq_true _ _ (eq_true hne)]
            refine ⟨by trivial, ?_⟩
            rw [← Hz2]; word
          · try wp_auto
            ispecialize HΦ $$ %z2 %GoInterface.nil
            iapply HΦ; iframe; ipureintro
            rw [ite_eq_right_of_eq_false _ _ (eq_false (by word))]
            simp only []
            rw [← Hz]
            have hne : sint.Z z % sint.Z ps ≠ 0 := by
              intro h; apply Hnz; rw [← Hr2] at h; word
            rw [ite_eq_left_of_eq_true _ _ (eq_true hne)]
            refine ⟨by trivial, ?_⟩
            rw [← Hz2]; word
      · try wp_auto
        generalize hz : size = z at HS HM Hr Hr0 Hr1 Hif ⊢
        have Hz : sint.Z z = (if sint.Z z % 1073741824 > 0 then sint.Z z + 1073741824 - sint.Z z % 1073741824 else sint.Z z) := by
          subst hz
          rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        have Hzb : sint.Z z ≤ 2 ^ 49 := by rw [Hz]; split <;> omega
        have Hz0' : 0 < sint.Z z := by rw [Hz]; split <;> omega
        have Hr2 := sint_srem z ps (by omega) Hps
        have Hq := sint_sdiv z ps (by omega) Hps
        have Hq0 := Int.ediv_nonneg (by omega : 0 ≤ sint.Z z) (by omega : 0 ≤ sint.Z ps)
        have Hqle := Int.ediv_le_self (sint.Z ps) (by omega : 0 ≤ sint.Z z)
        have Hqm := Int.ediv_mul_le (sint.Z z) (by omega : sint.Z ps ≠ 0)
        wp_if_destruct
        · -- the size is a whole number of pages
          have Hz0 := Hif
          try wp_auto
          wp_if_destruct
          · try wp_auto
            ispecialize HΦ $$ %(W64 281474976710655) %GoInterface.nil
            iapply HΦ; iframe; ipureintro
            rw [ite_eq_right_of_eq_false _ _ (eq_false (by word))]
            simp only []
            rw [← Hz]
            have he : ¬ (sint.Z z % sint.Z ps ≠ 0) := by
              rw [← Hr2, Hz0]; decide
            rw [ite_eq_right_of_eq_false _ _ (eq_false he)]
            refine ⟨by trivial, ?_⟩
            word
          · try wp_auto
            ispecialize HΦ $$ %z %GoInterface.nil
            iapply HΦ; iframe; ipureintro
            rw [ite_eq_right_of_eq_false _ _ (eq_false (by word))]
            simp only []
            rw [← Hz]
            have he : ¬ (sint.Z z % sint.Z ps ≠ 0) := by
              rw [← Hr2, Hz0]; decide
            rw [ite_eq_right_of_eq_false _ _ (eq_false he)]
            refine ⟨by trivial, ?_⟩
            word
        · -- rounded up to a whole page
          have Hnz := Hif
          try wp_auto
          have HQ1 : sint.Z (BitVec.sdiv z ps + W64 1) = sint.Z z / sint.Z ps + 1 := by
            rw [← Hq] at Hq0 Hqle ⊢; word
          have Hprod : (sint.Z z / sint.Z ps + 1) * sint.Z ps < 2 ^ 63 := by
            rw [Int.add_mul, Int.one_mul]; omega
          generalize hz2 : (BitVec.sdiv z ps + W64 1) * ps = z2
          have Hz2 : sint.Z z2 = (sint.Z z / sint.Z ps + 1) * sint.Z ps := by
            subst hz2
            rw [sint_mul _ _ (by rw [HQ1]; omega) (by omega) (by rw [HQ1]; exact Hprod), HQ1]
          wp_if_destruct
          · try wp_auto
            ispecialize HΦ $$ %(W64 281474976710655) %GoInterface.nil
            iapply HΦ; iframe; ipureintro
            rw [ite_eq_right_of_eq_false _ _ (eq_false (by word))]
            simp only []
            rw [← Hz]
            have hne : sint.Z z % sint.Z ps ≠ 0 := by
              intro h; apply Hnz; rw [← Hr2] at h; word
            rw [ite_eq_left_of_eq_true _ _ (eq_true hne)]
            refine ⟨by trivial, ?_⟩
            rw [← Hz2]; word
          · try wp_auto
            ispecialize HΦ $$ %z2 %GoInterface.nil
            iapply HΦ; iframe; ipureintro
            rw [ite_eq_right_of_eq_false _ _ (eq_false (by word))]
            simp only []
            rw [← Hz]
            have hne : sint.Z z % sint.Z ps ≠ 0 := by
              intro h; apply Hnz; rw [← Hr2] at h; word
            rw [ite_eq_left_of_eq_true _ _ (eq_true hne)]
            refine ⟨by trivial, ?_⟩
            rw [← Hz2]; word

end proof

end bbolt
end EtcdGrove
end Perennial
