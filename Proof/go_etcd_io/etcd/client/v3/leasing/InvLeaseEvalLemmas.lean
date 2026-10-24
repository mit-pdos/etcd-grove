/-
Pure lemmas of the proofs of `evalCmp` and `leaseCache.evalOps`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseEval

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

section lemmas
variable [ext : FfiSyntax]

theorem sint_compareInt64M (a b : w64) : sint.Z (compareInt64M a b) = int64Cmp a b := by
  unfold compareInt64M int64Cmp cmpSign
  by_cases h1 : sint.Z a < sint.Z b
  · simp [h1]
  · by_cases h2 : a = b
    · subst h2; simp
    · have : sint.Z b < sint.Z a := by
        have : sint.Z a ≠ sint.Z b := fun h => h2 (by word)
        omega
      simp [h1, h2, this]

theorem decide_w64_eq_zero (r : w64) : decide (r = W64 0) = (sint.Z r == 0) := by
  by_cases h : r = W64 0
  · subst h; rfl
  · have h' : sint.Z r ≠ 0 := fun h0 => h (by word)
    rw [decide_eq_false h]; exact (beq_eq_false_iff_ne.mpr h').symm

theorem leaseEvalOk_false (st : LeaseCacheSt) (os : List OpFull) (n : Nat) (o : OpFull)
    (ho : os[n]? = some o)
    (hf : (decide (o.t = W64 1) && !isBadOpM o && (st.entries !! o.key).isSome) = false) :
    leaseEvalOk st os = false := by
  unfold leaseEvalOk
  rw [List.all_eq_false]
  exact ⟨o, List.mem_of_getElem? ho, by simp only [hf]; decide⟩

end lemmas

end leasing
end EtcdGrove
end Perennial
