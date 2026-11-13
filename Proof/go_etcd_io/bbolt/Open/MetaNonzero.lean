/-
A well-formed file's meta pages are not all zero (U11, `notes/bbolt-proof-plan.md`): `Open` takes
the `init` branch on a file whose first `min(size, 8192)` bytes are zero (`metasZero`), which for
a file `fileHolds` describes happens only when it is empty (`fileOK`'s first case): the current
meta is valid, so its magic is not zero.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.FileHolds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- The meta of an all-zero page is not valid (its magic is 0). -/
theorem metaValid_zero : ¬ metaValid (decode (List.replicate 64 (W8 0)) : Meta) := by
  have e : (decode (List.replicate 64 (W8 0)) : Meta).magic' = W32 0 := rfl
  unfold metaValid boltMagic
  intro h
  have := h.1
  rw [e] at this
  revert this
  decide

/-- The meta of a page whose bytes are all zero is not valid. -/
theorem metaOf_zero_invalid (pg : List w8) (hl : 80 ≤ pg.length) (hz : ∀ b ∈ pg, b = W8 0) :
    ¬ metaValid (metaOf pg) := by
  have : bytesAt pg 16 64 = List.replicate 64 (W8 0) := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp [bytesAt]; omega, fun b hb => hz b ?_⟩
    exact List.mem_of_mem_drop (List.mem_of_mem_take hb)
  unfold metaOf
  rw [this]
  exact metaValid_zero

/-- **A `metaOk` image's meta pages are not all zero.** -/
theorem fileImage_metas_nonzero (xs : List w8) (C : CommitSt) (hI : fileImage xs C)
    (hC : C.metaOk) : ¬ ∀ b ∈ xs.take 8192, b = W8 0 := by
  intro hz
  obtain ⟨h0, h1, -⟩ := hI
  obtain ⟨hl0, hl1, -, -, -, hv, -⟩ := hC
  have hsub : ∀ i, ∀ b ∈ C.slot i, b = W8 0 := by
    intro i b hb
    unfold CommitSt.slot at hb
    split at hb
    · rw [h0] at hb
      apply hz
      unfold bytesAt at hb
      rw [List.drop_zero] at hb
      exact (List.take_subset_take_left _ (by omega)) hb
    · rw [h1] at hb
      apply hz
      unfold bytesAt at hb
      rw [List.take_drop] at hb
      exact List.mem_of_mem_drop hb
  have hlen : 80 ≤ (C.slot C.txid).length := by
    unfold CommitSt.slot; split <;> omega
  exact metaOf_zero_invalid _ hlen (hsub C.txid) hv

/-- **`Open`'s branch**: a file `fileOK` describes with all-zero meta pages is empty. -/
theorem fileOK_metasZero (xs : List w8) (size : Nat) (D : Data) (h : fileOK xs size D)
    (hz : ∀ b ∈ xs.take 8192, b = W8 0) : size = 0 ∧ D = ∅ := by
  rcases h with h | ⟨C, hI, hC, -⟩
  · exact h
  · exact absurd hz (fileImage_metas_nonzero xs C hI hC)

end pure

end bbolt
end EtcdGrove
end Perennial
