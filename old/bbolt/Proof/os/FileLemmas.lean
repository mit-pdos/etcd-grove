/-
Lemmas about the file model (`FileModel.lean`).
-/
module

public import Proof.os.FileModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- No offsets, no cells. -/
theorem mapRange_empty (m : Option (Loc × Nat)) (bs : List w8) (lo hi : Nat) (h : hi ≤ lo) :
    (mapRange (GF := GF) m bs lo hi) ⊣⊢ emp := by
  unfold mapRange
  cases m with
  | none => exact .rfl
  | some pn =>
    obtain ⟨p, n⟩ := pn
    simp only
    have : ((bs.take n).take hi).drop lo = [] := by
      rw [List.drop_eq_nil_iff]; simp only [List.length_take]; omega
    rw [this]
    exact bytesPointsto_nil _ _

/-- Past the end of the file, no cells. -/
theorem mapRange_beyond (m : Option (Loc × Nat)) (bs : List w8) (lo hi : Nat) (h : bs.length ≤ lo) :
    (mapRange (GF := GF) m bs lo hi) ⊣⊢ emp := by
  unfold mapRange
  cases m with
  | none => exact .rfl
  | some pn =>
    obtain ⟨p, n⟩ := pn
    simp only
    have : ((bs.take n).take hi).drop lo = [] := by
      rw [List.drop_eq_nil_iff]; simp only [List.length_take]; omega
    rw [this]
    exact bytesPointsto_nil _ _

theorem truncBytes_length (bs : List w8) (n : Nat) (h : bs.length ≤ n) :
    (truncBytes bs n).length = n := by
  unfold truncBytes; simp only [List.length_append, List.length_take, List.length_replicate]; omega

/-- A truncate that grew the file (or did nothing): its new cells. -/
theorem mapRange_grown (m : Option (Loc × Nat)) (bs bs' : List w8) (n : Nat) (hn : bs.length ≤ n)
    (h : bs' = truncBytes bs n ∨ bs' = bs) :
    mapRange (GF := GF) m bs' bs.length n ⊢ mapRange m bs' bs.length bs'.length := by
  rcases h with h | h
  · rw [h, truncBytes_length bs n hn]
  · rw [h]
    exact (mapRange_beyond m bs _ _ (Nat.le_refl _)).1.trans
      (mapRange_beyond m bs _ _ (Nat.le_refl _)).2

end lemmas

end bbolt
end EtcdGrove
end Perennial
