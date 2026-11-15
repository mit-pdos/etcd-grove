/-
**Names in a clean absolute directory** (WAL leaf specs, 2026-11-13): what the WAL and `fileutil`
need of `filepath.Join(dir, name)`, `Base` and `Dir` (whose specs are `path`'s models,
`Proof/path/Model.lean`). Lean-first.

A clean absolute directory is a path `/s1/.../sn` (`n ≥ 1`) of clean segments (`path.cleanSeg`:
non-empty, no `/`, not `.` or `..`; `Proof/path/Segs.lean`'s `segsPath`), and a clean name is one
such segment (a WAL segment `0000000000000000-0000000000000000.wal`, `0.tmp`, `.touch`). Then
`Join(dir, name)` is `dir + "/" + name`, again a clean absolute directory, whose `Base` is `name`
and `Dir` is `dir`; and `Clean(dir)` is `dir`. As the main tree's `Proof/path/Segs.lean`
(`joinModel_segs`, `baseModel_seg`, `dirModel_segs`), for clean segments instead of plain ones
(without `.`).
-/
module

public import Proof.path.Segs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace filepath

open path

/-- **A clean absolute path**: `/s1/.../sn`, `n ≥ 1`, of clean segments. -/
def CleanAbs (d : List w8) : Prop :=
  ∃ segs : List (List w8), segs ≠ [] ∧ (∀ s ∈ segs, cleanSeg s) ∧ d = segsPath segs

/-- `Clean(dir)` of a clean absolute path: itself. -/
theorem cleanModel_cleanAbs (d : List w8) (hd : CleanAbs d) : cleanModel d = d := by
  obtain ⟨segs, hne, hp, rfl⟩ := hd
  simpa using cleanModel_segs segs [] hne hp (Or.inl rfl)

/-- A clean absolute path with a clean name appended is one. -/
theorem cleanAbs_append (d n : List w8) (hd : CleanAbs d) (hn : cleanSeg n) :
    CleanAbs (d ++ [slash] ++ n) := by
  obtain ⟨segs, hne, hp, rfl⟩ := hd
  refine ⟨segs ++ [n], by simp, ?_, (segsPath_snoc segs n).symm⟩
  intro x hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact hp x hx
  · exact hn

/-- **`Join(dir, name)`**: `dir + "/" + name`. -/
theorem joinModel_name (d n : List w8) (hd : CleanAbs d) (hn : cleanSeg n) :
    joinModel [d, n] = d ++ [slash] ++ n := by
  obtain ⟨segs, hne, hp, rfl⟩ := hd
  have hl := segsPath_length_two segs hne hp
  have h0 : segsPath segs ≠ [] := by intro h; rw [h] at hl; simp at hl
  have hA : 0 < (segsPath segs).length := by omega
  have hb : joinBuf [segsPath segs, n] [] = segsPath (segs ++ [n]) := by
    rw [segsPath_snoc]
    simp [joinBuf, h0, hA]
  have hsum : ([segsPath segs, n].map List.length).sum ≠ 0 := by
    intro h
    have : (segsPath segs).length ≤ ([segsPath segs, n].map List.length).sum := by simp
    omega
  unfold joinModel
  rw [if_neg hsum, hb]
  have := cleanModel_segs (segs ++ [n]) [] (by simp) (by
    intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hp x hx
    · exact hn) (Or.inl rfl)
  simp only [List.append_nil] at this
  rw [this, segsPath_snoc]

/-- **`Base(dir + "/" + name)`**: `name`. -/
theorem baseModel_name (q n : List w8) (hn : cleanSeg n) : baseModel (q ++ [slash] ++ n) = n := by
  obtain ⟨hne, hcs, -, -⟩ := hn
  obtain ⟨s', x, rfl⟩ : ∃ s' x, n = s' ++ [x] := by
    cases h : n.reverse with
    | nil => exact absurd (List.reverse_eq_nil_iff.1 h) hne
    | cons x r => exact ⟨r.reverse, x, by rw [← List.reverse_reverse n, h]; simp⟩
  have hx : x ≠ slash := hcs x (by simp)
  have hst : stripSlashes (q ++ [slash] ++ (s' ++ [x])) = q ++ [slash] ++ (s' ++ [x]) := by
    rw [show q ++ [slash] ++ (s' ++ [x]) = (q ++ [slash] ++ s') ++ [x] by simp,
      stripSlashes_snoc_ne _ _ hx]
  have hl := lastIndexByte_seg q (s' ++ [x]) (fun c hc => hcs c hc)
  unfold baseModel
  rw [if_neg (by simp)]
  simp only [hst, hl]
  simp

/-- **`Dir(dir + "/" + name)`**: `dir`. -/
theorem dirModel_name (d n : List w8) (hd : CleanAbs d) (hn : cleanSeg n) :
    dirModel (d ++ [slash] ++ n) = d := by
  obtain ⟨segs, hne, hp, rfl⟩ := hd
  have hl := lastIndexByte_seg (segsPath segs) n (fun c hc => hn.2.1 c hc)
  unfold dirModel splitModel
  rw [hl]
  have : (((segsPath segs).length : Int) + 1).toNat = (segsPath segs).length + 1 := by omega
  rw [this]
  have ht : List.take ((segsPath segs).length + 1) (segsPath segs ++ [slash] ++ n) =
      segsPath segs ++ [slash] := by
    rw [List.append_assoc, List.take_append]; simp [List.take_of_length_le]
  simp only [ht]
  exact cleanModel_segs segs [slash] hne hp (Or.inr rfl)

end filepath
end EtcdGrove
end Perennial
