/-
**Lemmas over the WAL's history and its reader** (WAL W4b, 2026-11-12; `/shared/tmp/wal-spec/w4b/plan.md`
§2 A, approved by etcd-grove-81). Proved; no trusted text. For the tester's proof (W4c), rung 2's crash
clause (C3) and the server's restart (S2/C6).
DRAFT (unchecked): starting point for Part A.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalDisk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

/-! ## A1. The image algebra -/

section img
variable {E : Type}

theorem getElem?_some_lt {α : Type} {l : List α} {j : Nat} {x : α} (h : l[j]? = some x) :
    j < l.length := by
  rcases Nat.lt_or_ge j l.length with hl | hl
  · exact hl
  · rw [List.getElem?_eq_none hl] at h; cases h

/-- The whole history is an image of itself at any mark up to its length. -/
theorem walImg_refl {H : List (WalOpG E)} {n : Nat} (h : n ≤ H.length) : walImg H n H :=
  ⟨H.length, h, Nat.le_refl _, Or.inl (List.take_length).symm⟩

/-- A higher mark allows fewer images. -/
theorem walImg_mono {H I : List (WalOpG E)} {n n' : Nat} (hn : n ≤ n') (hI : walImg H n' I) :
    walImg H n I := by
  obtain ⟨j, h1, h2, h3⟩ := hI
  exact ⟨j, Nat.le_trans hn h1, h2, h3⟩

/-- An image is no longer than the history. -/
theorem walImg_length_le {H I : List (WalOpG E)} {n : Nat} (hI : walImg H n I) :
    I.length ≤ H.length := by
  obtain ⟨j, -, h2, h3 | ⟨h, es, k, hj, -, h3⟩⟩ := hI
  · subst h3; simp; omega
  · have := getElem?_some_lt hj
    subst h3; simp; omega

/-- An image of `H` is an image of `H` with one more operation (the operation not yet written). -/
theorem walImg_snoc {H I : List (WalOpG E)} {n : Nat} (o : WalOpG E) (hI : walImg H n I) :
    walImg (H ++ [o]) n I := by
  obtain ⟨j, h1, h2, h3 | ⟨h, es, k, hj, hk, h3⟩⟩ := hI
  · refine ⟨j, h1, by simp; omega, Or.inl ?_⟩
    rw [h3, List.take_append_of_le_length h2]
  · have hjl := getElem?_some_lt hj
    refine ⟨j, h1, by simp; omega, Or.inr ⟨h, es, k, ?_, hk, ?_⟩⟩
    · rw [List.getElem?_append_left hjl]; exact hj
    · rw [h3, List.take_append_of_le_length h2]

/-- **The graceful instance**: with every operation synced, the only image is the history. -/
theorem walImg_full {H I : List (WalOpG E)} : walImg H H.length I ↔ I = H := by
  constructor
  · rintro ⟨j, h1, h2, h3 | ⟨h, es, k, hj, -, -⟩⟩
    · have : j = H.length := by omega
      subst this; simpa using h3
    · have := getElem?_some_lt hj; omega
  · rintro rfl; exact walImg_refl (Nat.le_refl _)

/-- An image keeps the synced prefix. -/
theorem walImg_prefix {H I : List (WalOpG E)} {n : Nat} (hI : walImg H n I) :
    n ≤ I.length ∧ I.take n = H.take n := by
  obtain ⟨j, h1, h2, h3 | ⟨h, es, k, hj, -, h3⟩⟩ := hI
  · subst h3
    refine ⟨by simp; omega, ?_⟩
    rw [List.take_take, Nat.min_eq_left h1]
  · subst h3
    have hl : (H.take j).length = j := by simp; omega
    refine ⟨by simp; omega, ?_⟩
    rw [List.take_append_of_le_length (by omega), List.take_take, Nat.min_eq_left h1]

/-- **An image of an image is an image** (a kill, a restart, then a power loss: `walCrash`'s
docstring). -/
theorem walImg_trans {H I I' : List (WalOpG E)} {n : Nat} (hI : walImg H n I) (hI' : walImg I n I') :
    walImg H n I' := by
  obtain ⟨j, h1, h2, h3 | ⟨h, es, k, hj, hk, h3⟩⟩ := hI
  · subst h3
    obtain ⟨j', h1', h2', h3' | ⟨h', es', k', hj', hk', h3'⟩⟩ := hI'
    · have hj'j : j' ≤ j := by simp at h2'; omega
      refine ⟨j', h1', by omega, Or.inl ?_⟩
      rw [h3', List.take_take, Nat.min_eq_left hj'j]
    · have hlt := getElem?_some_lt hj'
      have hj'j : j' < j := by simp at hlt; omega
      refine ⟨j', h1', by omega, Or.inr ⟨h', es', k', ?_, hk', ?_⟩⟩
      · rw [List.getElem?_take_of_lt hj'j] at hj'; exact hj'
      · rw [h3', List.take_take, Nat.min_eq_left (Nat.le_of_lt hj'j)]
  · subst h3
    have hjl := getElem?_some_lt hj
    have hl : (H.take j).length = j := by simp; omega
    obtain ⟨j', h1', h2', h3' | ⟨h', es', k', hj', hk', h3'⟩⟩ := hI'
    · simp only [List.length_append, List.length_cons, List.length_nil, hl] at h2'
      rcases Nat.lt_or_ge j' (j + 1) with hlt | hge
      · refine ⟨j', h1', by omega, Or.inl ?_⟩
        rw [h3', List.take_append_of_le_length (by omega), List.take_take,
          Nat.min_eq_left (by omega)]
      · have : j' = j + 1 := by omega
        subst this
        refine ⟨j, h1, h2, Or.inr ⟨h, es, k, hj, hk, ?_⟩⟩
        rw [h3', List.take_of_length_le (by simp [hl])]
    · have hlt := getElem?_some_lt hj'
      simp only [List.length_append, List.length_cons, List.length_nil, hl] at hlt
      rcases Nat.lt_or_ge j' j with hj'j | hge
      · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hj'j] at hj'
        refine ⟨j', h1', by omega, Or.inr ⟨h', es', k', hj', hk', ?_⟩⟩
        rw [h3', List.take_append_of_le_length (by omega), List.take_take,
          Nat.min_eq_left (by omega)]
      · have : j' = j := by omega
        subst this
        rw [List.getElem?_append_right (by omega), hl, Nat.sub_self] at hj'
        simp only [List.getElem?_cons_zero, Option.some.injEq, WalOpG.save.injEq] at hj'
        obtain ⟨-, rfl⟩ := hj'
        refine ⟨j', h1, h2, Or.inr ⟨h, es, min k' k, hj, by omega, ?_⟩⟩
        rw [h3', List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
          List.take_take]
end img

/-! ## A2. The read's hard state -/

section reader
variable [GooseExts]

theorem walReadCut_hs {I : WalHist} {k : Nat} {σ : StorContents}
    (h : walReadCut I k = some σ) : σ.hs = walLastHS I := by
  sorry -- A2

/-- A3. -/
theorem walReadCut_base {I : WalHist} {k : Nat} {σ : StorContents} {s : w64 × w64}
    (h : walReadCut I k = some σ) (hs : some s = walNewestPair (walValidSnaps I k)) :
    σ.base = entryID.mk s.2 s.1 := by
  sorry -- A3

/-- A4 (restart S3's `walRead_wf`). -/
theorem walReadCut_wf {I : WalHist} {k : Nat} {σ : StorContents}
    (h : walReadCut I k = some σ) :
    ∀ (j : Nat) (e : EntryM), σ.ents[j]? = some e → uint.nat e.Index' = σ.b + 1 + j := by
  sorry -- A4

end reader

end EtcdGrove
end Perennial
