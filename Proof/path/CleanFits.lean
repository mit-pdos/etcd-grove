/-
**`Clean` keeps a path that fits** (wal-fsfix2, 2026-11-20): `Clean(p)` of a non-empty `p` is no
longer than `p`, and has no component longer than `p`'s longest (`Fs.WinOk`: every 256-byte infix
holds a `/`, i.e. no run of 256 bytes without one). So `Join` of elements that fit gives a path that
fits (`config.snapDirOf`, `Proof/go_etcd_io/etcd/server/v3/config/Defs.lean`). Lean-first; pure, over
the model of `Proof/path/Model.lean`.

The loop invariant (`CleanInv`): the output `o` has the window property and is no longer than the
input read so far (`r`); a rooted output starts with `/` and `dotdot ≥ 1`; and before an element that
gets a separator (the output not empty, nor the root), the output is shorter than `r` (the input's
`/` before that element pays for it).
-/
module

public import Proof.path.Model
public import GooseLang.Ext.Fs.PathFitsLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace path

theorem slash_eq_slashB : slash = slashB := rfl

/-- A byte read as `/` is in range. -/
theorem getD_slash_lt {p : List w8} {i : Nat} (h : p.getD i 0 = slash) : i < p.length := by
  refine Classical.byContradiction fun hn => ?_
  have h0 : p[i]? = none := List.getElem?_eq_none (by omega)
  simp only [List.getD_eq_getElem?_getD, h0, Option.getD_none] at h
  exact absurd h (by decide)

/-- **The copy of an element**: the bytes from `r` up to the next `/` (or the end). -/
theorem copyElem_shape (p : List w8) (r : Nat) (o : List w8) (hr : r ≤ p.length) :
    ∃ k, copyElem p r o = (r + k, o ++ (p.drop r).take k) ∧ r + k ≤ p.length ∧
      (∀ c ∈ (p.drop r).take k, c ≠ slash) ∧ (r + k = p.length ∨ p.getD (r + k) 0 = slash) := by
  generalize hn : p.length - r = n
  induction n generalizing r o with
  | zero =>
    refine ⟨0, ?_, by omega, by simp, Or.inl (by omega)⟩
    rw [copyElem_stop p r o (by omega)]; simp
  | succ n ih =>
    by_cases hc : r < p.length ∧ p.getD r 0 ≠ slash
    · obtain ⟨k, hk, hkl, hks, hke⟩ := ih (r + 1) (o ++ [p.getD r 0]) (by omega) (by omega)
      have hd : p.drop r = p.getD r 0 :: p.drop (r + 1) := by
        have hg : p.getD r 0 = p[r] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc.1, Option.getD_some]
        rw [hg, List.drop_eq_getElem_cons hc.1]
      refine ⟨k + 1, ?_, by omega, ?_, by rw [show r + (k + 1) = r + 1 + k by omega]; exact hke⟩
      · rw [copyElem_step p r o hc.1 hc.2, hk, hd]
        simp [show r + 1 + k = r + (k + 1) by omega]
      · rw [hd]
        intro c hcm
        simp only [List.take_succ_cons, List.mem_cons] at hcm
        rcases hcm with rfl | hcm
        · exact hc.2
        · exact hks c hcm
    · refine ⟨0, ?_, by omega, by simp, ?_⟩
      · rw [copyElem_stop p r o hc]; simp
      · by_cases hl : r < p.length
        · exact Or.inr (by simpa using (not_and.1 hc) hl)
        · exact Or.inl (by omega)

/-- A run of the input without `/` is at most 255 bytes when the input has the window property. -/
theorem run_le {p s : List w8} (hp : Fs.WinOk p) (hs : s <:+: p) (hns : ∀ c ∈ s, c ≠ slash) :
    s.length ≤ 255 := by
  refine Classical.byContradiction fun hl => ?_
  have h1 : s.take 256 <:+: p := (List.take_prefix _ _).isInfix.trans hs
  have h2 := hp _ h1 (by simp; omega)
  exact hns _ (List.mem_of_mem_take h2) rfl

theorem winOk_prefix {l o : List w8} (ho : Fs.WinOk o) (h : l <+: o) : Fs.WinOk l :=
  fun q hq hl => ho q (hq.trans h.isInfix) hl

/-- The invariant of `Clean`'s loop (see the file header). -/
def CleanInv (p : List w8) (rooted : Bool) (r : Nat) (o : List w8) (dd : Nat) : Prop :=
  Fs.WinOk o ∧ o.length ≤ r ∧ r ≤ p.length ∧ (rooted = true → o.head? = some slash ∧ 1 ≤ dd) ∧
    (r < p.length → p.getD r 0 ≠ slash →
      ((rooted ∧ o.length ≠ 1) ∨ (!rooted ∧ o.length ≠ 0)) → o.length < r)

theorem cleanInv_step (p : List w8) (rooted : Bool) (r : Nat) (o : List w8) (dd : Nat)
    (hp : Fs.WinOk p) (hI : CleanInv p rooted r o dd) (hr : r < p.length) :
    CleanInv p rooted (cleanStep p rooted r o dd).1 (cleanStep p rooted r o dd).2.1
      (cleanStep p rooted r o dd).2.2 := by
  obtain ⟨hw, hl, hrl, hh, hs⟩ := hI
  unfold cleanStep
  split
  · -- `/`
    dsimp only
    exact ⟨hw, by omega, by omega, hh, fun _ _ _ => by omega⟩
  split
  · -- `.`
    next h1 h2 =>
    dsimp only
    refine ⟨hw, by omega, by omega, hh, fun h3 h4 _ => ?_⟩
    rcases h2.2 with h | h
    · omega
    · exact absurd h h4
  split
  · next h1 h2 h3 =>
    have hr2 : r + 2 ≤ p.length := by
      rcases h3.2.2 with h | h
      · omega
      · have := getD_slash_lt h; omega
    have hv : ∀ o' : List w8, r + 2 < p.length → p.getD (r + 2) 0 ≠ slash →
        ((rooted ∧ o'.length ≠ 1) ∨ (!rooted ∧ o'.length ≠ 0)) → o'.length < r + 2 := by
      intro o' h4 h5 _
      rcases h3.2.2 with h | h
      · omega
      · exact absurd h h5
    split
    · -- `..` backtracking
      next hdd =>
      dsimp only
      have hb := backW_bounds o dd (o.length - 1) (by omega)
      refine ⟨winOk_prefix hw (List.take_prefix _ _), ?_, hr2, ?_, hv _⟩
      · have := List.length_take_le (backW o dd (o.length - 1)) o; omega
      · intro hro
        obtain ⟨hh1, hh2⟩ := hh hro
        refine ⟨?_, hh2⟩
        rw [List.head?_take, if_neg (by omega), hh1]
    split
    · -- `..` kept (not rooted)
      next hdd hro =>
      dsimp only
      have hrf : rooted = false := by simpa using hro
      refine ⟨?_, ?_, hr2, fun h => by simp [hrf] at h, hv _⟩
      · split
        · have := Fs.winOk_child (b := [dot, dot]) hw (by simp)
          simpa [Fs.child, slashB] using this
        · next h0 => exact Fs.winOk_short (by simp; omega)
      · split
        · next h0 =>
          have := hs hr (by rw [h3.1]; decide) (Or.inr ⟨by simp [hrf], by omega⟩)
          simp; omega
        · simp; omega
    · -- `..` at the root
      dsimp only
      exact ⟨hw, by omega, hr2, hh, hv _⟩
  · -- an element
    next h1 h2 h3 =>
    obtain ⟨k, hk, hkl, hks, hke⟩ := copyElem_shape p r
      (if (rooted ∧ o.length ≠ 1) ∨ (!rooted ∧ o.length ≠ 0) then o ++ [slash] else o) hrl
    have hrun : ((p.drop r).take k).length ≤ 255 :=
      run_le hp ((List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix) hks
    have hkk : ((p.drop r).take k).length = k := by simp; omega
    simp only [hk]
    refine ⟨?_, ?_, hkl, ?_, fun h4 h5 _ => ?_⟩
    · split
      · have := Fs.winOk_child hw hrun
        simpa [Fs.child, slashB] using this
      · next hc =>
        cases hro : rooted
        · have : o.length = 0 := by
            refine Classical.byContradiction fun h => hc (Or.inr ⟨by simp [hro], h⟩)
          rw [List.length_eq_zero_iff.1 this]
          exact Fs.winOk_short (by simp only [List.nil_append]; omega)
        · have h1' : o.length = 1 := by
            refine Classical.byContradiction fun h => hc (Or.inl ⟨by simp [hro], h⟩)
          have hhd := (hh hro).1
          obtain ⟨x, rfl⟩ : ∃ x, o = [x] := List.length_eq_one_iff.1 h1'
          simp at hhd
          subst hhd
          have := Fs.winOk_child (a := []) (Fs.winOk_short (by simp)) hrun
          simpa [Fs.child, slashB] using this
    · split
      · next hc =>
        have := hs hr h1 hc
        simp; omega
      · simp; omega
    · intro hro
      obtain ⟨hh1, hh2⟩ := hh hro
      refine ⟨?_, hh2⟩
      have hne : o ≠ [] := by intro h; simp [h] at hh1
      split <;> simp [List.head?_append, hh1]
    · rcases hke with h | h
      · omega
      · exact absurd h h5

/-- **`Clean`'s loop keeps the invariant to its end.** -/
theorem cleanLoop_inv (p : List w8) (rooted : Bool) (hp : Fs.WinOk p) :
    ∀ (n r : Nat) (o : List w8) (dd : Nat), p.length - r = n → CleanInv p rooted r o dd →
      Fs.WinOk (cleanLoop p rooted r o dd) ∧ (cleanLoop p rooted r o dd).length ≤ p.length := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro r o dd hn hI
    by_cases hr : r < p.length
    · rw [cleanLoop_step _ _ _ _ _ hr]
      have hgt := cleanStep_fst_gt p rooted r o dd hr
      have hI' := cleanInv_step p rooted r o dd hp hI hr
      exact ih _ (by omega) _ _ _ rfl hI'
    · rw [cleanLoop_stop _ _ _ _ _ hr]
      exact ⟨hI.1, by have := hI.2.1; have := hI.2.2.1; omega⟩

/-- **`Clean` of a non-empty path that fits**: no longer, and with the window property. -/
theorem cleanModel_fits (p : List w8) (hne : p ≠ []) (hp : Fs.WinOk p) :
    Fs.WinOk (cleanModel p) ∧ (cleanModel p).length ≤ p.length := by
  have hlen : 1 ≤ p.length := by
    cases p with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  unfold cleanModel
  rw [if_neg hne]
  dsimp only
  generalize decide (p.getD 0 0 = slash) = b
  have hI : CleanInv p b (if b = true then 1 else 0) (if b = true then [slash] else [])
      (if b = true then 1 else 0) := by
    cases b <;> exact ⟨Fs.winOk_short (by simp), by simp, by simp; try omega, by simp, by simp⟩
  obtain ⟨hw, hl⟩ := cleanLoop_inv p b hp _ _ _ _ rfl hI
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hw hl ⊢ <;> split <;>
    first | exact ⟨hw, hl⟩ | exact ⟨Fs.winOk_short (by decide), by simpa using hlen⟩

end path
end EtcdGrove
end Perennial
