/-
`TcKnows` (I3b, `wal-tc10`): what the candidates known past the size after a truncate (`rsTail`, the
outcome's `tc` when the update's owner keeps them, `rsPostK true`/`rsUnMeta true`) know at least, as a
fact on the `tc` a caller of `os.File.Truncate.specAu` holds up to (`os.ftDoneH`, `os.ftUndoneH`): the
caller then knows which bytes past the size have known candidates without knowing them (the WAL's
`TailZ` after `cut`'s truncate). Pure; untrusted. With the laws the retry loop of
`os.File.Truncate.wp_proofAu` carries it by (an attempt from a state an earlier attempt left).
-/
module

public import LinuxFs.Proof.os.Base
public import LinuxFs.Proof.os.ResizeAu

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-- **`tc` knows every byte a truncate of `m` to `tg` that left the size `sz'` keeps known**
(`rsTail true m tg sz'`'s domain: the bytes the announcement leaves known, and the bytes in
`[min size tg, rsHi true size tg)` at or past `sz'` that are below the old size or known to `m.pc`).
The truncate landed: `sz' = tg`; not landed: `sz' = m.size`. Monotone in `tc`'s domain. -/
def TcKnows (m : OsMeta) (tg sz' : Nat) (tc : GMap Nat Cands) : Prop :=
  ∀ b, (rsTail true m tg sz' 0 [] !! b).isSome → (tc !! b).isSome

/-- `rsTail`'s domain does not depend on the stamp or the bytes cut off. -/
theorem rsTail_isSome (tr : Bool) (m : OsMeta) (tg sz' n n' : Nat) (xs xs' : List ByteG) (b : Nat) :
    (rsTail tr m tg sz' n xs !! b).isSome = (rsTail tr m tg sz' n' xs' !! b).isSome := by
  rw [rsTail_lookup, rsTail_lookup]
  split
  · split
    · rfl
    · cases m.pc b <;> rfl
  · rfl

/-- **The supply's fact**: `rsTail` knows what it knows. -/
theorem TcKnows.rsTail (m : OsMeta) (tg sz' n : Nat) (xs : List ByteG) :
    TcKnows m tg sz' (Fs.rsTail true m tg sz' n xs) := by
  intro b hb
  rw [rsTail_isSome true m tg sz' n 0 xs []]
  exact hb

theorem TcKnows.mono {m : OsMeta} {tg sz' : Nat} {tc tc' : GMap Nat Cands} (h : TcKnows m tg sz' tc)
    (h' : ∀ b, (tc !! b).isSome → (tc' !! b).isSome) : TcKnows m tg sz' tc' :=
  fun b hb => h' b (h b hb)

/-- What `rsTail`'s domain is, unfolded. -/
theorem rsTail_isSome_iff (m : OsMeta) (tg sz' : Nat) (b : Nat) :
    (rsTail true m tg sz' 0 [] !! b).isSome ↔
      ((min m.size tg ≤ b ∧ b < rsHi true m.size tg ∧ sz' ≤ b) ∧ (b < m.size ∨ (m.pc b).isSome)) ∨
      (¬ (min m.size tg ≤ b ∧ b < rsHi true m.size tg ∧ sz' ≤ b) ∧ inRange (min m.size tg)
        (rsHi true m.size tg) b = false ∧ (m.tc !! b).isSome) := by
  rw [rsTail_lookup]
  by_cases h1 : min m.size tg ≤ b ∧ b < rsHi true m.size tg ∧ sz' ≤ b
  · rw [if_pos h1]
    by_cases h2 : b < m.size
    · rw [if_pos h2]; simp [h1, h2]
    · rw [if_neg h2]; cases m.pc b <;> simp [h1, h2]
  · rw [if_neg h1, announce_tc]
    by_cases h3 : inRange (min m.size tg) (rsHi true m.size tg) b = true
    · rw [if_pos h3]; simp [h1, h3]
    · rw [if_neg h3]; simp [h1, h3]

/-- **An attempt from a state an earlier attempt left not landed** (the announcement, knowing
`tc0 ⊇` what the not-landed outcome keeps known): what it keeps known, the first state's outcome
keeps too. -/
theorem TcKnows.of_announce {m : OsMeta} {tg sz' : Nat} {tc0 tc : GMap Nat Cands} {rz0 : List Nat}
    (h0 : TcKnows m tg m.size tc0)
    (h : TcKnows ((m.announce (min m.size tg) (rsHi true m.size tg) tg).withTc tc0 rz0) tg sz' tc) :
    TcKnows m tg sz' tc := by
  intro b hb
  apply h b
  rw [rsTail_isSome_iff] at hb ⊢
  simp only [OsMeta.withTc_size, announce_size]
  rcases hb with ⟨hr, hb | hb⟩ | ⟨hr, hin, hb⟩
  · exact .inl ⟨hr, .inl hb⟩
  · by_cases hlt : b < m.size
    · exact .inl ⟨hr, .inl hlt⟩
    refine .inl ⟨hr, .inr ?_⟩
    have hk := h0 b (by
      rw [rsTail_isSome_iff]
      exact .inl ⟨⟨hr.1, hr.2.1, by omega⟩, .inr hb⟩)
    unfold OsMeta.pc
    simp only [OsMeta.withTc_tc]
    cases hc : tc0 !! b with
    | none => rw [hc] at hk; cases hk
    | some c => rfl
  · refine .inr ⟨hr, hin, ?_⟩
    simp only [OsMeta.withTc_tc]
    exact h0 b (by rw [rsTail_isSome_iff]; exact .inr ⟨fun h' => by
      simp only [inRange, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hin
      omega, hin, hb⟩)

/-- **An attempt from a state an earlier attempt left landed** (`rsPost true m tg tg`, knowing `tc0 ⊇`
what the landed outcome keeps known): what it keeps known (landed or not: its size is `tg`), the first
state's landed outcome keeps too. -/
theorem TcKnows.of_rsPost {m : OsMeta} {tg : Nat} {tc0 tc : GMap Nat Cands} {rz0 : List Nat}
    (h0 : TcKnows m tg tg tc0)
    (h : TcKnows ((rsPost true m tg tg).withTc tc0 rz0) tg tg tc) :
    TcKnows m tg tg tc := by
  intro b hb
  apply h b
  have hk := h0 b hb
  have hhi := rsHi_same_le true m.size tg
  rw [rsTail_isSome_iff] at hb ⊢
  simp only [OsMeta.withTc_size, Perennial.os.rsPost_size', Nat.min_self]
  have hpc : (((rsPost true m tg tg).withTc tc0 rz0).pc b).isSome := by
    unfold OsMeta.pc
    simp only [OsMeta.withTc_tc]
    cases hc : tc0 !! b with
    | none => rw [hc] at hk; cases hk
    | some c => rfl
  have hout : ¬ (tg ≤ b ∧ b < rsHi true tg tg) →
      (¬ (tg ≤ b ∧ b < rsHi true tg tg ∧ tg ≤ b) ∧ inRange tg (rsHi true tg tg) b = false ∧
        (((rsPost true m tg tg).withTc tc0 rz0).tc !! b).isSome) := fun hn => by
    refine ⟨fun h' => hn ⟨h'.1, h'.2.1⟩, ?_, by simpa using hk⟩
    simp only [inRange, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
  rcases hb with ⟨hr, -⟩ | ⟨hr, hin, -⟩
  · by_cases hb1 : b < rsHi true tg tg
    · exact .inl ⟨⟨hr.2.2, hb1, hr.2.2⟩, .inr hpc⟩
    · exact .inr (hout (fun h' => hb1 h'.2))
  · refine .inr (hout fun h' => ?_)
    simp only [inRange, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hin
    omega

end Fs
end Perennial

end
