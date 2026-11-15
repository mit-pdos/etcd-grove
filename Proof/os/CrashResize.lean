/-
What a crash after a truncate landed may leave of a file (I3b of `notes/wal-fsext-plan.md`, the
`tc` change of branch `wal-tc`): with the `OsMeta` the landing leaves when it keeps the candidates
of the bytes it cut off (`rsPostK true`), a crash is one of the crashes of the file as the
truncate's first step announced it (`fileCrashedR_rsPostK`): the bytes cut off, past the new size,
are bounded by their candidates (`tc`, `FileCrashedR`'s last clause) exactly as the token held them
in flight (`rsAnn`). So a crash invariant need only hold of the announced state, across both steps.
Pure. Lean-first. Untrusted.
-/
module

public import GooseLang.Ext.Fs.CrashFiles
public import GooseLang.Ext.Fs.Falloc

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-- **A crash after a truncate landed is a crash of the file as announced.** The landing from `m`
to `tg ≤ m.size` (change `n`, the bytes `xs` cut off, the bytes `ys` below `tg`), keeping the
candidates of the bytes cut off (`rsPostK true`): any crash its `OsMeta` and `ys` allow, the
announced `OsMeta` and `ys ++ rsAnn n xs` allow. -/
theorem fileCrashedR_rsPostK {m : OsMeta} {tg n : Nat} {xs ys : List ByteG} {q : Iris.DFrac}
    {fo : Option OsFile} (htg : tg ≤ m.size) (hxl : xs.length = m.size - tg) (hyl : ys.length = tg)
    (h : FileCrashedR (rsPostK true true m tg tg n xs) [(0, q, ys)] fo) :
    FileCrashedR (m.announce (min m.size tg) (rsHi true m.size tg) tg)
      [(0, q, ys ++ rsAnn n xs)] fo := by
  intro f' hf'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h f' hf'
  have hmin : min m.size tg = tg := Nat.min_eq_right htg
  have hR := le_rsHi true m.size tg
  refine ⟨h1, h2, h3, fun r hr k hk hks => ?_, h5, fun b c hb hc hbs => ?_⟩
  · rw [List.mem_singleton] at hr; subst hr
    simp only [Nat.zero_add] at hks ⊢
    simp only [List.length_append, rsAnn_length] at hk
    by_cases hkt : k < tg
    · have := h4 _ (List.mem_singleton_self _) k (by rw [hyl]; exact hkt) (by simpa using hks)
      simp only [Nat.zero_add] at this
      rw [List.getElem_append_left (by rw [hyl]; exact hkt)]
      exact this
    · have hj : k - tg < xs.length := by omega
      have htc := rsPostK_true_tc (tr := true) (m := m) (tg := tg) (sz' := tg) (n := n)
        (by omega) hxl hj
      rw [hmin, show tg + (k - tg) = k by omega] at htc
      have := h6 k _ (by show tg ≤ k; omega) htc hks
      rw [List.getElem_append_right (by rw [hyl]; omega)]
      simp only [hyl, rsAnn, List.getElem_map]
      exact this
  · -- a byte past the size the announcement knows: the landing knows it the same
    simp only [announce_size] at hb
    have hc' : (rsPostK true true m tg tg n xs).tc !! b = some c := by
      show rsTail true m tg tg n xs !! b = some c
      rw [rsTail_lookup]
      by_cases hin : min m.size tg ≤ b ∧ b < rsHi true m.size tg ∧ tg ≤ b
      · exfalso
        rw [announce_tc, if_pos (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; omega)] at hc
        cases hc
      · rw [if_neg hin]; exact hc
    exact h6 b c (by show tg ≤ b; omega) hc' hbs

end Fs
end Perennial

end
