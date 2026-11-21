/- Coverage of an immutable run list as entries are appended in index order. -/
module
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReplayHistory

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open go_etcd_io.etcd.server.v3.etcdserver

variable [GooseExts]

/-- One entry can extend the last run or start a new one. Both choices preserve
every previously represented entry and make the new index readable. -/
theorem replayAdd_coverage (rs : List replayTermRun) (e : EntryModel)
    (layout : replayLayout rs) (past : ∀ r ∈ rs, uint.nat r.last' < uint.nat e.index) :
    replayLayout (replayAddEntry rs e) ∧
    (∀ i t, replayHasTerm rs i t → replayHasTerm (replayAddEntry rs e) i t) ∧
    replayHasTerm (replayAddEntry rs e) e.index e.term ∧
    (∀ r ∈ replayAddEntry rs e, uint.nat r.last' ≤ uint.nat e.index) := by
  let singleton : replayTermRun := ⟨e.index, e.index, e.term⟩
  have startRun (h : replayAddEntry rs e = rs ++ [singleton]) :
      replayLayout (replayAddEntry rs e) ∧
      (∀ i t, replayHasTerm rs i t → replayHasTerm (replayAddEntry rs e) i t) ∧
      replayHasTerm (replayAddEntry rs e) e.index e.term ∧
      (∀ r ∈ replayAddEntry rs e, uint.nat r.last' ≤ uint.nat e.index) := by
    rw [h]
    refine ⟨⟨?_, List.pairwise_append.mpr ⟨layout.2, by simp, ?_⟩⟩, ?_, ?_, ?_⟩
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact layout.1 r hr
      · obtain rfl := List.mem_singleton.mp hr
        exact Nat.le_refl _
    · intro r hr x hx
      obtain rfl := List.mem_singleton.mp hx
      exact past r hr
    · rintro i t ⟨r, hr, hc⟩
      exact ⟨r, List.mem_append_left _ hr, hc⟩
    · exact ⟨singleton, by simp, Nat.le_refl _, Nat.le_refl _, rfl⟩
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact Nat.le_of_lt (past r hr)
      · obtain rfl := List.mem_singleton.mp hr; exact Nat.le_refl _
  by_cases he : rs = []
  · apply startRun
    simp [he, replayAddEntry, replayJoin, singleton]
  obtain ⟨pre, last, rfl⟩ : ∃ pre last, rs = pre ++ [last] :=
    ⟨rs.dropLast, rs.getLast he, (List.dropLast_concat_getLast he).symm⟩
  by_cases same : last.term' = e.term
  · let ext : replayTermRun := ⟨last.first', e.index, e.term⟩
    have out : replayAddEntry (pre ++ [last]) e = pre ++ [ext] := by
      rw [replayAddEntry, replayJoin_snoc]
      simp only [same, ↓reduceIte]; rfl
    rw [out]
    have hl := layout.1 last (by simp)
    have hlast := past last (by simp)
    obtain ⟨hpre, _, hsep⟩ := List.pairwise_append.mp layout.2
    refine ⟨⟨?_, List.pairwise_append.mpr ⟨hpre, by simp, ?_⟩⟩, ?_, ?_, ?_⟩
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact layout.1 r (List.mem_append_left _ hr)
      · obtain rfl := List.mem_singleton.mp hr
        exact Nat.le_trans hl (Nat.le_of_lt hlast)
    · intro r hr x hx
      obtain rfl := List.mem_singleton.mp hx
      exact hsep r hr last (by simp)
    · rintro i t ⟨r, hr, hc⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, hc⟩
      · obtain rfl := List.mem_singleton.mp hr
        exact ⟨ext, by simp, hc.1, Nat.le_trans hc.2.1 (Nat.le_of_lt hlast), same.symm.trans hc.2.2⟩
    · exact ⟨ext, by simp, Nat.le_trans hl (Nat.le_of_lt hlast), Nat.le_refl _, rfl⟩
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact Nat.le_of_lt (past r (List.mem_append_left _ hr))
      · obtain rfl := List.mem_singleton.mp hr; exact Nat.le_refl _
  · apply startRun
    rw [replayAddEntry, replayJoin_snoc]
    simp only [same, ↓reduceIte]; rfl

/-- A whole batch, including mixed terms, retains previous lookups and adds a lookup
for every physical entry. The bound on the old runs is only needed for incoming entries. -/
theorem replayFold_coverage (rs : List replayTermRun) (es : List EntryModel)
    (layout : replayLayout rs)
    (ordered : es.Pairwise fun a b => uint.nat a.index < uint.nat b.index)
    (past : ∀ r ∈ rs, ∀ e ∈ es, uint.nat r.last' < uint.nat e.index) :
    let out := es.foldl replayAddEntry rs
    replayLayout out ∧ (∀ i t, replayHasTerm rs i t → replayHasTerm out i t) ∧
      ∀ e ∈ es, replayHasTerm out e.index e.term := by
  induction es generalizing rs with
  | nil => exact ⟨layout, fun _ _ h => h, by simp⟩
  | cons e es ih =>
    obtain ⟨later, rest⟩ := List.pairwise_cons.mp ordered
    obtain ⟨layout', keep, here, last⟩ :=
      replayAdd_coverage rs e layout (fun r hr => past r hr e (by simp))
    obtain ⟨done, prior, batch⟩ := ih (replayAddEntry rs e) layout' rest
      (fun r hr x hx => Nat.lt_of_le_of_lt (last r hr) (later x hx))
    refine ⟨done, fun i t h => prior i t (keep i t h), ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact prior _ _ here
    · exact batch _ hx
/-- Replacing a suffix preserves all represented indices below its start, even
when the first replaced entry falls inside an existing run. -/
theorem replayRetain_coverage (rs : List replayTermRun) (k : Nat) (first : w64)
    (layout : replayLayout rs) (cut : replayCutIndex rs first k) :
    let pre := replayRetain rs k first
    replayLayout pre ∧ (∀ r ∈ pre, uint.nat r.last' < uint.nat first) ∧
      ∀ i t, uint.nat i < uint.nat first → replayHasTerm rs i t → replayHasTerm pre i t := by
  obtain ⟨hk, gone, stop⟩ := cut
  have below : ∀ r ∈ rs.take k, uint.nat r.last' < uint.nat first := by
    intro r hr
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hr
    have hjk : j < k := by simpa [Nat.min_eq_left hk] using hj
    have hjr : j < rs.length := by omega
    rw [List.getElem_take] at he
    rcases stop with hzero | ⟨last, hl, lt⟩
    · omega
    have hl' := (List.getElem?_eq_some_iff.mp hl).2
    by_cases h : j = k - 1
    · subst j; rw [← he, hl']; exact lt
    have hsep := layout.2.rel_getElem_of_lt hjr (show k - 1 < rs.length from (List.getElem?_eq_some_iff.mp hl).1) (by omega)
    rw [he, hl'] at hsep
    have hvalid := layout.1 last (List.mem_of_getElem? hl)
    omega
  have hpre := replayLayout_sublist layout (List.take_sublist k rs)
  have keep (i t : w64) (hi : uint.nat i < uint.nat first)
      (h : replayHasTerm rs i t) :
      replayHasTerm (rs.take k) i t ∨ ∃ r, rs[k]? = some r ∧ replayContains r i t := by
    obtain ⟨r, hr, hc⟩ := h
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hr
    by_cases hlt : j < k
    · left; refine ⟨r, ?_, hc⟩
      apply List.mem_of_getElem? (i := j)
      simp [List.getElem?_take, hlt, List.getElem?_eq_getElem hj, he]
    · by_cases heq : k = j
      · right; subst j; exact ⟨r, (List.getElem?_eq_getElem hj).trans (congrArg some he), hc⟩
      have hks : k < rs.length := by omega
      have hgone := gone k rs[k] (Nat.le_refl _) (List.getElem?_eq_getElem hks)
      have hsep := layout.2.rel_getElem_of_lt hks hj (by omega)
      rw [he] at hsep
      have hfirst := hc.1
      omega
  unfold replayRetain
  cases hx : rs[k]? with
  | none =>
    refine ⟨hpre, below, ?_⟩
    intro i t hi h
    rcases keep i t hi h with h | ⟨r, hr, _⟩
    · exact h
    · rw [hx] at hr; contradiction
  | some x =>
    by_cases hb : uint.nat x.first' < uint.nat first
    · simp only [hb, ↓reduceIte]
      let clip : replayTermRun := { x with last' := first - W64 1 }
      have pred : uint.nat (first - W64 1) + 1 = uint.nat first := by word
      have hclip : uint.nat clip.last' < uint.nat first := by
        change uint.nat (first - W64 1) < uint.nat first
        omega
      refine ⟨⟨?_, List.pairwise_append.mpr ⟨hpre.2, by simp, ?_⟩⟩, ?_, ?_⟩
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hpre.1 _ hr
        · obtain rfl := List.mem_singleton.mp hr
          change uint.nat x.first' ≤ uint.nat (first - W64 1)
          omega
      · intro r hr y hy
        obtain rfl := List.mem_singleton.mp hy
        obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hr
        have hjk : j < k := by simpa [Nat.min_eq_left hk] using hj
        rw [List.getElem_take] at he
        obtain ⟨hkr, heq⟩ := List.getElem?_eq_some_iff.mp hx
        have hsep := layout.2.rel_getElem_of_lt (Nat.lt_trans hjk hkr) hkr hjk
        rwa [he, heq] at hsep
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact below r hr
        · obtain rfl := List.mem_singleton.mp hr; exact hclip
      · intro i t hi h
        rcases keep i t hi h with ⟨r, hr, hc⟩ | ⟨r, hr, hc⟩
        · exact ⟨r, List.mem_append_left _ hr, hc⟩
        · rw [hx] at hr; cases hr
          refine ⟨clip, by simp [clip], hc.1, ?_, hc.2.2⟩
          change uint.nat i ≤ uint.nat (first - W64 1)
          omega
    · simp only [hb, ↓reduceIte]
      refine ⟨hpre, below, ?_⟩
      intro i t hi h
      rcases keep i t hi h with h | ⟨r, hr, hc⟩
      · exact h
      · rw [hx] at hr; cases hr; have := hc.1; omega

end EtcdGrove
end Perennial
