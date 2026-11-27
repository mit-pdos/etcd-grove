/-
Lean-first (no Rocq counterpart).

# k8s-dist K4: a watch's check on the search and on the cluster

`notes/k8s-dist-k4.md`, "Handoff K4-4", step 4. Under `HRel`, a cluster configuration `c` whose
watch check (`watchOkL`) passes makes it pass on the search's `s`, once `s` is at the watch's target
(`targetL`): the events over revisions paired by the renaming are the renamed events
(`eventsInL_ren`, by induction on the two ends), an event's object carries a stored revision
(`eventsInL_stored`), and the events a watch shows are anchored, so the renaming fixes them.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedWatchEv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_dist

open k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item)

section go
variable [GooseExts]

/-! ## `eventsInL` one revision at a time -/

theorem eventsInL_self (x : Input) (hs : List GSt) (lo : Nat) : eventsInL x hs lo lo = [] := by
  simp [eventsInL]

theorem eventsInL_succ (x : Input) (hs : List GSt) (lo n : Nat) (h : lo ≤ n) :
    eventsInL x hs lo (n + 1) = eventsInL x hs lo n ++ (evAtL x hs n).toList := by
  unfold eventsInL
  rw [show n + 1 - lo = (n - lo) + 1 by omega, List.range'_concat, List.filterMap_append]
  congr 1
  rw [show lo + 1 * (n - lo) = n by omega]
  cases hev : evAtL x hs n <;> simp [hev]

/-- A revision whose store has the previous one's items has no event. -/
theorem evAtL_quiet (x : Input) (hs : List GSt) (r : Nat)
    (h : (histN hs r).items = (histN hs (r - 1)).items) : evAtL x hs r = none := by
  unfold evAtL
  split
  · rw [h, changeAtL_self]; rfl
  · rfl

/-! ## The renaming on stored revisions -/

section rel
variable {A : List Nat} {n0 : Nat} {ρ : Nat → Nat} {W : List Nat} {s c : HSt}

/-- The renaming does not lower a stored revision. -/
theorem HRel.ge (h : HRel A n0 ρ W s c) (r : Nat) (hr : StoredRv n0 W r) : r ≤ ρ r := by
  rcases hr with hr | hr
  · exact Nat.le_of_eq (h.ρ_id r hr).symm
  · exact (h.ρ_W r hr).1

/-- The renaming is strictly increasing on stored revisions. -/
theorem HRel.lt_iff (h : HRel A n0 ρ W s c) (r r' : Nat) (hr : StoredRv n0 W r)
    (hr' : StoredRv n0 W r') : r < r' ↔ ρ r < ρ r' := by
  have mono : ∀ a b, StoredRv n0 W a → StoredRv n0 W b → a < b → ρ a < ρ b := by
    intro a b ha hb hab
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [h.ρ_id a ha, h.ρ_id b hb]; exact hab
    · rw [h.ρ_id a ha]; have := (h.ρ_W b hb).1; omega
    · have := (h.W_in a ha).1; omega
    · exact h.ρ_mono a ha b hb hab
  constructor
  · exact mono r r' hr hr'
  · intro hl
    rcases Nat.lt_trichotomy r r' with e | e | e
    · exact e
    · subst e; omega
    · have := mono r' r hr' hr e; omega

theorem HRel.le_iff (h : HRel A n0 ρ W s c) (r r' : Nat) (hr : StoredRv n0 W r)
    (hr' : StoredRv n0 W r') : r ≤ r' ↔ ρ r ≤ ρ r' := by
  have := h.lt_iff r' r hr' hr; omega

/-- A stored revision is renamed to one below `2^64`. -/
theorem HRel.fits (h : HRel A n0 ρ W s c) (r : Nat) (hr : StoredRv n0 W r) : ρ r < 2 ^ 64 := by
  have h1 := (h.stored_cut r hr).2
  have h2 := h.stored_le r hr
  have : uint.nat s.st.rv < 2 ^ 64 := by word
  have : uint.nat c.st.rv < 2 ^ 64 := by word
  omega

/-- A stored revision of the search and its image are paired, and so are the revisions before. -/
theorem HRel.pair_stored (h : HRel A n0 ρ W s c) (r : Nat) (hr : StoredRv n0 W r) (k : Nat) (hk : k ≤ 1) :
    PairW n0 ρ W (r - k) (ρ r - k) := by
  have hge := h.ge r hr
  refine ⟨fun h' => ?_, fun w hw => ?_⟩
  · rcases hr with hr | hr
    · rw [h.ρ_id r hr]
    · have := (h.W_in r hr).1; omega
  · have hw' : StoredRv n0 W w := Or.inr hw
    have := h.lt_iff w r hw' hr
    have := h.le_iff w r hw' hr
    have := (h.W_in w hw).1; have := h.ge w hw'
    have : 0 < n0 ∨ 0 < w := Or.inr (by omega)
    omega

/-- The stores at a stored revision and the one before, on both sides, are renamed. -/
theorem HRel.hist_stored (h : HRel A n0 ρ W s c) (r : Nat) (hr : StoredRv n0 W r) (k : Nat) (hk : k ≤ 1) :
    (histN c.hist (ρ r - k)).items = (histN s.hist (r - k)).items.map (renItem ρ) := by
  have hle := h.stored_le r hr
  have := (h.stored_cut r hr).2
  have : ρ r ≤ uint.nat c.st.rv := by have := h.le; omega
  exact h.hist _ (by omega) _ (by omega) (h.pair_stored r hr k hk)

/-- **The events of a stored revision**, renamed. -/
theorem HRel.evAt_stored (h : HRel A n0 ρ W s c) (hn0 : 1 ≤ n0) (x : Input) (r : Nat)
    (hr : StoredRv n0 W r) : evAtL x c.hist (ρ r) = (evAtL x s.hist r).map (renEv ρ) := by
  by_cases h2 : 2 ≤ r
  · have hle := h.stored_le r hr
    have : uint.nat s.st.rv < 2 ^ 64 := by word
    refine evAtL_ren ρ x s.hist c.hist r (ρ r) h2 (by have := h.ge r hr; omega) (by omega) rfl
      (h.hist_stored r hr 1 (by omega)) (h.hist_stored r hr 0 (by omega)) ?_
    intro p hp q hq he
    have sp := h.stored _ (by omega) p hp
    have sq := h.stored _ (by omega) q hq
    exact renItem_inj ρ p q (h.fits _ sp) (h.fits _ sq) (fun e => h.inj _ _ sp sq e) he
  · have : r ≤ n0 := by omega
    rw [h.ρ_id r this]
    simp [evAtL, h2]

/-- **The events over paired revisions are the renamed events** (`notes/k8s-dist-k4.md`, "Handoff
K4-4", step 4): from `lo`, paired with itself, to `xs` on the search and `yc` on the cluster, paired
over the stored revisions. -/
theorem HRel.eventsIn_ren (h : HRel A n0 ρ W s c) (hn0 : 1 ≤ n0) (x : Input) (lo : Nat)
    (hlo : ∀ r, StoredRv n0 W r → (r < lo ↔ ρ r < lo)) :
    ∀ n xs yc, xs + yc = n → lo ≤ xs → xs ≤ uint.nat s.st.rv + 1 → lo ≤ yc →
      yc ≤ uint.nat c.st.rv + 1 → (∀ r, StoredRv n0 W r → (r < xs ↔ ρ r < yc)) →
      eventsInL x c.hist lo yc = (eventsInL x s.hist lo xs).map (renEv ρ) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro xs yc hn hxs hxs' hyc hyc' hp
  by_cases ha : lo < yc ∧ ∀ r, StoredRv n0 W r → ρ r ≠ yc - 1
  · -- (a) the cluster's last revision is no image: no event there
    obtain ⟨hlt, hno⟩ := ha
    have hgt : n0 < yc - 1 := by
      rcases Nat.lt_or_ge n0 (yc - 1) with e | e
      · exact e
      · exact absurd (h.ρ_id _ e) (hno _ (Or.inl e))
    have hq := h.cquiet (yc - 1) hgt (by omega) (fun w hw => hno w (Or.inr hw))
    rw [show yc = (yc - 1) + 1 by omega, eventsInL_succ x _ lo _ (by omega), evAtL_quiet x _ _ hq,
      Option.toList_none, List.append_nil]
    exact ih (xs + (yc - 1)) (by omega) xs (yc - 1) rfl hxs hxs' (by omega) (by omega)
      (fun r hr => by have := hp r hr; have := hno r hr; omega)
  by_cases hb : lo < xs ∧ ¬ StoredRv n0 W (xs - 1)
  · -- (b) the search's last revision is not stored: no event there
    obtain ⟨hlt, hns⟩ := hb
    have hgt : n0 < xs - 1 := by
      rcases Nat.lt_or_ge n0 (xs - 1) with e | e
      · exact e
      · exact absurd (Or.inl e) hns
    have hq := h.squiet (xs - 1) hgt (by omega) (fun hw => hns (Or.inr hw))
    rw [show xs = (xs - 1) + 1 by omega, eventsInL_succ x _ lo _ (by omega), evAtL_quiet x _ _ hq,
      Option.toList_none, List.append_nil]
    exact ih ((xs - 1) + yc) (by omega) (xs - 1) yc rfl (by omega) (by omega) hyc hyc'
      (fun r hr => by
        have := hp r hr
        have : r ≠ xs - 1 := fun e => hns (e ▸ hr)
        omega)
  -- (c) both last revisions are a stored one and its image, or both ends are `lo`
  by_cases hxl : xs = lo
  · by_cases hyl : yc = lo
    · rw [hxl, hyl, eventsInL_self, eventsInL_self]; rfl
    · exfalso
      have : ∃ r, StoredRv n0 W r ∧ ρ r = yc - 1 := by
        exact Classical.byContradiction fun hne => ha ⟨by omega, fun r hr e => hne ⟨r, hr, e⟩⟩
      obtain ⟨r, hr, he⟩ := this
      have := hp r hr; have := hlo r hr; omega
  · have hst : StoredRv n0 W (xs - 1) :=
      Classical.byContradiction fun hns => hb ⟨by omega, hns⟩
    have := hp (xs - 1) hst
    have hylt : lo < yc := by have := hlo (xs - 1) hst; omega
    obtain ⟨r0, hr0, he⟩ : ∃ r, StoredRv n0 W r ∧ ρ r = yc - 1 := by
      exact Classical.byContradiction fun hne => ha ⟨hylt, fun r hr e => hne ⟨r, hr, e⟩⟩
    have hr0x : r0 = xs - 1 := by
      have h1 := hp r0 hr0
      have h2 := h.lt_iff r0 (xs - 1) hr0 hst
      have h3 := h.lt_iff (xs - 1) r0 hst hr0
      omega
    subst hr0x
    rw [show xs = (xs - 1) + 1 by omega, show yc = (yc - 1) + 1 by omega,
      eventsInL_succ x s.hist lo (xs - 1) (by omega), eventsInL_succ x c.hist lo (yc - 1) (by omega), ← he,
      h.evAt_stored hn0 x _ hst, List.map_append]
    congr 1
    · rw [he]
      exact ih ((xs - 1) + (yc - 1)) (by omega) (xs - 1) (yc - 1) rfl (by omega) (by omega)
        (by omega) (by omega) (fun r hr => by
          have := hp r hr
          have := h.lt_iff r (xs - 1) hr hst
          have := h.inj r (xs - 1) hr hst
          constructor
          · intro hl; have : ρ r ≠ ρ (xs - 1) := fun e => by have := this e; omega
            omega
          · intro hl; omega)
    · cases evAtL x s.hist (xs - 1) <;> rfl

end rel

end go

end k8s_dist
end EtcdGrove
end Perennial
