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

/-! ## The objects of a change and of an event -/

theorem changeAtL_objs : ∀ (P Q : List item) (r : Nat) (ch : Chg), changeAtL P Q r = some ch →
    (∀ o, ch.prev = some o → ∃ it ∈ P, it.obj' = o) ∧ (∀ o, ch.cur = some o → ∃ it ∈ Q, it.obj' = o)
  | [], [], _, _, h => by simp [changeAtL] at h
  | p :: _, [], _, _, h => by
    simp only [changeAtL, Option.some.injEq] at h; subst h
    exact ⟨fun o e => ⟨p, List.mem_cons_self, by simpa using e⟩, fun o e => by simp at e⟩
  | [], q :: _, _, _, h => by
    simp only [changeAtL, Option.some.injEq] at h; subst h
    exact ⟨fun o e => by simp at e, fun o e => ⟨q, List.mem_cons_self, by simpa using e⟩⟩
  | p :: ps, q :: qs, r, ch, h => by
    simp only [changeAtL] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      exact ⟨fun o e => ⟨p, List.mem_cons_self, by simpa using e⟩, fun o e => by simp at e⟩
    split at h
    · simp only [Option.some.injEq] at h; subst h
      exact ⟨fun o e => by simp at e, fun o e => ⟨q, List.mem_cons_self, by simpa using e⟩⟩
    split at h
    · obtain ⟨h1, h2⟩ := changeAtL_objs ps qs r ch h
      exact ⟨fun o e => let ⟨it, hi, he⟩ := h1 o e; ⟨it, List.mem_cons_of_mem _ hi, he⟩,
        fun o e => let ⟨it, hi, he⟩ := h2 o e; ⟨it, List.mem_cons_of_mem _ hi, he⟩⟩
    · simp only [Option.some.injEq] at h; subst h
      exact ⟨fun o e => ⟨p, List.mem_cons_self, by simpa using e⟩,
        fun o e => ⟨q, List.mem_cons_self, by simpa using e⟩⟩

/-- **An event's object** is one of the two stores' objects, or a deleted object at the revision. -/
theorem evAtL_obj (x : Input) (hs : List GSt) (r : Nat) (e : WEv) (he : evAtL x hs r = some e) :
    (∃ it ∈ (histN hs (r - 1)).items ++ (histN hs r).items, it.obj' = e.o) ∨
      e.o.ResourceVersion' = W64 (r : Int) := by
  unfold evAtL at he
  split at he
  · rcases hc : changeAtL (histN hs (r - 1)).items (histN hs r).items r with _ | ch
    · rw [hc] at he; cases he
    · rw [hc] at he
      have hrv := changeAtL_rv' _ _ _ _ hc
      obtain ⟨hp, hq⟩ := changeAtL_objs _ _ _ _ hc
      simp only [Option.bind_some] at he
      split at he
      · unfold toEventL at he
        dsimp only at he
        split at he
        · rcases hcur : ch.cur with _ | o
          · rw [hcur] at he; cases he
          · rw [hcur] at he; simp only [Option.map_some, Option.some.injEq] at he; subst he
            obtain ⟨it, hi, hio⟩ := hq o hcur
            exact Or.inl ⟨it, List.mem_append_right _ hi, hio⟩
        split at he
        · rcases hcur : ch.cur with _ | o
          · rw [hcur] at he; cases he
          · rw [hcur] at he; simp only [Option.map_some, Option.some.injEq] at he; subst he
            obtain ⟨it, hi, hio⟩ := hq o hcur
            exact Or.inl ⟨it, List.mem_append_right _ hi, hio⟩
        split at he
        · rcases hprev : ch.prev with _ | o
          · rw [hprev] at he; cases he
          · rw [hprev] at he; simp only [Option.map_some, Option.some.injEq] at he; subst he
            right; simp [hrv]
        · cases he
      · cases he
  · cases he

/-- **Renamed events with anchored revisions are the events.** -/
theorem map_renEv_fix (A : List Nat) (ρ : Nat → Nat) :
    ∀ (L M : List WEv), (∀ e ∈ L, CutW A ρ (uint.nat e.o.ResourceVersion') ∧
        ρ (uint.nat e.o.ResourceVersion') < 2 ^ 64) →
      (∀ e ∈ M, uint.nat e.o.ResourceVersion' ∈ A) →
      (L.map (renEv ρ)).map (fun e => (e.t, e.o)) = M.map (fun e => (e.t, e.o)) →
      L.map (fun e => (e.t, e.o)) = M.map (fun e => (e.t, e.o))
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | e :: L, f :: M, hL, hM, h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨⟨ht, ho⟩, hr⟩ := h
    obtain ⟨hc, hf⟩ := hL e List.mem_cons_self
    have hfix : renObj ρ e.o = e.o := renObj_fix e.o hc hf (by
      have : renEv ρ e = ⟨e.t, renObj ρ e.o⟩ := rfl
      rw [this] at ho; simp only at ho; rw [ho]; exact hM f List.mem_cons_self)
    have : renEv ρ e = e := by
      show (⟨e.t, renObj ρ e.o⟩ : WEv) = e; rw [hfix]
    rw [this] at ht ho
    exact ⟨⟨ht, ho⟩, map_renEv_fix A ρ L M (fun e' he' => hL e' (List.mem_cons_of_mem _ he'))
      (fun f' hf' => hM f' (List.mem_cons_of_mem _ hf')) hr⟩

theorem evsEqL_ren (A : List Nat) (ρ : Nat → Nat) (L M : List WEv)
    (hL : ∀ e ∈ L, CutW A ρ (uint.nat e.o.ResourceVersion') ∧ ρ (uint.nat e.o.ResourceVersion') < 2 ^ 64)
    (hM : ∀ e ∈ M, uint.nat e.o.ResourceVersion' ∈ A) (h : evsEqL (L.map (renEv ρ)) M = true) :
    evsEqL L M = true := by
  unfold evsEqL at h ⊢
  exact decide_eq_true (map_renEv_fix A ρ L M hL hM (of_decide_eq_true h))

/-- A revision is an anchor or the one after. -/
def AnchorIsh (A : List Nat) (u : Nat) : Prop := ∃ v ∈ A, u = v ∨ u = v + 1

section rel2
variable {A : List Nat} {n0 : Nat} {ρ : Nat → Nat} {W : List Nat} {s c : HSt}

/-- **An event's object on the search carries a stored revision.** -/
theorem HRel.eventsIn_stored (h : HRel A n0 ρ W s c) (x : Input) (lo xs : Nat)
    (hxs : xs ≤ uint.nat s.st.rv + 1) (e : WEv) (he : e ∈ eventsInL x s.hist lo xs) :
    StoredRv n0 W (uint.nat e.o.ResourceVersion') := by
  unfold eventsInL at he
  obtain ⟨r, hr, hre⟩ := List.mem_filterMap.mp he
  have hr' := List.mem_range'_1.mp hr
  have hst : StoredRv n0 W r := by
    rcases Nat.lt_or_ge n0 r with hlt | hge
    · exact Classical.byContradiction fun hns => by
        have := evAtL_quiet x s.hist r (h.squiet r hlt (by omega) (fun hw => hns (Or.inr hw)))
        rw [this] at hre; cases hre
    · exact Or.inl hge
  rcases evAtL_obj x s.hist r e hre with ⟨it, hi, hio⟩ | hrv
  · rw [← hio]
    rcases List.mem_append.mp hi with hi | hi
    · exact h.stored _ (by omega) it hi
    · exact h.stored _ (by omega) it hi
  · have : r < 2 ^ 64 := by have : uint.nat s.st.rv < 2 ^ 64 := by word
                            omega
    rw [hrv, show uint.nat (W64 (r : Int)) = r by word]; exact hst

/-- An anchor, or one after, splits the stored revisions as their images. -/
theorem HRel.anchorIsh_pair (h : HRel A n0 ρ W s c) (u : Nat) (hu : AnchorIsh A u) (r : Nat)
    (hr : StoredRv n0 W r) : r < u ↔ ρ r < u := by
  obtain ⟨v, hv, e⟩ := hu
  obtain ⟨⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := (h.stored_cut r hr).1 v hv
  constructor <;> intro hl <;> rcases e with e | e <;> subst e
  · exact Classical.byContradiction fun hn => by have := h1' (by omega); omega
  · exact Classical.byContradiction fun hn => by have := h2' (by omega); omega
  · exact Classical.byContradiction fun hn => by have := h1 (by omega); omega
  · exact Classical.byContradiction fun hn => by have := h2 (by omega); omega

/-- An anchor pairs with itself. -/
theorem HRel.anchor_pairW (h : HRel A n0 ρ W s c) (v : Nat) (hv : v ∈ A) : PairW n0 ρ W v v := by
  refine ⟨fun _ => rfl, fun w hw => ?_⟩
  have := h.anchorIsh_pair (v + 1) ⟨v, hv, Or.inr rfl⟩ w (Or.inr hw)
  omega

/-- **The events over a range of anchors**, on the search, renamed, are the cluster's. -/
theorem HRel.eventsIn_anchor (h : HRel A n0 ρ W s c) (hn0 : 1 ≤ n0) (x : Input) (lo hi : Nat)
    (hlo : AnchorIsh A lo) (hhi : AnchorIsh A hi) (hs : hi ≤ uint.nat s.st.rv + 1)
    (hc : hi ≤ uint.nat c.st.rv + 1) :
    eventsInL x c.hist lo hi = (eventsInL x s.hist lo hi).map (renEv ρ) := by
  by_cases hl : lo ≤ hi
  · exact h.eventsIn_ren hn0 x lo (h.anchorIsh_pair lo hlo) _ hi hi rfl hl hs hl hc
      (h.anchorIsh_pair hi hhi)
  · simp [eventsInL, Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_le hl))]

end rel2

/-! ## `reliableOkL` -/

theorem anchorIsh_max {A : List Nat} {a b : Nat} (ha : AnchorIsh A a) (hb : AnchorIsh A b) :
    AnchorIsh A (max a b) := by
  rcases Nat.le_total a b with e | e
  · rw [Nat.max_eq_right e]; exact hb
  · rw [Nat.max_eq_left e]; exact ha

theorem anchorIsh_min {A : List Nat} {a b : Nat} (ha : AnchorIsh A a) (hb : AnchorIsh A b) :
    AnchorIsh A (min a b) := by
  rcases Nat.le_total a b with e | e
  · rw [Nat.min_eq_left e]; exact ha
  · rw [Nat.min_eq_right e]; exact hb

/-- The range of anchored events: its ends are anchors or one after, and it ends at most one after
their greatest revision. -/
theorem evRangeL_ok (A : List Nat) (m : Nat) :
    ∀ (evs : List WEv) (acc : Option (Nat × Nat)),
      (∀ lo hi, acc = some (lo, hi) → AnchorIsh A lo ∧ AnchorIsh A hi ∧ hi ≤ m + 1) →
      (∀ e ∈ evs, uint.nat e.o.ResourceVersion' ∈ A ∧ uint.nat e.o.ResourceVersion' ≤ m) →
      ∀ lo hi, evs.foldl evRStep acc = some (lo, hi) → AnchorIsh A lo ∧ AnchorIsh A hi ∧ hi ≤ m + 1
  | [], _, hacc, _ => hacc
  | e :: evs, acc, hacc, he => by
    rw [List.foldl_cons]
    refine evRangeL_ok A m evs _ ?_ (fun e' h' => he e' (List.mem_cons_of_mem _ h'))
    obtain ⟨hA, hm⟩ := he e List.mem_cons_self
    have hlo : AnchorIsh A (evLo e) := by
      unfold evLo; split
      · exact ⟨_, hA, Or.inr rfl⟩
      · exact ⟨_, hA, Or.inl rfl⟩
    have hhi : AnchorIsh A (evHi e) ∧ evHi e ≤ m + 1 := by
      unfold evHi; split
      · exact ⟨⟨_, hA, Or.inl rfl⟩, by omega⟩
      · exact ⟨⟨_, hA, Or.inr rfl⟩, by omega⟩
    intro lo hi hacc'
    unfold evRStep at hacc'
    rcases acc with _ | ⟨lo', hi'⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at hacc'
      obtain ⟨rfl, rfl⟩ := hacc'
      exact ⟨hlo, hhi.1, hhi.2⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at hacc'
      obtain ⟨rfl, rfl⟩ := hacc'
      obtain ⟨h1, h2, h3⟩ := hacc lo' hi' rfl
      exact ⟨anchorIsh_min hlo h1, anchorIsh_max hhi.1 h2, by have := hhi.2; omega⟩

section rel3
variable {A : List Nat} {n0 : Nat} {ρ : Nat → Nat} {W : List Nat} {s c : HSt}

/-- On anchored events of the search's revisions: the events over a range of anchors match on the
cluster, then on the search. -/
theorem HRel.evsEq_anchor (h : HRel A n0 ρ W s c) (hn0 : 1 ≤ n0) (x : Input) (lo hi : Nat)
    (hlo : AnchorIsh A lo) (hhi : AnchorIsh A hi) (hs : hi ≤ uint.nat s.st.rv + 1)
    (hc : hi ≤ uint.nat c.st.rv + 1) (M : List WEv) (hM : ∀ e ∈ M, uint.nat e.o.ResourceVersion' ∈ A)
    (hok : evsEqL (eventsInL x c.hist lo hi) M = true) : evsEqL (eventsInL x s.hist lo hi) M = true := by
  rw [h.eventsIn_anchor hn0 x lo hi hlo hhi hs hc] at hok
  refine evsEqL_ren A ρ _ M (fun e he => ?_) hM hok
  have hst := h.eventsIn_stored x lo hi hs e he
  exact ⟨(h.stored_cut _ hst).1, h.fits _ hst⟩

/-- **`reliableOkL` on the cluster gives it on the search**, for anchored events at most the
search's revision. -/
theorem HRel.reliableOk (h : HRel A n0 ρ W s c) (hn0 : 1 ≤ n0) (x : Input) (req : Nat) (hreq : req ∈ A)
    (evs : List WEv) (hA : ∀ e ∈ evs, uint.nat e.o.ResourceVersion' ∈ A)
    (hle : ∀ e ∈ evs, uint.nat e.o.ResourceVersion' ≤ uint.nat s.st.rv)
    (hok : reliableOkL x req evs c = true) : reliableOkL x req evs s = true := by
  unfold reliableOkL at hok ⊢
  rcases hr : evRangeL evs with _ | ⟨lo0, hi⟩
  · rfl
  rw [hr] at hok
  obtain ⟨hlo0, hhi, hhim⟩ := evRangeL_ok A (uint.nat s.st.rv) evs none (by simp)
    (fun e he => ⟨hA e he, hle e he⟩) lo0 hi hr
  dsimp only at hok ⊢
  have hLO : AnchorIsh A (if x.Match' = W64 1 then (if 0 < req then max lo0 (req + 1) else lo0)
      else if 0 < req then req + 1 else lo0) := by
    have hr1 : AnchorIsh A (req + 1) := ⟨req, hreq, Or.inr rfl⟩
    split
    · split
      · exact anchorIsh_max hlo0 hr1
      · exact hlo0
    · split
      · exact hr1
      · exact hlo0
  generalize (if x.Match' = W64 1 then (if 0 < req then max lo0 (req + 1) else lo0)
      else if 0 < req then req + 1 else lo0) = lo at hLO hok ⊢
  by_cases h1 : x.Match' = W64 2 ∧ req = 0
  · rw [if_pos h1] at hok; cases hok
  rw [if_neg h1] at hok ⊢
  by_cases h2 : uint.nat c.st.rv + 1 < hi
  · rw [if_pos h2] at hok; cases hok
  rw [if_neg h2] at hok; rw [if_neg (by omega)]
  exact h.evsEq_anchor hn0 x lo hi hLO hhi hhim (by omega) _
    (fun e he => hA e (List.mem_filter.mp he).1) hok

end rel3


/-! ## The initial events, the target, and the check -/

theorem initialEventsL_ren (ρ : Nat → Nat) (x : Input) (S C : GSt)
    (h : C.items = S.items.map (renItem ρ)) :
    initialEventsL x C = (initialEventsL x S).map (renEv ρ) := by
  unfold initialEventsL
  rw [h, List.filter_map, List.map_map, List.map_map]
  have hf : ((fun it => keyInScopeL x.WKey' x.Recursive' (storeKeyL it.key') && selOkL x it.obj') ∘
      renItem ρ) = (fun it => keyInScopeL x.WKey' x.Recursive' (storeKeyL it.key') && selOkL x it.obj') := by
    funext it; simp only [Function.comp, renItem_key, renItem_obj, selOkL_ren]
  rw [hf]; rfl

theorem initialEventsL_obj (x : Input) (S : GSt) (e : WEv) (he : e ∈ initialEventsL x S) :
    ∃ it ∈ S.items, it.obj' = e.o := by
  unfold initialEventsL at he
  obtain ⟨it, hi, rfl⟩ := List.mem_map.mp he
  exact ⟨it, (List.mem_filter.mp hi).1, rfl⟩

theorem evMaxL_foldl_ge : ∀ (l : List WEv) (acc : Nat),
    acc ≤ l.foldl (fun t e => max t (uint.nat e.o.ResourceVersion')) acc ∧
      ∀ e ∈ l, uint.nat e.o.ResourceVersion' ≤ l.foldl (fun t e => max t (uint.nat e.o.ResourceVersion')) acc
  | [], _ => ⟨Nat.le_refl _, fun _ h => by cases h⟩
  | e :: l, acc => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := evMaxL_foldl_ge l (max acc (uint.nat e.o.ResourceVersion'))
    refine ⟨by omega, fun e' he' => ?_⟩
    rcases List.mem_cons.mp he' with rfl | he'
    · omega
    · exact h2 e' he'

/-- `evMaxL` bounds every event's revision but the errors'. -/
theorem evMaxL_ge (evs : List WEv) (e : WEv) (he : e ∈ evs) (ht : e.t < 4) :
    uint.nat e.o.ResourceVersion' ≤ evMaxL evs :=
  (evMaxL_foldl_ge _ 0).2 e (List.mem_filter.mpr ⟨he, by simpa using ht⟩)

section rel4
variable {A : List Nat} {n0 : Nat} {ρ : Nat → Nat} {W : List Nat} {s c : HSt}

/-- **A cluster revision from the request's on has a search revision from the request's on paired
with it**: itself below the seeds; above, the greatest of the seeds', the request's (at least 1)
and the last write renamed at or below it. -/
theorem HRel.pair_below (h : HRel A n0 ρ W s c) (hn0 : 1 ≤ n0) (req r : Nat) (hreq : req ∈ A)
    (hr1 : max req 1 ≤ r) (hs : max req 1 ≤ uint.nat s.st.rv) :
    ∃ x', max req 1 ≤ x' ∧ x' ≤ uint.nat s.st.rv ∧ PairW n0 ρ W x' r := by
  have hn0s := h.n0_le
  by_cases hrn : r ≤ n0
  · refine ⟨r, hr1, by omega, fun _ => rfl, fun w hw => ?_⟩
    have := (h.W_in w hw).1; have := (h.ρ_W w hw).1; omega
  · have hwm : (W.filter fun w => ρ w ≤ r).foldr max 0 = 0 ∨
        (W.filter fun w => ρ w ≤ r).foldr max 0 ∈ W.filter (fun w => ρ w ≤ r) := foldr_max_mem _
    have hge : ∀ w ∈ W.filter (fun w => ρ w ≤ r), w ≤ (W.filter fun w => ρ w ≤ r).foldr max 0 :=
      fun w hw => foldr_max_ge _ _ hw
    generalize (W.filter fun w => ρ w ≤ r).foldr max 0 = wm at hwm hge
    have hwm_le : wm ≤ uint.nat s.st.rv := by
      rcases hwm with e | e
      · omega
      · exact (h.W_in _ (List.mem_filter.mp e).1).2
    refine ⟨max n0 (max (max req 1) wm), by omega, by omega, fun _ => by omega, fun w hw => ?_⟩
    have hwn := (h.W_in w hw).1
    constructor
    · intro hle
      rcases (show w ≤ wm ∨ w ≤ max req 1 by omega) with e | e
      · rcases hwm with h0 | hm
        · omega
        · have hm' := List.mem_filter.mp hm
          have := (h.le_iff w wm (Or.inr hw) (Or.inr hm'.1)).mp e
          have : ρ wm ≤ r := by simpa using hm'.2
          omega
      · have := h.anchorIsh_pair (req + 1) ⟨req, hreq, Or.inr rfl⟩ w (Or.inr hw)
        omega
    · intro hle
      have := hge w (List.mem_filter.mpr ⟨hw, by simpa using hle⟩)
      omega


/-- **`initialPrefixOkL` on the cluster gives it on the search**, for anchored events, the search
from the request's revision on. -/
theorem HRel.initialPrefixOk (h : HRel A n0 ρ W s c) (hn0 : 1 ≤ n0) (x : Input) (req : Nat) (hreq : req ∈ A)
    (evs : List WEv) (hA : ∀ e ∈ evs, uint.nat e.o.ResourceVersion' ∈ A)
    (hs : evs ≠ [] → max req 1 ≤ uint.nat s.st.rv)
    (hok : initialPrefixOkL x req evs c = true) : initialPrefixOkL x req evs s = true := by
  unfold initialPrefixOkL at hok ⊢
  by_cases he : evs.isEmpty = true
  · simp [he]
  have hne : evs ≠ [] := fun e => he (by rw [e]; rfl)
  rw [Bool.eq_false_iff.mpr he, Bool.false_or] at hok ⊢
  obtain ⟨r, hr, hcond⟩ := List.any_eq_true.mp hok
  have hr' := List.mem_range'_1.mp hr
  obtain ⟨x', h1, h2, hp⟩ := h.pair_below hn0 req r hreq (by omega) (hs hne)
  have hc := h.hist x' h2 r (by omega) hp
  rw [initialEventsL_ren ρ x _ _ hc] at hcond
  refine List.any_eq_true.mpr ⟨x', List.mem_range'_1.mpr ⟨h1, by omega⟩, ?_⟩
  rw [Bool.and_eq_true] at hcond ⊢
  obtain ⟨hq, hl⟩ := hcond
  rw [← List.map_take] at hq
  rw [List.length_map] at hl
  refine ⟨evsEqL_ren A ρ _ evs (fun e he' => ?_) hA hq, hl⟩
  obtain ⟨it, hi, hio⟩ := initialEventsL_obj x _ e (List.mem_of_mem_take he')
  have hst := h.stored x' h2 it hi
  rw [← hio]; exact ⟨(h.stored_cut _ hst).1, h.fits _ hst⟩

/-- **A watch's check on the cluster gives it on the search** (`notes/k8s-dist-k4.md`, "Handoff
K4-4", step 4), for a watch whose revisions are anchors (`OpAnchors`), the search at its target. -/
theorem HRel.watchOk (h : HRel A n0 ρ W s c) (hn0 : 1 ≤ n0) (x : Input) (y : Output)
    (hanc : OpAnchors A x y) (hk : x.Kind' = W64 5) (htg : targetL x y 0 ≤ uint.nat s.st.rv)
    (hok : watchOkL x y c = true) : watchOkL x y s = true := by
  unfold watchOkL at hok ⊢
  by_cases hf : (y.WFailed' || x.Skip') = true
  · rw [if_pos hf]
  rw [if_neg hf] at hok ⊢
  have hwf : y.WFailed' = false := by revert hf; cases y.WFailed' <;> simp
  rcases hd : decWEventsL y.WEvents' with _ | all
  · rw [hd] at hok; cases hok
  rw [hd] at hok
  dsimp only at hok ⊢
  by_cases h5 : all.any (fun e => 5 ≤ e.t) = true
  · rw [if_pos h5] at hok; cases hok
  rw [if_neg h5] at hok ⊢
  have h5' : ∀ e ∈ all, e.t < 5 := fun e he => by
    have := List.any_eq_false.mp (Bool.eq_false_iff.mpr h5) e he; simp at this; omega
  have hA : ∀ e ∈ all.filter (fun e => e.t ≠ 4), uint.nat e.o.ResourceVersion' ∈ A := fun e he => by
    have he' := List.mem_filter.mp he
    exact hanc.2.2.1 hk hwf all hd e he'.1 (by have := h5' e he'.1; have : e.t ≠ 4 := by simpa using he'.2
                                                 omega)
  have hmax : evMaxL all ≤ uint.nat s.st.rv := by
    refine Nat.le_trans ?_ htg
    unfold targetL; rw [if_pos hk, if_neg hf, hd]; dsimp only
    split
    · split
      · exact Nat.le_max_left _ _
      · exact Nat.le_refl _
    · exact Nat.le_refl _
  have hle : ∀ e ∈ all.filter (fun e => e.t ≠ 4), uint.nat e.o.ResourceVersion' ≤ uint.nat s.st.rv :=
    fun e he => by
      have he' := List.mem_filter.mp he
      have : e.t ≠ 4 := by simpa using he'.2
      have := h5' e he'.1
      exact Nat.le_trans (evMaxL_ge all e he'.1 (by omega)) hmax
  have hreq1 : x.SendInit' = W64 2 → all.filter (fun e => e.t ≠ 4) ≠ [] → ∀ r, parseRVD x.MinRV' = some r →
      max (uint.nat r) 1 ≤ uint.nat s.st.rv := by
    intro hsi hne r hr
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
    have he' := List.mem_filter.mp he
    have hany : all.any (fun e => e.t < 4) = true := List.any_eq_true.mpr ⟨e, he'.1, by
      have := h5' e he'.1; have : e.t ≠ 4 := by simpa using he'.2
      simp; omega⟩
    refine Nat.le_trans ?_ htg
    unfold targetL; rw [if_pos hk, if_neg hf, hd]; dsimp only
    rw [if_pos ⟨hsi, hany⟩, hr]; exact Nat.le_max_right _ _
  generalize all.filter (fun e => e.t ≠ 4) = evs at hA hle hok hreq1 ⊢
  by_cases hrv : evs.any (fun e => uint.nat s.st.rv < uint.nat e.o.ResourceVersion') = true
  · exfalso; obtain ⟨e, he, hlt⟩ := List.any_eq_true.mp hrv; have := hle e he; simp at hlt; omega
  rw [if_neg hrv]
  by_cases hrc : evs.any (fun e => uint.nat c.st.rv < uint.nat e.o.ResourceVersion') = true
  · rw [if_pos hrc] at hok; cases hok
  rw [if_neg hrc] at hok
  by_cases hbm : (!bookmarksOkL evs) = true
  · rw [if_pos hbm] at hok; cases hok
  rw [if_neg hbm] at hok ⊢
  rcases hp : parseRVD x.MinRV' with _ | reqw
  · rw [hp] at hok; cases hok
  rw [hp] at hok
  dsimp only at hok ⊢
  have hreq : uint.nat reqw ∈ A := hanc.1 reqw hp
  by_cases hsi : x.SendInit' = W64 2
  · rw [if_pos hsi] at hok ⊢
    rcases hb : evs.findIdx? (fun e => e.t = 3) with _ | b
    · rw [hb] at hok ⊢
      exact h.initialPrefixOk hn0 x _ hreq evs hA (fun hne => hreq1 hsi hne reqw hp) hok
    · rw [hb] at hok ⊢
      dsimp only at hok ⊢
      generalize hbmd : evs.getD b ⟨0, ⟨[], [], [], [], [], [], 0, false⟩⟩ = bm at hok ⊢
      by_cases ha : (!bm.o.Annotated') = true
      · rw [if_pos ha] at hok; cases hok
      rw [if_neg ha] at hok ⊢
      by_cases hc1 : (uint.nat reqw ≠ 0 ∧ uint.nat bm.o.ResourceVersion' < uint.nat reqw) ∨
          uint.nat bm.o.ResourceVersion' < 1 ∨ uint.nat c.st.rv < uint.nat bm.o.ResourceVersion'
      · rw [if_pos hc1] at hok; cases hok
      rw [if_neg hc1] at hok
      have hbmem : bm ∈ evs := by
        rw [List.getD_eq_getElem?_getD] at hbmd
        rcases hg : evs[b]? with _ | bm'
        · rw [hg] at hbmd; simp only [Option.getD_none] at hbmd; subst hbmd
          exfalso; exact hc1 (Or.inr (Or.inl (by simp)))
        · rw [hg] at hbmd; simp only [Option.getD_some] at hbmd; subst hbmd
          exact List.mem_of_getElem? hg
      have hbA := hA bm hbmem
      have hbs := hle bm hbmem
      rw [if_neg (by omega)]
      by_cases hie : (!evsEqL (initialEventsL x (histN c.hist (uint.nat bm.o.ResourceVersion'))) (evs.take b)) = true
      · rw [if_pos hie] at hok; cases hok
      rw [if_neg hie] at hok
      have hc := h.hist _ hbs _ (by omega) (h.anchor_pairW _ hbA)
      have hie' : evsEqL (initialEventsL x (histN s.hist (uint.nat bm.o.ResourceVersion'))) (evs.take b) = true := by
        have : evsEqL (initialEventsL x (histN c.hist (uint.nat bm.o.ResourceVersion'))) (evs.take b) = true := by
          simpa using hie
        rw [initialEventsL_ren ρ x _ _ hc] at this
        refine evsEqL_ren A ρ _ _ (fun e he' => ?_) (fun e he' => hA e (List.mem_of_mem_take he')) this
        obtain ⟨it, hi, hio⟩ := initialEventsL_obj x _ e he'
        have hst := h.stored _ hbs it hi
        rw [← hio]; exact ⟨(h.stored_cut _ hst).1, h.fits _ hst⟩
      rw [if_neg (by simp [hie'])]
      exact h.reliableOk hn0 x _ hreq _ (fun e he => hA e (List.mem_of_mem_drop he))
        (fun e he => hle e (List.mem_of_mem_drop he)) hok
  · rw [if_neg hsi] at hok ⊢
    exact h.reliableOk hn0 x _ hreq evs hA hle hok

end rel4

end go

end k8s_dist
end EtcdGrove
end Perennial
