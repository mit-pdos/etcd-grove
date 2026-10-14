/-
Lean-first (no Rocq counterpart).

# The search's linked list, in pure terms (2026-10-14)

`checkSingle` keeps the entries not lifted as a doubly-linked list of nodes behind a head node
(`headEntry`). A *slot* is the head (`none`) or the node of an entry (`some e`). The list of
slots linked is `cur es B`: the head, then the entries of the operations not in `B` (the ids
lifted, newest first), in order. A lifted node is not in the list, and keeps the neighbours it
had when it was lifted (what `unlift` needs to relink it): the call of the operation lifted by
a frame, those of the list below the frame; its return, those of that list without the call.
`layout es B x` is the neighbours (previous, next) of every slot `x` (`lift_layout`,
`unlift_layout`: what `lift` and `unlift` do to it).
-/
module

public import Proof.github_com.anishathalye.porcupine.ListLemmas

@[expose] public section

namespace Perennial
namespace github_com.anishathalye.porcupine
namespace Theory

/-- A slot of the list: the head (`none`) or the node of an entry. -/
abbrev Slot := Option Entry

/-- The slots linked when the operations `B` are lifted: the head, then `rem es B`. -/
def cur (es : List Entry) (B : List Nat) : List Slot := none :: (rem es B).map some

/-- The neighbours of every slot when the operations `B` (newest first) are lifted. -/
def layout (es : List Entry) : List Nat → Slot → Option Slot × Option Slot
  | [], x => nb (cur es []) x
  | y :: B, x =>
    if x ∈ cur es (y :: B) then nb (cur es (y :: B)) x
    else if x = some ⟨false, y⟩ then nb (cur es B) x
    else if x = some ⟨true, y⟩ then nb ((cur es B).erase (some ⟨false, y⟩)) x
    else layout es B x

theorem layout_cur {es : List Entry} {B : List Nat} {x : Slot} (hx : x ∈ cur es B) :
    layout es B x = nb (cur es B) x := by
  cases B with
  | nil => rfl
  | cons y B => simp only [layout, hx, ↓reduceIte]

theorem nodup_map_some {α : Type} {l : List α} (h : l.Nodup) : (l.map some).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    rw [List.nodup_cons] at h
    simp only [List.map_cons, List.nodup_cons, List.mem_map, Option.some.injEq, not_exists,
      not_and]
    exact ⟨fun x hx hxa => h.1 (hxa ▸ hx), ih h.2⟩

theorem rem_nodup {es : List Entry} (hnd : es.Nodup) (B : List Nat) : (rem es B).Nodup :=
  hnd.sublist List.filter_sublist

theorem cur_nodup {es : List Entry} (hnd : es.Nodup) (B : List Nat) : (cur es B).Nodup := by
  unfold cur
  rw [List.nodup_cons]
  exact ⟨by simp, nodup_map_some (rem_nodup hnd B)⟩

theorem cur_getElem? {es : List Entry} {B : List Nat} {p : Nat} :
    (cur es B)[p + 1]? = ((rem es B)[p]?).map some := by
  simp [cur]

theorem cur_sub {es : List Entry} {B : List Nat} {y : Nat} {x : Slot} (hx : x ∈ cur es (y :: B)) :
    x ∈ cur es B := by
  unfold cur at hx ⊢
  simp only [List.mem_cons, List.mem_map] at hx ⊢
  rcases hx with rfl | ⟨e, he, rfl⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨e, ?_, rfl⟩
    simp only [rem, List.mem_filter, decide_eq_true_eq, List.mem_cons, not_or] at he ⊢
    exact ⟨he.1, he.2.2⟩

theorem map_some_erase {α : Type} [DecidableEq α] (l : List α) (a : α) :
    (l.map some).erase (some a) = (l.erase a).map some := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases h : b = a
    · subst h; simp
    · rw [List.map_cons, List.erase_cons_tail (by simpa using h), List.erase_cons_tail (by simpa using h),
        ih, List.map_cons]

/-- Lifting `y` removes its call and its return from the list. -/
theorem rem_cons {es : List Entry} (hnd : es.Nodup) (B : List Nat) (y : Nat) :
    rem es (y :: B) = ((rem es B).erase ⟨false, y⟩).erase ⟨true, y⟩ := by
  have hnd' := rem_nodup hnd B
  rw [List.Nodup.erase_eq_filter (hnd'.erase _) _, List.Nodup.erase_eq_filter hnd' _,
    List.filter_filter]
  unfold rem
  rw [List.filter_filter]
  apply List.filter_congr
  intro e _
  obtain ⟨b, i⟩ := e
  cases b <;> by_cases hi : i = y <;> simp [hi]

theorem cur_cons {es : List Entry} (hnd : es.Nodup) (B : List Nat) (y : Nat) :
    cur es (y :: B) = ((cur es B).erase (some ⟨false, y⟩)).erase (some ⟨true, y⟩) := by
  unfold cur
  rw [List.erase_cons_tail (by simp), List.erase_cons_tail (by simp), map_some_erase,
    map_some_erase, rem_cons hnd]

/-- `lift` on a list `l`: unlinking `c = l[p + 1]`, then `r = l[q + 1]` (`p < q`). -/
theorem lift_core {l : List Slot} (hlnd : l.Nodup) {p q : Nat} {c r : Slot}
    (hc : l[p + 1]? = some c) (hpq : p < q) (hr : l[q + 1]? = some r)
    {G : Slot → Option Slot × Option Slot} (hG : ∀ x ∈ l, G x = nb l x) :
    ∃ (pc nc rp : Slot) (rn : Option Slot),
      G c = (some pc, some nc) ∧ eraseG G pc (some nc) r = (some rp, rn) ∧
      (∀ x ∈ (l.erase c).erase r, eraseG (eraseG G pc (some nc)) rp rn x =
        nb ((l.erase c).erase r) x) ∧
      eraseG (eraseG G pc (some nc)) rp rn r = nb (l.erase c) r ∧
      eraseG (eraseG G pc (some nc)) rp rn c = G c ∧
      (∀ x, x ∉ l → eraseG (eraseG G pc (some nc)) rp rn x = G x) := by
  obtain ⟨pc, hpc⟩ : ∃ pc, l[p]? = some pc :=
    ⟨l[p]'(by have := (List.getElem?_eq_some_iff.mp hc).1; omega), List.getElem?_eq_getElem _⟩
  obtain ⟨nc, hnc⟩ : ∃ nc, l[p + 2]? = some nc :=
    ⟨l[p + 2]'(by have := (List.getElem?_eq_some_iff.mp hr).1; omega), List.getElem?_eq_getElem _⟩
  have hcm : c ∈ l := List.mem_of_getElem? hc
  have hG0c : G c = (some pc, some nc) := by
    rw [hG c hcm]; unfold nb; rw [prevOf_succ hlnd hc, nextOf_getElem? hlnd hc, hpc, hnc]
  obtain ⟨hA1, hA2⟩ := erase_step hlnd hc hpc hG
  rw [hnc] at hA1 hA2
  have hl1nd : (l.erase c).Nodup := hlnd.erase c
  have hl1e : l.erase c = l.eraseIdx (p + 1) := erase_eq_eraseIdx_of_getElem? hlnd hc
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hr1 : (l.erase c)[q' + 1]? = some r := by
    rw [hl1e, List.getElem?_eraseIdx, ite_eq_right (by omega)]; exact hr
  obtain ⟨rp, hrp⟩ : ∃ rp, (l.erase c)[q']? = some rp :=
    ⟨(l.erase c)[q']'(by have := (List.getElem?_eq_some_iff.mp hr1).1; omega),
      List.getElem?_eq_getElem _⟩
  have hrm1 : r ∈ l.erase c := List.mem_of_getElem? hr1
  obtain ⟨hB1, hB2⟩ := erase_step hl1nd hr1 hrp hA1
  have hcl1 : c ∉ l.erase c := List.Nodup.not_mem_erase hlnd
  have hrl2 : r ∉ (l.erase c).erase r := List.Nodup.not_mem_erase hl1nd
  refine ⟨pc, nc, rp, (l.erase c)[q' + 2]?, hG0c, ?_, hB1, ?_, ?_, ?_⟩
  · rw [hA1 r hrm1]; unfold nb; rw [prevOf_succ hl1nd hr1, nextOf_getElem? hl1nd hr1, hrp]
  · rw [hB2 r hrl2, hA1 r hrm1]
  · rw [hB2 c (fun h => hcl1 ((List.erase_subset) h)), hA2 c hcl1]
  · intro x hx
    have hx1 : x ∉ l.erase c := fun h => hx ((List.erase_subset) h)
    rw [hB2 x (fun h => hx1 ((List.erase_subset) h)), hA2 x hx1]

/-- `unlift` on a list `l`: relinking `r = l[q + 1]`, then `c = l[p + 1]` (`p < q`), from the
neighbours in `(l.erase c).erase r` and the frozen ones of `r` and `c`. -/
theorem unlift_core {l : List Slot} (hlnd : l.Nodup) {p q : Nat} {c r : Slot}
    (hc : l[p + 1]? = some c) (hpq : p < q) (hr : l[q + 1]? = some r)
    {G : Slot → Option Slot × Option Slot}
    (hG : ∀ x ∈ (l.erase c).erase r, G x = nb ((l.erase c).erase r) x)
    (hGr : G r = nb (l.erase c) r) (hGc : G c = nb l c) :
    ∃ (pc nc rp : Slot) (rn : Option Slot),
      G r = (some rp, rn) ∧ insertG G rp r rn c = (some pc, some nc) ∧
      (∀ x ∈ l, insertG (insertG G rp r rn) pc c (some nc) x = nb l x) ∧
      (∀ x, x ∉ l → insertG (insertG G rp r rn) pc c (some nc) x = G x) := by
  obtain ⟨pc, hpc⟩ : ∃ pc, l[p]? = some pc :=
    ⟨l[p]'(by have := (List.getElem?_eq_some_iff.mp hc).1; omega), List.getElem?_eq_getElem _⟩
  obtain ⟨nc, hnc⟩ : ∃ nc, l[p + 2]? = some nc :=
    ⟨l[p + 2]'(by have := (List.getElem?_eq_some_iff.mp hr).1; omega), List.getElem?_eq_getElem _⟩
  have hl1nd : (l.erase c).Nodup := hlnd.erase c
  have hl1e : l.erase c = l.eraseIdx (p + 1) := erase_eq_eraseIdx_of_getElem? hlnd hc
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hr1 : (l.erase c)[q' + 1]? = some r := by
    rw [hl1e, List.getElem?_eraseIdx, ite_eq_right (by omega)]; exact hr
  obtain ⟨rp, hrp⟩ : ∃ rp, (l.erase c)[q']? = some rp :=
    ⟨(l.erase c)[q']'(by have := (List.getElem?_eq_some_iff.mp hr1).1; omega),
      List.getElem?_eq_getElem _⟩
  obtain ⟨hB1, hB2⟩ := insert_step hl1nd hr1 hrp hG hGr
  have hcl1 : c ∉ l.erase c := List.Nodup.not_mem_erase hlnd
  have hcl2 : c ∉ (l.erase c).erase r := fun h => hcl1 ((List.erase_subset) h)
  have hGmc : insertG G rp r (l.erase c)[q' + 2]? c = nb l c := by rw [hB2 c hcl2, hGc]
  obtain ⟨hA1, hA2⟩ := insert_step hlnd hc hpc hB1 hGmc
  rw [hnc] at hA1 hA2
  refine ⟨pc, nc, rp, (l.erase c)[q' + 2]?, ?_, ?_, hA1, ?_⟩
  · rw [hGr]; unfold nb; rw [prevOf_succ hl1nd hr1, nextOf_getElem? hl1nd hr1, hrp]
  · rw [hGmc]; unfold nb; rw [prevOf_succ hlnd hc, nextOf_getElem? hlnd hc, hpc, hnc]
  · intro x hx
    have hx1 : x ∉ l.erase c := fun h => hx ((List.erase_subset) h)
    rw [hA2 x hx1, hB2 x (fun h => hx1 ((List.erase_subset) h))]

/-- What `lift` does: the call `c = (rem es B)[p]` and its return `r = (rem es B)[q]` (`p < q`)
are unlinked one after the other (`eraseG` twice), which leaves `layout es (y :: B)`. The slots
`lift` reads and writes: `pc`, `nc` (`c`'s neighbours), `rp`, `rn` (`r`'s, once `c` is
unlinked). -/
theorem lift_layout {es : List Entry} (hnd : es.Nodup) {B : List Nat} {p q y : Nat}
    (hp : (rem es B)[p]? = some ⟨false, y⟩) (hpq : p < q) (hq : (rem es B)[q]? = some ⟨true, y⟩) :
    ∃ (pc nc rp : Slot) (rn : Option Slot),
      layout es B (some ⟨false, y⟩) = (some pc, some nc) ∧
      eraseG (layout es B) pc (some nc) (some ⟨true, y⟩) = (some rp, rn) ∧
      (∀ x, eraseG (eraseG (layout es B) pc (some nc)) rp rn x = layout es (y :: B) x) := by
  have hc : (cur es B)[p + 1]? = some (some ⟨false, y⟩) := by rw [cur_getElem?, hp]; rfl
  have hr : (cur es B)[q + 1]? = some (some ⟨true, y⟩) := by rw [cur_getElem?, hq]; rfl
  obtain ⟨pc, nc, rp, rn, h1, h2, h3, h4, h5, h6⟩ :=
    lift_core (cur_nodup hnd B) hc hpq hr (fun x hx => layout_cur hx)
  refine ⟨pc, nc, rp, rn, h1, h2, fun x => ?_⟩
  rw [← cur_cons hnd] at h3
  by_cases hx2 : x ∈ cur es (y :: B)
  · rw [h3 x hx2, layout_cur hx2]
  · by_cases hxr : x = some ⟨true, y⟩
    · subst hxr
      rw [h4]
      simp only [layout, hx2, ↓reduceIte, Option.some.injEq, Entry.mk.injEq,
        Bool.true_eq_false, false_and]
    · by_cases hxc : x = some ⟨false, y⟩
      · subst hxc
        rw [h5, layout_cur (List.mem_of_getElem? hc)]
        simp only [layout, hx2, ↓reduceIte]
      · have hxl : x ∉ cur es B := by
          intro h
          apply hx2
          rw [cur_cons hnd]
          exact (List.mem_erase_of_ne hxr).mpr ((List.mem_erase_of_ne hxc).mpr h)
        rw [h6 x hxl]
        simp only [layout, hx2, hxc, hxr, ↓reduceIte]

/-- What `unlift` does: the return `r` of `y` is relinked, then its call `c` (`insertG` twice),
which leaves `layout es B`. The slots `unlift` reads and writes: `rp`, `rn` (`r`'s
neighbours, frozen), `pc`, `nc` (`c`'s, frozen). -/
theorem unlift_layout {es : List Entry} (hnd : es.Nodup) {B : List Nat} {p q y : Nat}
    (hp : (rem es B)[p]? = some ⟨false, y⟩) (hpq : p < q) (hq : (rem es B)[q]? = some ⟨true, y⟩) :
    ∃ (pc nc rp : Slot) (rn : Option Slot),
      layout es (y :: B) (some ⟨true, y⟩) = (some rp, rn) ∧
      insertG (layout es (y :: B)) rp (some ⟨true, y⟩) rn (some ⟨false, y⟩) = (some pc, some nc) ∧
      (∀ x, insertG (insertG (layout es (y :: B)) rp (some ⟨true, y⟩) rn) pc (some ⟨false, y⟩)
        (some nc) x = layout es B x) := by
  have hc : (cur es B)[p + 1]? = some (some ⟨false, y⟩) := by rw [cur_getElem?, hp]; rfl
  have hr : (cur es B)[q + 1]? = some (some ⟨true, y⟩) := by rw [cur_getElem?, hq]; rfl
  have hlnd := cur_nodup hnd B
  have hl2 := cur_cons hnd B y
  have hcnot : (some ⟨false, y⟩ : Slot) ∉ cur es (y :: B) := by
    rw [hl2]; intro h; exact (List.Nodup.not_mem_erase hlnd) ((List.erase_subset) h)
  have hrnot : (some ⟨true, y⟩ : Slot) ∉ cur es (y :: B) := by
    rw [hl2]; exact List.Nodup.not_mem_erase (hlnd.erase _)
  obtain ⟨pc, nc, rp, rn, h1, h2, h3, h4⟩ := unlift_core hlnd hc hpq hr (G := layout es (y :: B))
    (fun x hx => by rw [← hl2] at hx ⊢; exact layout_cur hx)
    (by simp only [layout, hrnot, ↓reduceIte, Option.some.injEq, Entry.mk.injEq,
          Bool.true_eq_false, false_and])
    (by simp only [layout, hcnot, ↓reduceIte])
  refine ⟨pc, nc, rp, rn, h1, h2, fun x => ?_⟩
  by_cases hxl : x ∈ cur es B
  · rw [h3 x hxl, layout_cur hxl]
  · rw [h4 x hxl]
    have hx3 : x ∉ cur es (y :: B) := fun h => hxl (cur_sub h)
    have hxc : x ≠ some ⟨false, y⟩ := fun h => hxl (h ▸ List.mem_of_getElem? hc)
    have hxr : x ≠ some ⟨true, y⟩ := fun h => hxl (h ▸ List.mem_of_getElem? hr)
    simp only [layout, hx3, ↓reduceIte, hxc, hxr]

end Theory
end github_com.anishathalye.porcupine
end Perennial
