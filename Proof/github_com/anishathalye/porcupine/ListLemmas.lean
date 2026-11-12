/-
Lean-first (no Rocq counterpart).

# Doubly-linked lists, in pure terms (2026-10-14)

The neighbours of an element in a list without duplicates (`prevOf`, `nextOf`), and what
unlinking an element does to them (`eraseG`, `erase_step`) and relinking it (`insertG`,
`insert_step`): `lift` and `unlift` in `checker.go` ("dancing links") are these on the list of
nodes. The neighbours are given as a function `G : α → Option α × Option α` (previous, next),
updated pointwise, as the Go code stores fields one at a time.
-/
module

public import Proof.github_com.anishathalye.porcupine.Theory

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial
namespace github_com.anishathalye.porcupine
namespace Theory

section generic
variable {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]

/-- `f` with `a` mapped to `v` (`Function.update`, which is Mathlib's). -/
def upd {β : Type} (f : α → β) (a : α) (v : β) : α → β := fun x => if x = a then v else f x

@[simp] theorem upd_self {β : Type} (f : α → β) (a : α) (v : β) : upd f a v a = v := by
  simp [upd]

theorem upd_ne {β : Type} {f : α → β} {a x : α} {v : β} (h : x ≠ a) : upd f a v x = f x := by
  simp [upd, h]

/-- The element after `x` in `l` (`none` if `x` is last or absent). -/
def nextOf : List α → α → Option α
  | [], _ => none
  | a :: l, x => if a = x then l.head? else nextOf l x

/-- The element before `x` in `l` (`none` if `x` is first or absent). -/
def prevOf : List α → α → Option α
  | [], _ => none
  | a :: l, x => if l.head? = some x then some a else prevOf l x

/-- Both neighbours. -/
def nb (l : List α) (x : α) : Option α × Option α := (prevOf l x, nextOf l x)

theorem prevOf_not_mem {l : List α} {x : α} (h : x ∉ l) : prevOf l x = none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mem_cons, not_or] at h
    have : l.head? ≠ some x := fun h' => h.2 (List.mem_of_mem_head? h')
    simp only [prevOf, this, ↓reduceIte, ih h.2]

omit [DecidableEq α] in
theorem getElem?_inj {l : List α} (hnd : l.Nodup) {i j : Nat} {x : α}
    (hi : l[i]? = some x) (hj : l[j]? = some x) : i = j := by
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj', hx⟩ := List.getElem?_eq_some_iff.mp hj
  exact (List.Nodup.getElem_inj hnd).mp hx.symm

theorem nextOf_getElem? {l : List α} (hnd : l.Nodup) {i : Nat} {x : α} (h : l[i]? = some x) :
    nextOf l x = l[i + 1]? := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [nextOf, List.head?_eq_getElem?]
    | succ i =>
      simp only [List.getElem?_cons_succ] at h ⊢
      have hx : x ∈ l := List.mem_of_getElem? h
      have hax : a ≠ x := fun h' => hnd.1 (h' ▸ hx)
      simp only [nextOf, ite_eq_right hax]
      exact ih hnd.2 h

theorem prevOf_zero {l : List α} (hnd : l.Nodup) {x : α} (h : l[0]? = some x) :
    prevOf l x = none := by
  cases l with
  | nil => simp at h
  | cons a l =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [List.nodup_cons] at hnd
    have : l.head? ≠ some a := fun h' => hnd.1 (List.mem_of_mem_head? h')
    simp only [prevOf, this, ↓reduceIte, prevOf_not_mem hnd.1]

theorem prevOf_succ {l : List α} (hnd : l.Nodup) {i : Nat} {x : α} (h : l[i + 1]? = some x) :
    prevOf l x = l[i]? := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.getElem?_cons_succ] at h
    have hnd' := (List.nodup_cons.mp hnd).2
    cases i with
    | zero =>
      have : l.head? = some x := by rw [List.head?_eq_getElem?]; exact h
      simp [prevOf, this]
    | succ i =>
      have : l.head? ≠ some x := by
        rw [List.head?_eq_getElem?]
        intro h0
        have := getElem?_inj hnd' h0 h
        omega
      simp only [prevOf, this, ↓reduceIte, List.getElem?_cons_succ]
      exact ih hnd' h

theorem erase_eq_eraseIdx_of_getElem? {l : List α} (hnd : l.Nodup) {i : Nat} {c : α}
    (h : l[i]? = some c) : l.erase c = l.eraseIdx i := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      have hac : a ≠ c := fun h' => hnd.1 (h' ▸ List.mem_of_getElem? h)
      rw [List.erase_cons_tail (by simpa using hac), ih hnd.2 h]
      rfl

/-! ## Unlinking and relinking one element -/

/-- Unlinking the element after `pc` whose next is `n`: `pc.next = n`, then `n.prev = pc` if
`n` is not `nil` (`lift`'s two stores for one node). -/
def eraseG (G : α → Option α × Option α) (pc : α) (n : Option α) : α → Option α × Option α :=
  let G1 := upd G pc ((G pc).1, n)
  match n with
  | none => G1
  | some n' => upd G1 n' (some pc, (G1 n').2)

/-- Relinking `c` after `pc`, before `n`: `pc.next = c`, then `n.prev = c` if `n` is not `nil`
(`unlift`'s two stores for one node). -/
def insertG (G : α → Option α × Option α) (pc c : α) (n : Option α) : α → Option α × Option α :=
  let G1 := upd G pc ((G pc).1, some c)
  match n with
  | none => G1
  | some n' => upd G1 n' (some c, (G1 n').2)

/-- The neighbours in `l.erase c` of the elements other than `c`, from those in `l` (`c` at
`i + 1`, after `l[i]`). -/
theorem nb_erase {l : List α} (hnd : l.Nodup) {i : Nat} {c pc : α} (hc : l[i + 1]? = some c)
    (hpc : l[i]? = some pc) {x : α} (hx : x ∈ l.erase c) :
    nextOf (l.erase c) x = (if x = pc then l[i + 2]? else nextOf l x) ∧
    prevOf (l.erase c) x = (if some x = l[i + 2]? then some pc else prevOf l x) := by
  have hnd' : (l.erase c).Nodup := hnd.erase c
  rw [erase_eq_eraseIdx_of_getElem? hnd hc] at hx hnd' ⊢
  obtain ⟨j, hj⟩ := List.getElem_of_mem hx
  have hj' : (l.eraseIdx (i + 1))[j]? = some x := by rw [List.getElem?_eq_getElem hj.1, hj.2]
  have hget : ∀ k, (l.eraseIdx (i + 1))[k]? = if k < i + 1 then l[k]? else l[k + 1]? :=
    fun k => List.getElem?_eraseIdx
  rw [nextOf_getElem? hnd' hj', hget]
  have hj2 := hj'
  rw [hget] at hj2
  constructor
  · by_cases hji : j < i + 1
    · rw [ite_eq_left hji] at hj2
      by_cases hji' : j = i
      · subst hji'
        rw [hpc] at hj2; cases hj2
        simp
      · have hxpc : x ≠ pc := fun h => hji' (getElem?_inj hnd hj2 (h ▸ hpc))
        rw [ite_eq_right hxpc, ite_eq_left (by omega), nextOf_getElem? hnd hj2]
    · rw [ite_eq_right hji] at hj2
      have hxpc : x ≠ pc := fun h => by have := getElem?_inj hnd hj2 (h ▸ hpc); omega
      rw [ite_eq_right hxpc, ite_eq_right (by omega), nextOf_getElem? hnd hj2]
  · cases j with
    | zero =>
      rw [ite_eq_left (by omega)] at hj2
      rw [prevOf_zero hnd' hj', prevOf_zero hnd hj2]
      have : some x ≠ l[i + 2]? := fun h => by have := getElem?_inj hnd hj2 h.symm; omega
      rw [ite_eq_right this]
    | succ k =>
      rw [prevOf_succ hnd' hj', hget]
      by_cases hk : k + 1 < i + 1
      · rw [ite_eq_left hk] at hj2
        rw [ite_eq_left (by omega), prevOf_succ hnd hj2]
        have : some x ≠ l[i + 2]? := fun h => by have := getElem?_inj hnd hj2 h.symm; omega
        rw [ite_eq_right this]
      · rw [ite_eq_right hk] at hj2
        by_cases hki : k = i
        · subst hki
          rw [ite_eq_left (by omega), hpc, ite_eq_left hj2.symm]
        · rw [ite_eq_right (by omega), prevOf_succ hnd hj2]
          have : some x ≠ l[i + 2]? := fun h => by have := getElem?_inj hnd hj2 h.symm; omega
          rw [ite_eq_right this]

/-- Unlinking `c` (at `i + 1`, after `pc = l[i]`): from the neighbours in `l`, `eraseG` gives
the neighbours in `l.erase c`, and changes nothing outside `l.erase c`. -/
theorem erase_step {l : List α} (hnd : l.Nodup) {i : Nat} {c pc : α} (hc : l[i + 1]? = some c)
    (hpc : l[i]? = some pc) {G : α → Option α × Option α} (hG : ∀ x ∈ l, G x = nb l x) :
    (∀ x ∈ l.erase c, eraseG G pc l[i + 2]? x = nb (l.erase c) x) ∧
    (∀ x, x ∉ l.erase c → eraseG G pc l[i + 2]? x = G x) := by
  have hpcm : pc ∈ l.erase c := by
    rw [erase_eq_eraseIdx_of_getElem? hnd hc, List.mem_eraseIdx_iff_getElem?]
    exact ⟨i, by omega, hpc⟩
  have hnm : ∀ n', l[i + 2]? = some n' → n' ∈ l.erase c := fun n' hn' => by
    rw [erase_eq_eraseIdx_of_getElem? hnd hc, List.mem_eraseIdx_iff_getElem?]
    exact ⟨i + 2, by omega, hn'⟩
  have hpcn : ∀ n', l[i + 2]? = some n' → pc ≠ n' := fun n' hn' h => by
    have := getElem?_inj hnd hpc (h ▸ hn'); omega
  constructor
  · intro x hx
    have hxl : x ∈ l := (List.erase_subset) hx
    obtain ⟨h1, h2⟩ := nb_erase hnd hc hpc hx
    unfold nb
    rw [h1, h2]
    unfold eraseG
    cases hn : l[i + 2]? with
    | none =>
      simp only
      by_cases hxpc : x = pc
      · subst hxpc
        simp [upd_self, hG _ hxl, nb]
      · rw [upd_ne hxpc, hG x hxl]
        simp [nb, hxpc]
    | some n' =>
      simp only
      by_cases hxn : x = n'
      · subst hxn
        have hne := hpcn x hn
        rw [upd_self, upd_ne (Ne.symm hne), hG x hxl]
        simp [nb, Ne.symm hne]
      · rw [upd_ne hxn]
        have : ¬ some x = some n' := fun h => hxn (Option.some.inj h)
        by_cases hxpc : x = pc
        · subst hxpc
          simp [upd_self, hG _ hxl, nb, this]
        · rw [upd_ne hxpc, hG x hxl]
          simp [nb, hxpc, this]
  · intro x hx
    unfold eraseG
    have hxpc : x ≠ pc := fun h => hx (h ▸ hpcm)
    cases hn : l[i + 2]? with
    | none => simp only; rw [upd_ne hxpc]
    | some n' =>
      have hxn : x ≠ n' := fun h => hx (h ▸ hnm n' hn)
      simp only; rw [upd_ne hxn, upd_ne hxpc]

/-- Relinking `c` (at `i + 1` in `l`, after `pc = l[i]`): from the neighbours in `l.erase c`
and `c`'s own (those it had in `l`), `insertG` gives the neighbours in `l`, and changes nothing
outside `l.erase c`. -/
theorem insert_step {l : List α} (hnd : l.Nodup) {i : Nat} {c pc : α} (hc : l[i + 1]? = some c)
    (hpc : l[i]? = some pc) {G : α → Option α × Option α}
    (hG : ∀ x ∈ l.erase c, G x = nb (l.erase c) x) (hGc : G c = nb l c) :
    (∀ x ∈ l, insertG G pc c l[i + 2]? x = nb l x) ∧
    (∀ x, x ∉ l.erase c → insertG G pc c l[i + 2]? x = G x) := by
  have hpcm : pc ∈ l.erase c := by
    rw [erase_eq_eraseIdx_of_getElem? hnd hc, List.mem_eraseIdx_iff_getElem?]
    exact ⟨i, by omega, hpc⟩
  have hnm : ∀ n', l[i + 2]? = some n' → n' ∈ l.erase c := fun n' hn' => by
    rw [erase_eq_eraseIdx_of_getElem? hnd hc, List.mem_eraseIdx_iff_getElem?]
    exact ⟨i + 2, by omega, hn'⟩
  have hpcn : ∀ n', l[i + 2]? = some n' → pc ≠ n' := fun n' hn' h => by
    have := getElem?_inj hnd hpc (h ▸ hn'); omega
  have hcpc : c ≠ pc := fun h => by have := getElem?_inj hnd hc (h ▸ hpc); omega
  have hcn : ∀ n', l[i + 2]? = some n' → c ≠ n' := fun n' hn' h => by
    have := getElem?_inj hnd hc (h ▸ hn'); omega
  constructor
  · intro x hx
    by_cases hxc : x = c
    · subst hxc
      unfold insertG
      cases hn : l[i + 2]? with
      | none => simp only; rw [upd_ne hcpc, hGc]
      | some n' => simp only; rw [upd_ne (hcn n' hn), upd_ne hcpc, hGc]
    · have hx' : x ∈ l.erase c := (List.mem_erase_of_ne hxc).mpr hx
      obtain ⟨h1, h2⟩ := nb_erase hnd hc hpc hx'
      have hnext_pc : nextOf l pc = some c := by rw [nextOf_getElem? hnd hpc]; exact hc
      have hprev_n : ∀ n', l[i + 2]? = some n' → prevOf l n' = some c := fun n' hn' => by
        rw [prevOf_succ hnd hn']; exact hc
      unfold insertG
      cases hn : l[i + 2]? with
      | none =>
        simp only [hn] at h1 h2
        simp only [Option.some_ne_none, ↓reduceIte] at h2
        simp only
        by_cases hxpc : x = pc
        · subst hxpc
          rw [upd_self, hG x hx']
          simp only [nb, hnext_pc, h2]
        · rw [upd_ne hxpc, hG x hx']
          simp only [nb, h2]
          rw [h1, ite_eq_right hxpc]
      | some n' =>
        simp only [hn] at h1 h2
        simp only
        by_cases hxn : x = n'
        · subst hxn
          have hne := hpcn x hn
          rw [upd_self, upd_ne (Ne.symm hne), hG x hx']
          simp only [nb, hprev_n x hn]
          rw [h1, ite_eq_right (Ne.symm hne)]
        · rw [upd_ne hxn]
          have hsx : ¬ some x = some n' := fun h => hxn (Option.some.inj h)
          rw [ite_eq_right hsx] at h2
          by_cases hxpc : x = pc
          · subst hxpc
            rw [upd_self, hG x hx']
            simp only [nb, hnext_pc, h2]
          · rw [upd_ne hxpc, hG x hx']
            simp only [nb, h2]
            rw [h1, ite_eq_right hxpc]
  · intro x hx
    unfold insertG
    have hxpc : x ≠ pc := fun h => hx (h ▸ hpcm)
    cases hn : l[i + 2]? with
    | none => simp only; rw [upd_ne hxpc]
    | some n' =>
      have hxn : x ≠ n' := fun h => hx (h ▸ hnm n' hn)
      simp only; rw [upd_ne hxn, upd_ne hxpc]

end generic

end Theory
end github_com.anishathalye.porcupine
end Perennial
