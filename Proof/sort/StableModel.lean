/-
A model of Go's `sort.Stable` (`zsortinterface.go`: `stable`, `insertionSort`, `symMerge`,
`rotate`, `swapRange`) as pure functions on the list a sorter holds, one per Go function or
loop, following the code step by step: `swapL` is a `Swap(i, j)`, `lessL` a `Less(i, j)`. The
specs of those functions (`Spec/sort/{swapRange,rotate,insertionSort,symMerge,stable}.lean`)
say the code computes the model; `StableCorrect.lean` proves what the model computes (the
stable sort of the list, `stableM_eq_mergeSort`).
-/
module

public import Perennial.Proof.slices.SortBasics

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace stableModel

variable {α : Type}

/-- `data.Swap(i, j)`: the sorter's `Swap` on the list (`sorterSpec`). -/
def swapL (l : List α) (i j : Nat) : List α :=
  match l[i]?, l[j]? with
  | some x, some y => (l.set i y).set j x
  | _, _ => l

/-- `data.Less(i, j)`. -/
def lessL (lt : α → α → Bool) (l : List α) (i j : Nat) : Bool :=
  match l[i]?, l[j]? with
  | some x, some y => lt x y
  | _, _ => false

/-- `swapRange(data, a, b, n)` after its first `k` iterations. -/
def swapRangeM (l : List α) (a b : Nat) : Nat → List α
  | 0 => l
  | k + 1 => swapL (swapRangeM l a b k) (a + k) (b + k)

/-- `rotate`'s loop, from its variables `i` and `j` (the guard `i = 0 ∨ j = 0` is never taken:
`rotate` is called with `a < m < b`). -/
def rotLoop (l : List α) (m : Nat) (i j : Nat) : List α :=
  if _h : i = 0 ∨ j = 0 then l
  else if i = j then swapRangeM l (m - i) m i
  else if _h2 : j < i then rotLoop (swapRangeM l (m - i) m j) m (i - j) j
  else rotLoop (swapRangeM l (m - i) (m + j - i) i) m i (j - i)
termination_by i + j
decreasing_by all_goals omega

/-- `rotate(data, a, m, b)`. -/
def rotateM (l : List α) (a m b : Nat) : List α := rotLoop l m (m - a) (b - m)

/-- `insertionSort`'s inner loop, from `j`. -/
def insInner (lt : α → α → Bool) (a : Nat) (j : Nat) (l : List α) : List α :=
  if h : a < j ∧ lessL lt l j (j - 1) = true then insInner lt a (j - 1) (swapL l j (j - 1))
  else l
termination_by j
decreasing_by omega

/-- `insertionSort`'s outer loop, from `i`. -/
def insOuter (lt : α → α → Bool) (a b : Nat) (i : Nat) (l : List α) : List α :=
  if h : i < b then insOuter lt a b (i + 1) (insInner lt a i l) else l
termination_by b - i

/-- `insertionSort(data, a, b)`. -/
def insertionSortM (lt : α → α → Bool) (l : List α) (a b : Nat) : List α :=
  insOuter lt a b (a + 1) l

/-- The binary searches of `symMerge`: from `[i, j)`, `i = h + 1` if `P h`, else `j = h`. -/
def bsearch (P : Nat → Bool) (i j : Nat) : Nat :=
  if h : i < j then
    if P ((i + j) / 2) then bsearch P ((i + j) / 2 + 1) j else bsearch P i ((i + j) / 2)
  else i
termination_by j - i
decreasing_by all_goals omega

/-- `for k := a; k < ...; k++ { data.Swap(k, k+1) }` after `c` iterations. -/
def upM (l : List α) (a : Nat) : Nat → List α
  | 0 => l
  | c + 1 => swapL (upM l a c) (a + c) (a + c + 1)

/-- `for k := m; k > ...; k-- { data.Swap(k, k-1) }` after `c` iterations. -/
def downM (l : List α) (m : Nat) : Nat → List α
  | 0 => l
  | c + 1 => swapL (downM l m c) (m - c) (m - c - 1)

/-- `symMerge(data, a, m, b)` (the guard `a < m ∧ m < b` is its precondition). -/
def symMergeM (lt : α → α → Bool) (l : List α) (a m b : Nat) : List α :=
  if hd : a < m ∧ m < b then
    if m - a = 1 then
      upM l a (bsearch (fun h => lessL lt l h a) m b - 1 - a)
    else if b - m = 1 then
      downM l m (m - bsearch (fun h => !lessL lt l m h) a m)
    else
      let start := bsearch (fun c => !lessL lt l ((a + b) / 2 + m - 1 - c) c)
        (if (a + b) / 2 < m then (a + b) / 2 + m - b else a)
        (if (a + b) / 2 < m then (a + b) / 2 else m)
      let l1 := if start < m ∧ m < (a + b) / 2 + m - start then
        rotateM l start m ((a + b) / 2 + m - start) else l
      let l2 := if a < start ∧ start < (a + b) / 2 then
        symMergeM lt l1 a start ((a + b) / 2) else l1
      if (a + b) / 2 < (a + b) / 2 + m - start ∧ (a + b) / 2 + m - start < b then
        symMergeM lt l2 ((a + b) / 2) ((a + b) / 2 + m - start) b else l2
  else l
termination_by b - a
decreasing_by all_goals omega

/-- `stable`'s first loop and the `insertionSort(data, a, n)` after it (blocks of 20). -/
def insPhase (lt : α → α → Bool) (n a : Nat) (l : List α) : List α :=
  if h : a + 20 ≤ n then insPhase lt n (a + 20) (insertionSortM lt l a (a + 20))
  else insertionSortM lt l a n
termination_by n - a

/-- One iteration of `stable`'s second loop (the merges at `blockSize = bs`), from `a`. -/
def mergeLevel (lt : α → α → Bool) (n bs a : Nat) (l : List α) : List α :=
  if h : 0 < bs ∧ a + 2 * bs ≤ n then
    mergeLevel lt n bs (a + 2 * bs) (symMergeM lt l a (a + bs) (a + 2 * bs))
  else if a + bs < n then symMergeM lt l a (a + bs) n else l
termination_by n - a

/-- `stable`'s second loop, from `blockSize = bs`. -/
def mergePhase (lt : α → α → Bool) (n bs : Nat) (l : List α) : List α :=
  if h : 0 < bs ∧ bs < n then mergePhase lt n (2 * bs) (mergeLevel lt n bs 0 l) else l
termination_by n - bs

/-- `stable(data, n)`. -/
def stableM (lt : α → α → Bool) (l : List α) (n : Nat) : List α :=
  mergePhase lt n 20 (insPhase lt n 0 l)

/-! ### Basic facts -/

theorem swapL_eq (l : List α) (i j : Nat) (x y : α) (hx : l[i]? = some x) (hy : l[j]? = some y) :
    swapL l i j = (l.set i y).set j x := by
  unfold swapL; rw [hx, hy]

theorem lessL_eq (lt : α → α → Bool) (l : List α) (i j : Nat) (x y : α) (hx : l[i]? = some x)
    (hy : l[j]? = some y) : lessL lt l i j = lt x y := by
  unfold lessL; rw [hx, hy]

@[simp] theorem swapL_length (l : List α) (i j : Nat) : (swapL l i j).length = l.length := by
  unfold swapL; split <;> simp

theorem swapL_getElem? (l : List α) (i j p : Nat) (hi : i < l.length) (hj : j < l.length) :
    (swapL l i j)[p]? = if p = j then l[i]? else if p = i then l[j]? else l[p]? := by
  rw [swapL_eq l i j l[i] l[j] (by simp [hi]) (by simp [hj])]
  rw [List.getElem?_set, List.getElem?_set]
  by_cases h1 : p = j
  · subst h1; simp [hi, hj]
  · by_cases h2 : p = i
    · subst h2; simp [hi, hj, Ne.symm h1, h1]
    · simp [Ne.symm h1, Ne.symm h2, h1, h2]

theorem swapL_perm (l : List α) (i j : Nat) : (swapL l i j).Perm l := by
  unfold swapL
  split
  · rename_i x y hx hy
    exact Perennial.Permutation_insert_swap l i j x y hx hy
  · exact List.Perm.refl _

theorem swapRangeM_length (l : List α) (a b k : Nat) : (swapRangeM l a b k).length = l.length := by
  induction k with
  | zero => rfl
  | succ k ih => simp [swapRangeM, ih]

theorem upM_length (l : List α) (a c : Nat) : (upM l a c).length = l.length := by
  induction c with
  | zero => rfl
  | succ c ih => simp [upM, ih]

theorem downM_length (l : List α) (m c : Nat) : (downM l m c).length = l.length := by
  induction c with
  | zero => rfl
  | succ c ih => simp [downM, ih]


theorem rotLoop_length (l : List α) (m i j : Nat) : (rotLoop l m i j).length = l.length := by
  induction h : i + j using Nat.strongRecOn generalizing l i j with
  | _ n ih =>
  unfold rotLoop
  split
  · rfl
  split
  · exact swapRangeM_length ..
  split
  · rw [ih (i - j + j) (by omega) _ _ _ rfl, swapRangeM_length]
  · rw [ih (i + (j - i)) (by omega) _ _ _ rfl, swapRangeM_length]

theorem rotateM_length (l : List α) (a m b : Nat) : (rotateM l a m b).length = l.length :=
  rotLoop_length ..

theorem symMergeM_length (lt : α → α → Bool) (l : List α) (a m b : Nat) :
    (symMergeM lt l a m b).length = l.length := by
  induction h : b - a using Nat.strongRecOn generalizing l a m b with
  | _ n ih =>
  have hrec : ∀ (l' : List α) (a' m' b' : Nat), b' - a' < n →
      (symMergeM lt l' a' m' b').length = l'.length := fun l' a' m' b' hn =>
    ih (b' - a') hn l' a' m' b' rfl
  unfold symMergeM
  repeat' split
  all_goals simp (disch := omega) only [apply_ite List.length, hrec, rotateM_length, upM_length,
    downM_length, ite_self]

theorem insInner_length (lt : α → α → Bool) (a j : Nat) (l : List α) :
    (insInner lt a j l).length = l.length := by
  induction j generalizing l with
  | zero => unfold insInner; rw [dif_neg (by omega)]
  | succ j ih =>
    unfold insInner
    split
    · rw [show j + 1 - 1 = j by omega, ih, swapL_length]
    · rfl

theorem insOuter_length (lt : α → α → Bool) (a b i : Nat) (l : List α) :
    (insOuter lt a b i l).length = l.length := by
  induction h : b - i using Nat.strongRecOn generalizing i l with
  | _ n ih =>
  unfold insOuter
  split
  · rw [ih (b - (i + 1)) (by omega) _ _ rfl, insInner_length]
  · rfl

theorem insertionSortM_length (lt : α → α → Bool) (l : List α) (a b : Nat) :
    (insertionSortM lt l a b).length = l.length := insOuter_length ..

end stableModel
end EtcdGrove
end Perennial
