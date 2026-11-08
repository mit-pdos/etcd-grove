/-
Lean-first (no Rocq counterpart).

# The driver's list model, pure (stage 7e-3a of `notes/k8s-7e-scope.md`)

`mlist`'s loop (`examples/k8s/etcd3/k8setcd3.go`, the Model's `list`, `model.go:394-460`), on an
abstract item list, before the Go records it will be stated on (7e-3b, after 7e-0's translation):
the keys in scope (`inScope`: exact if not recursive, else under the key with the `/` boundary),
in order; the number of them (`total`); the first `limit` matching items (all if `limit = 0`);
and `hasMore`, set by any key in scope after the `limit`-th match, matching or not (etcd3's
`limitReached` at the next key: `foldl_full`). Proved so far: `loop_total`, `loop_nolimit`,
`loop_items_le`, `foldl_full`. And the history of stores (`hist[R-1]` the store at revision `R`),
which only revision bumps extend (`histOk_advance`). The full characterization of the items and
`hasMore` (the first `limit` matches; `hasMore` iff a key follows the `limit`-th match) comes with
7e-3b, on the Go records.
-/
module

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3
namespace ListModel

variable {α O : Type} [DecidableEq α]

/-! ## Scope -/

/-- A key without a trailing separator. -/
def trimSep (sep : α) (key : List α) : List α :=
  if key.getLast? = some sep then key.dropLast else key

/-- `keyInScope`: `k` is selected by a list of `key` (exact if not recursive; under
`trimSep key ++ [sep]` if recursive, so `/a` selects `/a/x`, not `/ab`). -/
def inScope (sep : α) (key : List α) (recursive : Bool) (k : List α) : Bool :=
  if recursive then (trimSep sep key ++ [sep]).isPrefixOf k else decide (k = key)

/-! ## The loop -/

/-- The loop's state: the items so far (reversed), the last matching key, `hasMore`, `total`. -/
structure LState (α O : Type) where
  items : List O
  last : Option (List α)
  more : Bool
  total : Nat

/-- One iteration of `mlist`'s loop on an item `(k, o)` already in scope. -/
def lstep (sel : O → Bool) (limit : Nat) (s : LState α O) (ko : List α × O) : LState α O :=
  let s := { s with total := s.total + 1 }
  if 0 < limit ∧ limit ≤ s.items.length then { s with more := true }
  else if sel ko.2 then { s with items := ko.2 :: s.items, last := some ko.1 } else s

/-- `mlist`'s loop on the items in scope `sc` (in key order): items in order, the last key,
`hasMore`, `total`. -/
def loop (sel : O → Bool) (limit : Nat) (sc : List (List α × O)) : LState α O :=
  sc.foldl (lstep sel limit) ⟨[], none, false, 0⟩

/-- The items in scope of a store's item list. -/
def inScopeItems (sep : α) (key : List α) (recursive : Bool) (its : List (List α × O)) :
    List (List α × O) :=
  its.filter fun ko => inScope sep key recursive ko.1

/-- The list's answer on a store's items: the loop on the items in scope. -/
def mlistL (sep : α) (key : List α) (recursive : Bool) (sel : O → Bool) (limit : Nat)
    (its : List (List α × O)) : LState α O :=
  loop sel limit (inScopeItems sep key recursive its)

/-! ## What the loop computes -/

/-- The loop from a state: `total` counts every item. -/
theorem foldl_total (sel : O → Bool) (limit : Nat) :
    ∀ (sc : List (List α × O)) (s : LState α O),
      (sc.foldl (lstep sel limit) s).total = s.total + sc.length
  | [], s => by simp
  | ko :: sc, s => by
    rw [List.foldl_cons, foldl_total sel limit sc]
    simp only [lstep, List.length_cons]
    split <;> (try split) <;> simp <;> omega

theorem loop_total (sel : O → Bool) (limit : Nat) (sc : List (List α × O)) :
    (loop sel limit sc).total = sc.length := by
  simp [loop, foldl_total]

/-- With no limit, the loop takes every matching item and never has more. -/
theorem foldl_nolimit (sel : O → Bool) :
    ∀ (sc : List (List α × O)) (s : LState α O),
      (sc.foldl (lstep sel 0) s).items = (sc.filter (sel ·.2)).reverse.map Prod.snd ++ s.items ∧
      (sc.foldl (lstep sel 0) s).more = s.more
  | [], s => by simp
  | ko :: sc, s => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := foldl_nolimit sel sc (lstep sel 0 s ko)
    rw [h1, h2]
    by_cases hs : sel ko.2 <;> simp [lstep, hs]

theorem loop_nolimit (sel : O → Bool) (sc : List (List α × O)) :
    (loop sel 0 sc).items.reverse = (sc.filter (sel ·.2)).map Prod.snd ∧
      (loop sel 0 sc).more = false := by
  obtain ⟨h1, h2⟩ := foldl_nolimit sel sc ⟨[], none, false, 0⟩
  simp only [loop, h1, h2, List.append_nil, List.reverse_reverse, List.map_reverse, and_true]

/-- The items never exceed a positive limit. -/
theorem foldl_items_le (sel : O → Bool) (limit : Nat) (hl : 0 < limit) :
    ∀ (sc : List (List α × O)) (s : LState α O), s.items.length ≤ limit →
      (sc.foldl (lstep sel limit) s).items.length ≤ limit
  | [], s, h => by simpa using h
  | ko :: sc, s, h => by
    rw [List.foldl_cons]
    apply foldl_items_le sel limit hl sc
    simp only [lstep]
    split
    · simpa using h
    · split
      · simp only [List.length_cons]; omega
      · simpa using h

theorem loop_items_le (sel : O → Bool) (limit : Nat) (hl : 0 < limit)
    (sc : List (List α × O)) : (loop sel limit sc).items.length ≤ limit :=
  foldl_items_le sel limit hl sc _ (by simp)

/-- Once the limit is reached, the items stay and `hasMore` is set by any further item. -/
theorem foldl_full (sel : O → Bool) (limit : Nat) (hl : 0 < limit) :
    ∀ (sc : List (List α × O)) (s : LState α O), limit ≤ s.items.length →
      (sc.foldl (lstep sel limit) s).items = s.items ∧
      (sc.foldl (lstep sel limit) s).more = (s.more || !sc.isEmpty)
  | [], s, _ => by simp
  | ko :: sc, s, h => by
    rw [List.foldl_cons]
    have hs : lstep sel limit s ko = { s with total := s.total + 1, more := true } := by
      simp only [lstep]; simp [hl, h]
    rw [hs]
    obtain ⟨h1, h2⟩ := foldl_full sel limit hl sc { s with total := s.total + 1, more := true } h
    rw [h1, h2]
    simp

/-! ## The history -/

/-- A history fits a store at revision `rv`: one store per revision `1..rv`, the last the
store itself. -/
def HistOk {S : Type} (rvOf : S → Nat) (hist : List S) (st : S) : Prop :=
  hist.length = rvOf st ∧ hist.getLast? = some st

/-- `advance`: the history grows by the new store iff the revision does. -/
def advanceH {S : Type} (rvOf : S → Nat) (hist : List S) (st st' : S) : List S :=
  if rvOf st' = rvOf st then hist else hist ++ [st']

/-- A step that keeps the revision keeps the store (the model's writes that do not bump the
revision leave the store unchanged), and one that bumps it bumps it by one: the history stays
fitted. -/
theorem histOk_advance {S : Type} (rvOf : S → Nat) (hist : List S) (st st' : S)
    (h : HistOk rvOf hist st)
    (hstep : (rvOf st' = rvOf st ∧ st' = st) ∨ rvOf st' = rvOf st + 1) :
    HistOk rvOf (advanceH rvOf hist st st') st' := by
  obtain ⟨hl, hlast⟩ := h
  unfold advanceH
  rcases hstep with ⟨hrv, rfl⟩ | hrv
  · simp only [ite_true]; exact ⟨hl, hlast⟩
  · simp only [show ¬ rvOf st' = rvOf st by omega, ite_false]
    exact ⟨by simp [hl, hrv], by simp⟩

end ListModel
end k8s_etcd3
end EtcdGrove
end Perennial
