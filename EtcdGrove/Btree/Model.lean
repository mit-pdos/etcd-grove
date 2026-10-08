/-
What google/btree's operations do to the abstract state, a list of entries `(v, k)` with
strictly increasing keys (`Sorted`): the reference semantics the specs are stated in.
-/
import EtcdGrove.Btree.Tree

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Classical

section model
variable {V K : Type} (lt : K → K → Prop)

/-- The item with key `k`. -/
def lookup (s : List (V × K)) (k : K) : Option V :=
  (s.find? (fun e => decide (e.2 = k))).map Prod.fst

/-- `ReplaceOrInsert`: the entry `e` replaces the one with its key, or goes where its key
belongs. -/
def insert : List (V × K) → V × K → List (V × K)
  | [], e => [e]
  | x :: xs, e =>
    if lt e.2 x.2 then e :: x :: xs
    else if e.2 = x.2 then e :: xs
    else x :: insert xs e

/-- `Delete`: drop the entry with key `k`. -/
def delete (s : List (V × K)) (k : K) : List (V × K) :=
  s.filter (fun e => decide (e.2 ≠ k))

/-- The keys an ascending iteration from `start` (inclusive) to `stop` (exclusive)
visits; `none` is no bound. -/
def ascIn (start stop : Option K) (k : K) : Prop :=
  (∀ a, start = some a → ¬ lt k a) ∧ (∀ b, stop = some b → lt k b)

/-- The keys a descending iteration from `start` (inclusive) down to `stop`
(exclusive) visits. -/
def descIn (start stop : Option K) (k : K) : Prop :=
  (∀ a, start = some a → ¬ lt a k) ∧ (∀ b, stop = some b → lt b k)

/-- The entries an ascending iteration visits, in order. -/
def ascRange (s : List (V × K)) (start stop : Option K) : List (V × K) :=
  s.filter (fun e => decide (ascIn lt start stop e.2))

/-- The entries a descending iteration visits, in order. -/
def descRange (s : List (V × K)) (start stop : Option K) : List (V × K) :=
  (s.filter (fun e => decide (descIn lt start stop e.2))).reverse

end model

end Btree
end EtcdGrove
end Perennial
