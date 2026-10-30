/-
The order of keys (`bytes.Compare`, `go.GoStringLt`) and the binary searches of a cursor:
in a well-formed page, whose keys increase, the predicate a cursor gives `sort.Search`
("key `i` is not below the searched key") is monotone.
-/
module

public import Proof.go_etcd_io.bbolt.PageModel
public import Perennial.Proof.bytes
public import Perennial.Proof.sort_proof.search

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace bbolt

theorem goStringLt_trans {a b c : List w8} (h1 : go.GoStringLt a b) (h2 : go.GoStringLt b c) :
    go.GoStringLt a c :=
  List.lex_trans (fun h h' => Int.lt_trans h h') h1 h2

theorem compareResult_eq_neg1 (a b : List w8) :
    bytes.compareResult a b = W64 (-1) ↔ go.GoStringLt a b := by
  unfold bytes.compareResult
  constructor
  · intro h
    by_cases hl : go.GoStringLt a b
    · exact hl
    · simp only [hl, ↓reduceIte] at h; split at h <;> exact absurd h (by decide)
  · intro h; simp only [h, ↓reduceIte]

/-- Leaf key `i` of `pg` is not below `key` (`sort.Search`'s predicate in `nsearch`). -/
def leafGE (pg key : List w8) (i : Int) : Bool :=
  decide (bytes.compareResult (leafKey pg i.toNat) key ≠ W64 (-1))

/-- Branch key `i` of `pg` is not below `key` (`searchPage`'s predicate). -/
def branchGE (pg key : List w8) (i : Int) : Bool :=
  decide (bytes.compareResult (branchKey pg i.toNat) key ≠ W64 (-1))

theorem leafGE_mono (pg key : List w8)
    (hs : ∀ i j, i < j → j < pageCount pg → go.GoStringLt (leafKey pg i) (leafKey pg j)) :
    sort.IsMonoPred (leafGE pg key) (pageCount pg) := by
  intro i j ⟨hi, hij, hj⟩ hfi
  simp only [leafGE, decide_eq_true_eq, ne_eq, compareResult_eq_neg1] at hfi ⊢
  intro hlt
  exact hfi (goStringLt_trans (hs i.toNat j.toNat (by omega) (by omega)) hlt)

theorem branchGE_mono (pg key : List w8)
    (hs : ∀ i j, i < j → j < pageCount pg → go.GoStringLt (branchKey pg i) (branchKey pg j)) :
    sort.IsMonoPred (branchGE pg key) (pageCount pg) := by
  intro i j ⟨hi, hij, hj⟩ hfi
  simp only [branchGE, decide_eq_true_eq, ne_eq, compareResult_eq_neg1] at hfi ⊢
  intro hlt
  exact hfi (goStringLt_trans (hs i.toNat j.toNat (by omega) (by omega)) hlt)

end bbolt
end EtcdGrove
end Perennial
