/-
Pure lemmas for `hashMap.idsFromFreemaps`, `idsFromForwardMap`, `idsFromBackwardMap`: the
id each step adds is not in the set built so far (the spans visited before, and the ids of the
current span gathered so far), by the spans' disjointness.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.HashLemmas

@[expose] public section

set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt.internal.freelist

/-- The ids of the spans whose starts satisfy `V`. -/
def idsVis (sp : GMap w64 w64) (V : w64 → Prop) (x : w64) : Prop :=
  ∃ st, V st ∧ ∃ v, sp !! st = some v ∧ inRun st (v.toNat) x

/-- An id of the span at `cur`, not visited, is in no visited span. -/
theorem ids_fresh {sp : GMap w64 w64} (hok : spansOK sp) {cur v y : w64}
    (hkv : sp !! cur = some v) (hy : inRun cur (v.toNat) y) {V : w64 → Prop} (hV : ¬ V cur) :
    ¬ idsVis sp V y := by
  rintro ⟨st, hst, v', hv', hy'⟩
  have := span_disj hok hkv hv' hy hy'
  subst this; exact hV hst

/-- The ids `e, e-1, ..., e-(n-1)` (`idsFromBackwardMap`'s, from the span's end `e`). -/
def downIds (e : w64) (n : Nat) : List w64 := (List.range n).map (fun j : Nat => e - W64 (j : Int))

theorem downIds_succ (e : w64) (n : Nat) : downIds e (n + 1) = downIds e n ++ [e - W64 (n : Int)] := by
  simp [downIds, List.range_succ]

theorem runIds_mem_succ (k x : w64) (n : Nat) : x ∈ runIds k (n + 1) ↔ x ∈ runIds k n ∨ x = k + W64 (n : Int) := by
  rw [runIds_succ, List.mem_append, List.mem_singleton]

theorem downIds_mem_succ (e x : w64) (n : Nat) : x ∈ downIds e (n + 1) ↔ x ∈ downIds e n ∨ x = e - W64 (n : Int) := by
  rw [downIds_succ, List.mem_append, List.mem_singleton]

/-- The `n`-th id of a span (`n` below its size) is in it. -/
theorem ids_fwd_in {sp : GMap w64 w64} (hok : spansOK sp) {k v : w64} (hkv : sp !! k = some v)
    {n : Nat} (hn : n < v.toNat) : inRun k (v.toNat) (k + W64 (n : Int)) := by
  have := (hok.1 k v hkv).2
  unfold inRun; constructor <;> word

/-- ... and not among the `n` before it. -/
theorem ids_fwd_notin {sp : GMap w64 w64} (hok : spansOK sp) {k v : w64} (hkv : sp !! k = some v)
    {n : Nat} (hn : n < v.toNat) : k + W64 (n : Int) ∉ runIds k n := by
  have := (hok.1 k v hkv).2
  rw [mem_runIds (by word)]
  unfold inRun; intro ⟨_, h2⟩; word

/-- The `n`-th id from the end of a span (`n` below its size) is in it. -/
theorem ids_bwd_in {sp : GMap w64 w64} (hok : spansOK sp) {st v : w64} (hkv : sp !! st = some v)
    {n : Nat} (hn : n < v.toNat) : inRun st (v.toNat) (st + v - W64 1 - W64 (n : Int)) := by
  have := hok.1 st v hkv
  unfold inRun; constructor <;> word

theorem ids_bwd_notin {sp : GMap w64 w64} (hok : spansOK sp) {st v : w64} (hkv : sp !! st = some v)
    {n : Nat} (hn : n < v.toNat) : st + v - W64 1 - W64 (n : Int) ∉ downIds (st + v - W64 1) n := by
  have := hok.1 st v hkv
  unfold downIds
  simp only [List.mem_map, List.mem_range, not_exists, not_and]
  intro j hj e
  have : (st + v - W64 1 - W64 (j : Int)).toNat = (st + v - W64 1 - W64 (n : Int)).toNat := by rw [e]
  have h1 : (st + v - W64 1 - W64 (j : Int)).toNat = st.toNat + v.toNat - 1 - j := by word
  have h2 : (st + v - W64 1 - W64 (n : Int)).toNat = st.toNat + v.toNat - 1 - n := by word
  omega

/-- All the ids from the end of a span: the span's ids. -/
theorem downIds_all {sp : GMap w64 w64} (hok : spansOK sp) {st v : w64} (hkv : sp !! st = some v)
    (x : w64) : x ∈ downIds (st + v - W64 1) (v.toNat) ↔ inRun st (v.toNat) x := by
  have := hok.1 st v hkv
  unfold downIds inRun
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; constructor <;> word
  · rintro ⟨h1, h2⟩
    refine ⟨st.toNat + v.toNat - 1 - x.toNat, by omega, ?_⟩
    word

end bbolt
end EtcdGrove
end Perennial
