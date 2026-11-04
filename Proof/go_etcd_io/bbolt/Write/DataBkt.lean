/-
U7k (`notes/bbolt-proof-plan.md`): `CreateBucket`'s and `DeleteBucket`'s data, `wtxData_create`
and `wtxData_drop` (`Model/LTree`), as primed copies: the writer's data at a name is that name's
`bktData` (`GMap.ofList` keeps the first binding, as `bktData`'s `find?`), so the data is
determined by `bktData` pointwise.
-/
module

public import Proof.go_etcd_io.bbolt.Model.LTree

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section databkt
variable [GooseExts]

/-- `GMap.ofList` keeps a key's first binding. -/
theorem ofList_lookup_find {K V : Type} [DecidableEq K] (l : List (K × V)) (k : K) :
    (GMap.ofList l) !! k = (l.find? fun e => decide (e.1 = k)).map Prod.snd := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨a1, a2⟩ := a
    simp only [GMap.ofList, GMap.lookup_insert_eq_iff, List.find?_cons]
    by_cases h : a1 = k
    · simp [h]
    · simp [h, ih]

/-- The writer's data at `n` is `n`'s `bktData`. -/
theorem wtxData_lookup (X : WX) (n : GoString) : (wtxData X) !! n = bktData X n := by
  unfold wtxData bktData
  rw [ofList_lookup_find, List.find?_map]
  cases h : (rootEnts X).find? (fun e => decide (e.1 = n)) with
  | none => simp [Function.comp_def, h]
  | some e =>
    have he := List.find?_some h
    simp only [decide_eq_true_eq] at he
    simp only [Option.map_some, Function.comp_def]
    rw [h]; simp [he]

theorem wtxData_create' (X X' : WX) (n : GoString) (hok : wOK X) (hok' : wOK X')
    (hnew : (wtxData X) !! n = none)
    (hn : bktData X' n = some ∅)
    (hnames : ∀ n', n' ≠ n → bktData X' n' = bktData X n') :
    wtxData X' = (wtxData X).insert n ∅ := by
  apply GMap.ext; intro m
  show (wtxData X') !! m = (GMap.insert n ∅ (wtxData X)) !! m
  rw [GMap.lookup_insert_eq_iff, wtxData_lookup, wtxData_lookup]
  by_cases h : n = m
  · subst h; simp [hn]
  · simp [h, hnames m (Ne.symm h)]

theorem wtxData_drop' (X X' : WX) (n : GoString) (hok : wOK X) (hok' : wOK X')
    (hn : bktData X' n = none)
    (hnames : ∀ n', n' ≠ n → bktData X' n' = bktData X n') :
    wtxData X' = (wtxData X).delete n := by
  apply GMap.ext; intro m
  show (wtxData X') !! m = (GMap.delete n (wtxData X)) !! m
  rw [GMap.lookup_delete_iff, wtxData_lookup, wtxData_lookup]
  by_cases h : n = m
  · subst h; simp [hn]
  · simp [h, hnames m (Ne.symm h)]

end databkt

end Write

end bbolt
end EtcdGrove
end Perennial
