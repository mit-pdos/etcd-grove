/-
The spill's data lemma (U9c, `notes/bbolt-proof-plan.md`; pure): `Model/LTree`'s `treeData_spill`,
proved. `GMap.ofList` keeps a key's first binding, so both sides look a name up by its first entry
(the tree's root entries, the writer's root entries); the premises say the names agree and each
tree entry's bucket is the writer's bucket of that name. Neither `wOKR` nor `treeOK` is needed.
-/
module

public import Proof.go_etcd_io.bbolt.Model.LTree

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section tds
variable [GooseExts]

/-- A lookup in `GMap.ofList` is the list's first binding of the key. -/
theorem ofList_lookup_find {K V : Type} [DecidableEq K] (L : List (K × V)) (k : K) :
    GMap.ofList L !! k = (L.find? fun e => decide (e.1 = k)).map Prod.snd := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    obtain ⟨k', v'⟩ := e
    show (GMap.ofList L).insert k' v' !! k = _
    by_cases h : k' = k
    · subst h; rw [GMap.lookup_insert]; simp
    · rw [GMap.lookup_insert_ne _ _ h, ih]; simp [h]

theorem find?_map_fst {α β γ : Type} [DecidableEq α] (L : List (α × β)) (f : α × β → γ) (k : α) :
    ((L.map fun e => (e.1, f e)).find? fun e => decide (e.1 = k)) =
      (L.find? fun e => decide (e.1 = k)).map fun e => (e.1, f e) := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    by_cases h : e.1 = k
    · simp [h]
    · simp only [List.map_cons, List.find?_cons, h, decide_false]; exact ih

theorem find?_none_of_fst {α β γ : Type} [DecidableEq α] (L1 : List (α × β)) (L2 : List (α × γ))
    (h : L1.map Prod.fst = L2.map Prod.fst) (k : α)
    (h1 : (L1.find? fun e => decide (e.1 = k)) = none) :
    (L2.find? fun e => decide (e.1 = k)) = none := by
  induction L1 generalizing L2 with
  | nil => cases L2 <;> simp_all
  | cons a L1 ih =>
    cases L2 with
    | nil => simp at h
    | cons b L2 =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.find?_cons] at h1 ⊢
      by_cases ha : a.1 = k
      · simp [ha] at h1
      · rw [h.1] at ha
        have ha' : ¬ a.1 = k := by rw [h.1]; exact ha
        simp only [ha, ha', decide_false] at h1 ⊢
        exact ih L2 h.2 h1

/-- **The spilled tree holds the writer's data** (`Model/LTree`'s `treeData_spill`). -/
theorem treeData_spill' (X : WX) (C' : CommitSt)
    (hnames : (treeEntries C'.pages C'.root).map Prod.fst = (rootEnts X).map Prod.fst)
    (hbkts : ∀ n v, (n, v) ∈ treeEntries C'.pages C'.root →
      some (bktOfPage C'.pages v) = bktData X n) :
    treeData C' = wtxData X := by
  apply GMap.ext; intro n
  show GMap.ofList _ !! n = GMap.ofList _ !! n
  rw [ofList_lookup_find, ofList_lookup_find, find?_map_fst, find?_map_fst]
  cases ht : (treeEntries C'.pages C'.root).find? fun e => decide (e.1 = n) with
  | some e =>
    have hm := List.mem_of_find?_eq_some ht
    have he : e.1 = n := by simpa using List.find?_some ht
    obtain ⟨n0, v⟩ := e
    simp only at he; subst he
    have hb := hbkts n0 v hm
    unfold bktData at hb
    simp only [Option.map_some]
    rw [hb]
    cases hr : (rootEnts X).find? fun e => decide (e.1 = n0) with
    | none => rfl
    | some e' =>
      have he' : e'.1 = n0 := by simpa using List.find?_some hr
      simp [he']
  | none =>
    rw [find?_none_of_fst _ _ hnames n ht]; rfl

/-- `Model/LTree`'s statement, with its unused premises. -/
theorem treeData_spill_of (X : WX) (C' : CommitSt) (_hok : wOKR X) (_htree : treeOK C')
    (hnames : (treeEntries C'.pages C'.root).map Prod.fst = (rootEnts X).map Prod.fst)
    (hbkts : ∀ n v, (n, v) ∈ treeEntries C'.pages C'.root →
      some (bktOfPage C'.pages v) = bktData X n) :
    treeData C' = wtxData X := treeData_spill' X C' hnames hbkts

end tds

end bbolt
end EtcdGrove
end Perennial
