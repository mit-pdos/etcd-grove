/-
**`RoleGrantPermission`'s pure lemmas** (the auth plan's S4d, 2026-10-24). Lean-first (no Rocq
counterpart). The role record's permissions on the wire (`RoleRec.perms`) and the model's
(`RoleRec.toRole`, those of a known type): an entry overwritten in place changes the model's list
by one entry set, inserted or dropped (`toRole_set_*`); the order `permSlice.Less` sorts by
(`bytes.Compare` of the keys) is a strict weak order on the pairs the sorter holds
(`StrictWeakOrder_keyLt`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Buckets
public import Perennial.Proof.slices.SortBasics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

/-- A strict weak order pulled back along a function. -/
theorem strictWeakOrder_comap {A B : Type} (g : A → B) (R : B → B → Prop)
    (h : slices.StrictWeakOrder R) : slices.StrictWeakOrder (fun x y => R (g x) (g y)) where
  strict_weak_order_irrefl x := h.strict_weak_order_irrefl (g x)
  strict_weak_order_trans x y z := h.strict_weak_order_trans (g x) (g y) (g z)
  strict_weak_order_equiv :=
    { refl := fun x => h.strict_weak_order_equiv.refl (g x)
      symm := fun hxy => h.strict_weak_order_equiv.symm hxy
      trans := fun hxy hyz => h.strict_weak_order_equiv.trans hxy hyz }

/-- The sorter's order on (message, wire permission) pairs: the keys' (`permSlice.Less`). -/
def keyLt (a b : Loc × PermW) : Prop := go.GoStringLt a.2.key b.2.key

theorem StrictWeakOrder_keyLt : slices.StrictWeakOrder keyLt :=
  strictWeakOrder_comap (fun a : Loc × PermW => a.2.key) go.GoStringLt slices.StrictWeakOrder_goStringLt

/-- `l` split at `i`, the entry there named. -/
theorem list_split {α : Type} (l : List α) (i : Nat) (h : i < l.length) :
    ∃ a b : List α, l = a ++ l[i] :: b ∧ a.length = i ∧
      ∀ x : α, l.set i x = a ++ x :: b := by
  refine ⟨l.take i, l.drop (i + 1), ?_, by simp; omega, ?_⟩
  · conv => lhs; rw [← List.take_append_drop i l]
    rw [List.drop_eq_getElem_cons h]
  · intro x
    rw [List.set_eq_take_append_cons_drop]; simp [h]

/-- An entry of a known type overwritten by one of a known type: the model's list with the entry
at the model's index set. -/
theorem toRole_set_known (l : List PermW) (idx : Nat) (h : idx < l.length) (w' : PermW)
    (p p' : Perm) (hp : permOfWire l[idx] = some p) (hp' : permOfWire w' = some p') :
    ∃ i, (l.filterMap permOfWire)[i]? = some p ∧
      (l.set idx w').filterMap permOfWire = (l.filterMap permOfWire).set i p' := by
  obtain ⟨a, b, hl, -, hset⟩ := list_split l idx h
  rw [hset]
  generalize l[idx] = x at hp hl
  subst hl
  refine ⟨(a.filterMap permOfWire).length, ?_, ?_⟩
  · simp [List.filterMap_append, hp]
  · simp [List.filterMap_append, hp, hp']

/-- An entry of an unknown type overwritten by one of a known type: the model's list with it
added. -/
theorem toRole_set_unknown_known (l : List PermW) (idx : Nat) (h : idx < l.length) (w' : PermW)
    (p' : Perm) (hp : permOfWire l[idx] = none) (hp' : permOfWire w' = some p') :
    ((l.set idx w').filterMap permOfWire).Perm (l.filterMap permOfWire ++ [p']) := by
  obtain ⟨a, b, hl, -, hset⟩ := list_split l idx h
  rw [hset]
  generalize l[idx] = x at hp hl
  subst hl
  simp only [List.filterMap_append, List.filterMap_cons, hp, hp', List.append_assoc]
  exact List.Perm.append_left _ (List.perm_append_comm (l₁ := [p']))

/-- An entry overwritten by one of an unknown type: the model's list loses at most it. -/
theorem toRole_set_unknown (l : List PermW) (idx : Nat) (h : idx < l.length) (w' : PermW)
    (hp' : permOfWire w' = none) :
    ((l.set idx w').filterMap permOfWire).Sublist (l.filterMap permOfWire) := by
  obtain ⟨a, b, hl, -, hset⟩ := list_split l idx h
  rw [hset]
  generalize l[idx] = x at hl
  subst hl
  simp only [List.filterMap_append, List.filterMap_cons, hp']
  apply List.Sublist.append (List.Sublist.refl _)
  cases permOfWire x with
  | none => exact List.Sublist.refl _
  | some _ => exact List.sublist_cons_self _ _

/-- `permOfWire` keeps the key and the range end. -/
theorem permOfWire_key (w : PermW) (p : Perm) (h : permOfWire w = some p) :
    p.key = w.key ∧ p.rangeEnd = w.rangeEnd := by
  unfold permOfWire at h
  by_cases h0 : w.ty = W32 0
  · rw [if_pos h0] at h; cases h; exact ⟨rfl, rfl⟩
  rw [if_neg h0] at h
  by_cases h1 : w.ty = W32 1
  · rw [if_pos h1] at h; cases h; exact ⟨rfl, rfl⟩
  rw [if_neg h1] at h
  by_cases h2 : w.ty = W32 2
  · rw [if_pos h2] at h; cases h; exact ⟨rfl, rfl⟩
  rw [if_neg h2] at h; cases h

end auth
end EtcdGrove
end Perennial
