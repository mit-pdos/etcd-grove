/-
**`RoleGrantPermission`'s pure lemmas** (the auth plan's S4d, 2026-10-24). Lean-first (no Rocq
counterpart). The role record's permissions on the wire (`RoleRec.perms`) and the model's
(`RoleRec.toRole`, those of a known type): an entry overwritten in place changes the model's list
by one entry set, inserted or dropped (`toRole_set_*`); the order `permSlice.Less` sorts by
(`bytes.Compare` of the keys) is a strict weak order on the pairs the sorter holds
(`StrictWeakOrder_keyLt`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Steps
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

theorem zip_set_left {α β : Type} (l : List α) (l' : List β) (i : Nat) (a : α) (b : β)
    (ha : l[i]? = some a) : (l.zip l').set i (a, b) = l.zip (l'.set i b) := by
  have hil : i < l.length := (List.getElem?_eq_some_iff.mp ha).1
  have hia : l[i] = a := (List.getElem?_eq_some_iff.mp ha).2
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_set, List.getElem_zip]
    by_cases hn : i = n
    · subst hn; simp [hia]
    · simp [hn]

theorem mem_filterMap_set {α β : Type} (f : α → Option β) (l : List α) (i : Nat) (x : α) (p : β)
    (h : p ∈ (l.set i x).filterMap f) : p ∈ l.filterMap f ∨ f x = some p := by
  rw [List.mem_filterMap] at h
  obtain ⟨a, ha, hfa⟩ := h
  rcases List.mem_or_eq_of_mem_set ha with h' | h'
  · left; exact List.mem_filterMap.mpr ⟨a, h', hfa⟩
  · subst h'; right; exact hfa

/-- **The update case**: the entry at `idx` of the same key and range end as `w` gets `w`. -/
theorem grant_update (name : GoString) (st0 : AuthState) (rr : RoleRec) (ps : Role) (idx : Nat)
    (q w : PermW) (hlook : st0.roles !! name = some ps) (hrr : rr.toRole = ps)
    (hq : rr.perms[idx]? = some q) (hk : q.key = w.key) (hre : q.rangeEnd = w.rangeEnd)
    (hvalid : rangeValid w.key w.rangeEnd) :
    roleGrantPermissionR name (some w) st0
      (.next (bump (putRole st0 name ({ rr with perms := rr.perms.set idx w } : RoleRec).toRole))) := by
  have hlt : idx < rr.perms.length := (List.getElem?_eq_some_iff.mp hq).1
  have hqi : rr.perms[idx] = q := (List.getElem?_eq_some_iff.mp hq).2
  simp only [roleGrantPermissionR, hvalid, not_true_eq_false, ↓reduceIte, hlook]
  unfold RoleRec.toRole at hrr ⊢
  simp only
  cases hw : permOfWire w with
  | some perm =>
    cases hq' : permOfWire q with
    | some p =>
      obtain ⟨i, hi, hset⟩ := toRole_set_known rr.perms idx hlt w p perm (by rw [hqi]; exact hq') hw
      refine ⟨_, Or.inr ⟨i, p, by rw [← hrr]; exact hi, ?_, by rw [hset, hrr]⟩, rfl⟩
      obtain ⟨h1, h2⟩ := permOfWire_key q p hq'
      exact ⟨h1.trans hk, h2.trans hre⟩
    | none =>
      refine ⟨_, Or.inl ?_, rfl⟩
      rw [← hrr]
      exact toRole_set_unknown_known rr.perms idx hlt w perm (by rw [hqi]; exact hq') hw
  | none =>
    refine ⟨_, _, ?_, List.Perm.refl _, rfl⟩
    rw [← hrr]
    exact toRole_set_unknown rr.perms idx hlt w hw

/-- **The insert case**: `w` appended and the pairs permuted (sorted). -/
theorem grant_insert (name : GoString) (st0 : AuthState) (rr : RoleRec) (ps : Role) (w : PermW)
    (locs : List Loc) (np : Loc) (xs' : List (Loc × PermW))
    (hlook : st0.roles !! name = some ps) (hrr : rr.toRole = ps)
    (hzl : locs.length = rr.perms.length)
    (hperm : (locs.zip rr.perms ++ [(np, w)]).Perm xs')
    (hvalid : rangeValid w.key w.rangeEnd) :
    roleGrantPermissionR name (some w) st0
      (.next (bump (putRole st0 name ({ rr with perms := xs'.map Prod.snd } : RoleRec).toRole))) := by
  have hsnd : (locs.zip rr.perms ++ [(np, w)]).map Prod.snd = rr.perms ++ [w] := by
    rw [List.map_append, List.map_snd_zip (by omega)]; rfl
  have hp : (xs'.map Prod.snd).filterMap permOfWire |>.Perm ((rr.perms ++ [w]).filterMap permOfWire) := by
    rw [← hsnd]; exact ((hperm.map Prod.snd).filterMap permOfWire).symm
  simp only [roleGrantPermissionR, hvalid, not_true_eq_false, ↓reduceIte, hlook]
  unfold RoleRec.toRole at hrr ⊢
  simp only
  rw [List.filterMap_append] at hp
  cases hw : permOfWire w with
  | some perm =>
    refine ⟨_, Or.inl ?_, rfl⟩
    rw [← hrr]; simpa [hw] using hp
  | none =>
    refine ⟨_, _, List.Sublist.refl _, ?_, rfl⟩
    rw [← hrr]; simpa [hw] using hp

/-- The keys of the role after the grant are non-empty, if the role's were and `w`'s is. -/
theorem grant_keys_update (rr : RoleRec) (idx : Nat) (w : PermW) (hw : w.key ≠ [])
    (hold : ∀ p ∈ rr.toRole, p.key ≠ []) :
    ∀ p ∈ ({ rr with perms := rr.perms.set idx w } : RoleRec).toRole, p.key ≠ [] := by
  intro p hp
  unfold RoleRec.toRole at hp hold
  rcases mem_filterMap_set permOfWire rr.perms idx w p hp with h | h
  · exact hold p h
  · rw [(permOfWire_key w p h).1]; exact hw

theorem grant_keys_insert (rr : RoleRec) (w : PermW) (locs : List Loc) (np : Loc)
    (xs' : List (Loc × PermW)) (hzl : locs.length = rr.perms.length)
    (hperm : (locs.zip rr.perms ++ [(np, w)]).Perm xs') (hw : w.key ≠ [])
    (hold : ∀ p ∈ rr.toRole, p.key ≠ []) :
    ∀ p ∈ ({ rr with perms := xs'.map Prod.snd } : RoleRec).toRole, p.key ≠ [] := by
  intro p hp
  unfold RoleRec.toRole at hp hold
  simp only at hp
  have hsnd : (locs.zip rr.perms ++ [(np, w)]).map Prod.snd = rr.perms ++ [w] := by
    rw [List.map_append, List.map_snd_zip (by omega)]; rfl
  have hp' := ((hperm.map Prod.snd).filterMap permOfWire).symm.subset hp
  rw [hsnd, List.filterMap_append] at hp'
  rcases List.mem_append.mp hp' with h | h
  · exact hold p h
  · simp only [List.filterMap_cons, List.filterMap_nil] at h
    cases hw' : permOfWire w with
    | none => rw [hw'] at h; simp at h
    | some q =>
      rw [hw'] at h; simp at h; subst h
      rw [(permOfWire_key w _ hw').1]; exact hw

end auth
end EtcdGrove
end Perennial
