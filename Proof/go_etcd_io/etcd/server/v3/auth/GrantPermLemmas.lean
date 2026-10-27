/-
**`RoleGrantPermission`'s pure lemmas** (the auth plan's S4d, 2026-10-24). Lean-first (no Rocq
counterpart). The role record's permissions on the wire (`RoleRec.perms`) and the model's
(`RoleRec.toRole`, those of a known type): the order `permSlice.Less` sorts by (`bytes.Compare` of
the keys) is a strict weak order on the pairs the sorter holds (`StrictWeakOrder_keyLt`); the
fork's grant (E3z: the permissions off the range kept, the new one appended, sorted) gives a record
whose model role is the step's up to order (`grant_kept_perm`).
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


/-- A wire permission on the range `[key, rangeEnd)` (`bytes.Equal` on both). -/
def permWAt (key rangeEnd : GoString) (q : PermW) : Bool :=
  decide (q.key = key) && decide (q.rangeEnd = rangeEnd)

/-- Keeping the wire permissions off a range keeps the model's off it. -/
theorem filterMap_filter_permWAt (l : List PermW) (key rangeEnd : GoString) :
    (l.filter (fun q => !permWAt key rangeEnd q)).filterMap permOfWire =
      (l.filterMap permOfWire).filter (fun p => ¬ permAt key rangeEnd p) := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    simp only [List.filter_cons, List.filterMap_cons]
    cases hq : permOfWire q with
    | none =>
      cases permWAt key rangeEnd q <;> simp [List.filterMap_cons, hq, ih]
    | some p =>
      obtain ⟨hk, hre⟩ := permOfWire_key q p hq
      have hpw : permWAt key rangeEnd q = decide (permAt key rangeEnd p) := by
        simp [permWAt, permAt, hk, hre]
      by_cases hpa : permAt key rangeEnd p
      · simp [hpw, hpa, ih]
      · simp [hpw, hpa, List.filterMap_cons, hq, ih]

/-- **The grant's record matches the model's step**: the pairs kept (`kept`, whose permissions are
the record's off `w`'s range) with `w`'s appended, permuted (sorted), make a record whose model
role is `grantPerms ps w` up to order, when the record's was `ps`'s. -/
theorem grant_kept_perm (rr : RoleRec) (ps : Role) (w : PermW) (kept xs' : List (Loc × PermW))
    (np : Loc) (hrr : rr.toRole.Perm ps)
    (hkept : kept.map Prod.snd = rr.perms.filter (fun q => !permWAt w.key w.rangeEnd q))
    (hperm : (kept ++ [(np, w)]).Perm xs') :
    ({ rr with perms := xs'.map Prod.snd } : RoleRec).toRole.Perm (grantPerms ps w) := by
  unfold RoleRec.toRole at hrr ⊢
  simp only
  have h1 : (xs'.map Prod.snd).filterMap permOfWire |>.Perm
      (((kept ++ [(np, w)]).map Prod.snd).filterMap permOfWire) :=
    ((hperm.map Prod.snd).filterMap permOfWire).symm
  refine h1.trans ?_
  rw [List.map_append, hkept, List.filterMap_append, filterMap_filter_permWAt]
  unfold grantPerms
  refine List.Perm.append (hrr.filter _) ?_
  cases hw : permOfWire w <;> simp [hw]

/-- The keys of the role after the grant are non-empty, if the role's were and `w`'s is. -/
theorem grant_keys (ps : Role) (w : PermW) (hw : w.key ≠ []) (hold : ∀ p ∈ ps, p.key ≠ []) :
    ∀ p ∈ grantPerms ps w, p.key ≠ [] := by
  intro p hp
  unfold grantPerms at hp
  rcases List.mem_append.mp hp with h | h
  · exact hold p (List.mem_filter.mp h).1
  · cases hw' : permOfWire w with
    | none => rw [hw'] at h; simp at h
    | some q =>
      rw [hw'] at h; simp at h; subst h
      rw [(permOfWire_key w _ hw').1]; exact hw

end auth
end EtcdGrove
end Perennial
