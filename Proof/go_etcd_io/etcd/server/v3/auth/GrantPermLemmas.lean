/-
**`RoleGrantPermission`'s pure lemmas** (the auth plan's S4d, 2026-10-24; nomode X-a1, 2026-11-27).
Lean-first (no Rocq counterpart). The role record's permissions on the wire (`RoleRec.perms`) and
the model's (`RoleRec.toRole`, every one, nomode X-a4): the order `permSlice.Less` sorts by
(`bytes.Compare` of the keys, then of the range ends: `rangeLt`) is a strict total order on the
ranges, so a strict weak order on the pairs the sorter holds (`StrictWeakOrder_permWLt`); the
fork's grant (E3z: the permissions off the range kept, the new one appended, sorted) gives a record
whose model role is the step's, in order (`grant_kept_eq`), when the role's was sorted with
distinct ranges (`roleOut`).
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

/-- `permOfWire` keeps the key and the range end. -/
theorem permOfWire_key (w : PermW) :
    (permOfWire w).key = w.key ∧ (permOfWire w).rangeEnd = w.rangeEnd := ⟨rfl, rfl⟩

/-- `rangeLt` is irreflexive, transitive and total on (key, range end) pairs. -/
theorem rangeLt_irrefl (k e : GoString) : ¬ rangeLt k e k e := by
  rintro (h | ⟨-, h⟩) <;> exact go.goStringLt_irrefl _ h

theorem rangeLt_trans {k1 e1 k2 e2 k3 e3 : GoString} (h1 : rangeLt k1 e1 k2 e2)
    (h2 : rangeLt k2 e2 k3 e3) : rangeLt k1 e1 k3 e3 := by
  rcases h1 with h1 | ⟨h1k, h1⟩ <;> rcases h2 with h2 | ⟨h2k, h2⟩
  · exact Or.inl (go.goStringLt_trans h1 h2)
  · subst h2k; exact Or.inl h1
  · subst h1k; exact Or.inl h2
  · subst h1k; subst h2k; exact Or.inr ⟨rfl, go.goStringLt_trans h1 h2⟩

theorem rangeLt_eq_of_not {k e k' e' : GoString} (h1 : ¬ rangeLt k e k' e')
    (h2 : ¬ rangeLt k' e' k e) : k = k' ∧ e = e' := by
  have hk : k = k' := go.goStringLt_eq_of_not_lt (fun h => h1 (Or.inl h)) (fun h => h2 (Or.inl h))
  subst hk
  exact ⟨rfl, go.goStringLt_eq_of_not_lt (fun h => h1 (Or.inr ⟨rfl, h⟩))
    (fun h => h2 (Or.inr ⟨rfl, h⟩))⟩

/-- `rangeLt` on pairs. -/
def pairLt (a b : GoString × GoString) : Prop := rangeLt a.1 a.2 b.1 b.2

theorem StrictWeakOrder_pairLt : slices.StrictWeakOrder pairLt where
  strict_weak_order_irrefl a := rangeLt_irrefl a.1 a.2
  strict_weak_order_trans _ _ _ h1 h2 := rangeLt_trans h1 h2
  strict_weak_order_equiv :=
    { refl := fun a => ⟨rangeLt_irrefl a.1 a.2, rangeLt_irrefl a.1 a.2⟩
      symm := fun h => ⟨h.2, h.1⟩
      trans := fun {x y z} hxy hyz => by
        have e := rangeLt_eq_of_not hxy.1 hxy.2
        have hxy' : x = y := Prod.ext e.1 e.2
        subst hxy'; exact hyz }

/-- The sorter's order on (message, wire permission) pairs: `permSlice.Less`'s. -/
def permWLt (a b : Loc × PermW) : Prop := rangeLt a.2.key a.2.rangeEnd b.2.key b.2.rangeEnd

theorem StrictWeakOrder_permWLt : slices.StrictWeakOrder permWLt :=
  strictWeakOrder_comap (fun a : Loc × PermW => (a.2.key, a.2.rangeEnd)) pairLt StrictWeakOrder_pairLt

/-- `sort.Sort`'s postcondition as a `Pairwise`. -/
theorem pairwise_of_sorted {E : Type} (R : E → E → Prop) (xs : List E)
    (h : ∀ (i j : Nat) (xi xj : E), xs[i]? = some xi → xs[j]? = some xj → i < j → ¬ R xj xi) :
    xs.Pairwise (fun a b => ¬ R b a) :=
  List.pairwise_iff_getElem.2 fun i j hi hj hij =>
    h i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij

/-- Two permissions on different ranges. -/
def permNe (p q : Perm) : Prop := (p.key, p.rangeEnd) ≠ (q.key, q.rangeEnd)

theorem permNe_of_permLt {p q : Perm} (h : permLt p q) : permNe p q := by
  intro he
  simp only [Prod.mk.injEq] at he
  unfold permLt at h; rw [he.1, he.2] at h
  exact rangeLt_irrefl _ _ h

theorem permLt_of_not {p q : Perm} (h1 : ¬ permLt q p) (h2 : permNe p q) : permLt p q := by
  apply Classical.byContradiction
  intro h3
  obtain ⟨hk, he⟩ := rangeLt_eq_of_not h3 h1
  exact h2 (by rw [hk, he])

/-- Inserting into a sorted role a permission on a range of its own keeps it sorted. -/
theorem permInsert_sorted (p : Perm) : ∀ l : Role, l.Pairwise permLt → (∀ q ∈ l, permNe p q) →
    (permInsert p l).Pairwise permLt
  | [], _, _ => List.pairwise_singleton _ _
  | q :: qs, hl, hne => by
    simp only [permInsert]
    split
    · rename_i hpq
      refine List.Pairwise.cons ?_ hl
      intro r hr
      rcases List.mem_cons.mp hr with h | h
      · subst h; exact hpq
      · exact rangeLt_trans hpq (List.rel_of_pairwise_cons hl h)
    · rename_i hpq
      have hqp : permLt q p := permLt_of_not hpq (fun h => hne q List.mem_cons_self h.symm)
      refine List.Pairwise.cons ?_
        (permInsert_sorted p qs hl.of_cons (fun r hr => hne r (List.mem_cons_of_mem _ hr)))
      intro r hr
      rcases List.mem_cons.mp ((permInsert_perm p qs).subset hr) with h | h
      · subst h; exact hqp
      · exact List.rel_of_pairwise_cons hl h

/-- The role after a grant is sorted, if the role was. -/
theorem grantPerms_sorted (ps : Role) (w : PermW) (h : ps.Pairwise permLt) :
    (grantPerms ps w).Pairwise permLt := by
  unfold grantPerms
  refine permInsert_sorted _ _ (h.filter _) ?_
  intro q hq hpq
  simp only [Prod.mk.injEq] at hpq
  have hq' := of_decide_eq_true (List.mem_filter.mp hq).2
  exact hq' ⟨hpq.1.symm, hpq.2.symm⟩

/-- A wire permission on the range `[key, rangeEnd)` (`bytes.Equal` on both). -/
def permWAt (key rangeEnd : GoString) (q : PermW) : Bool :=
  decide (q.key = key) && decide (q.rangeEnd = rangeEnd)

/-- Keeping the wire permissions off a range keeps the model's off it. -/
theorem map_filter_permWAt (l : List PermW) (key rangeEnd : GoString) :
    (l.filter (fun q => !permWAt key rangeEnd q)).map permOfWire =
      (l.map permOfWire).filter (fun p => ¬ permAt key rangeEnd p) := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    simp only [List.filter_cons, List.map_cons]
    have hpw : permWAt key rangeEnd q = decide (permAt key rangeEnd (permOfWire q)) := by
      unfold permWAt
      by_cases h1 : q.key = key <;> by_cases h2 : q.rangeEnd = rangeEnd <;>
        simp [permAt, permOfWire, h1, h2]
    by_cases hpa : permAt key rangeEnd (permOfWire q)
    · simp [hpw, hpa, ih]
    · simp [hpw, hpa, ih]

/-- **The grant's record matches the model's step**: the pairs kept (`kept`, whose permissions are
the record's off `w`'s range) with `w`'s appended, permuted and sorted by `permWLt` (`sort.Sort`'s
postcondition), make a record whose model role is `grantPerms ps w`, when the record's was `ps`,
sorted (`permLt`). -/
theorem grant_kept_eq (rr : RoleRec) (ps : Role) (w : PermW) (kept xs' : List (Loc × PermW))
    (np : Loc) (hrr : rr.toRole = ps) (hps : ps.Pairwise permLt)
    (hkept : kept.map Prod.snd = rr.perms.filter (fun q => !permWAt w.key w.rangeEnd q))
    (hperm : (kept ++ [(np, w)]).Perm xs')
    (hsorted : ∀ (i j : Nat) (xi xj : Loc × PermW), xs'[i]? = some xi → xs'[j]? = some xj →
      i < j → ¬ permWLt xj xi) :
    ({ rr with perms := xs'.map Prod.snd } : RoleRec).toRole = grantPerms ps w := by
  -- the new record's model role is a permutation of the model's permissions kept, then `w`'s
  have h1 : ((xs'.map Prod.snd).map permOfWire).Perm
      (ps.filter (fun p => ¬ permAt w.key w.rangeEnd p) ++ [permOfWire w]) := by
    have h1 : (xs'.map Prod.snd).map permOfWire |>.Perm
        (((kept ++ [(np, w)]).map Prod.snd).map permOfWire) :=
      ((hperm.map Prod.snd).map permOfWire).symm
    refine h1.trans ?_
    rw [List.map_append, hkept, List.map_append, map_filter_permWAt]
    unfold RoleRec.toRole at hrr
    rw [hrr]
    simp
  -- whose ranges are distinct
  have hne : (ps.filter (fun p => ¬ permAt w.key w.rangeEnd p) ++ [permOfWire w]).Pairwise
      permNe := by
    refine List.pairwise_append.2 ⟨(hps.filter _).imp permNe_of_permLt, by simp, ?_⟩
    intro q hq p hp
    simp only [List.mem_singleton] at hp; subst hp
    have hq' := of_decide_eq_true (List.mem_filter.mp hq).2
    intro hqp
    simp only [Prod.mk.injEq] at hqp
    exact hq' ⟨hqp.1, hqp.2⟩
  -- so it is strictly sorted
  have hys : ((xs'.map Prod.snd).map permOfWire).Pairwise permLt := by
    have hw0 : (xs'.map Prod.snd).Pairwise
        (fun a b : PermW => ¬ rangeLt b.key b.rangeEnd a.key a.rangeEnd) :=
      List.pairwise_map.2 (pairwise_of_sorted permWLt xs' hsorted)
    have hw1 : ((xs'.map Prod.snd).map permOfWire).Pairwise (fun p q => ¬ permLt q p) :=
      List.pairwise_map.2 hw0
    have hw2 := hne.perm h1.symm (fun h => fun e => h e.symm)
    exact (hw1.and hw2).imp fun h => permLt_of_not h.1 h.2
  -- and so is `grantPerms ps w`, another such permutation
  have h2 : (grantPerms ps w).Perm
      (ps.filter (fun p => ¬ permAt w.key w.rangeEnd p) ++ [permOfWire w]) := by
    unfold grantPerms
    exact (permInsert_perm _ _).trans (List.perm_append_singleton _ _).symm
  unfold RoleRec.toRole
  exact List.Perm.eq_of_pairwise
    (fun a b _ _ h h' => absurd (rangeLt_trans h h') (rangeLt_irrefl _ _))
    hys (grantPerms_sorted ps w hps) (h1.trans h2.symm)

/-- The ranges of the role after the grant are valid, if the role's were and `w`'s is. -/
theorem grant_keys (ps : Role) (w : PermW) (hw : rangeValid w.key w.rangeEnd)
    (hold : ∀ p ∈ ps, rangeValid p.key p.rangeEnd) :
    ∀ p ∈ grantPerms ps w, rangeValid p.key p.rangeEnd := by
  intro p hp
  unfold grantPerms at hp
  rcases List.mem_cons.mp ((permInsert_perm _ _).subset hp) with h | h
  · subst h; exact hw
  · exact hold p (List.mem_filter.mp h).1

end auth
end EtcdGrove
end Perennial
