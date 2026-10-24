/-
**The permission cache's trees against the model** (the auth plan's S2, 2026-10-23): the
interval `getMergedPerms` inserts for a permission (`permIvl`: the point `[key, key ++ "\x00")`,
the open range `[key, "")` for `"\x00"`, else `[key, rangeEnd)`), the intervals of a user's
permissions of a type (`ivlsOf`: what each of the entry's two trees holds), the interval
`checkKeyInterval` queries (`queryIvl`), and the bridge from the tree's pure meaning
(`adt.inIvl`, `adt.containsRes`, `Contains.lean`) to the model's `coversPoint`/`coversRange`
(`Model.lean`): a permission's interval holds a key exactly when the permission's range does
(`inIvl_permIvl`), for a permission with a non-empty key (`permKeysOk`: the affine order's top).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Model
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Contains

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open go_etcd_io.etcd.api.v3

section pure
variable [ext : FfiSyntax]

instance isOpenEnded_dec : DecidablePred isOpenEnded :=
  fun e => inferInstanceAs (Decidable (e = [(0 : w8)]))

/-- The model's operation type of the request side's `Permission_Type`: `READ` (`0`) is a read,
`WRITE` (`1`) a write (`permTypOk`). -/
def permOp (pt : authpb.Permission_Type) : PermType := if pt = W32 0 then .read else .write

/-- The interval `getMergedPerms` inserts for the permission `p` (`range_perm_cache.go`): the
point `[key, key ++ "\x00")` (`NewBytesAffinePoint`) when `rangeEnd` is empty, `[key, "")` (open
to the end of the key space: `rangeEnd` `nil`) when it is `"\x00"`, else `[key, rangeEnd)`. -/
def permIvl (p : Perm) : adt.IvlS :=
  if p.rangeEnd = [] then (p.key, p.key ++ [W8 0])
  else if isOpenEnded p.rangeEnd then (p.key, [])
  else (p.key, p.rangeEnd)

/-- The intervals of the permissions `ps` granting `op` (what the tree of `op` holds, as a
multiset: `readPerms` the permissions granting reads, `writePerms` those granting writes,
`READWRITE` in both). -/
def ivlsOf (op : PermType) (ps : List Perm) : List adt.IvlS :=
  (ps.filter fun p => p.ty.grants op).map permIvl

/-- The interval `checkKeyInterval(key, rangeEnd)` queries: `rangeEnd` `nil` when open-ended. -/
def queryIvl (key rangeEnd : GoString) : adt.IvlS :=
  (key, if isOpenEnded rangeEnd then [] else rangeEnd)

theorem goStringLt_nil_of_ne {k : GoString} (hk : k ≠ []) : go.GoStringLt [] k := by
  cases k with
  | nil => exact absurd rfl hk
  | cons x xs => exact go.goStringLt_nil_cons x xs

/-- `k < key ++ "\x00"` is `k ≤ key`. -/
theorem goStringLt_succ_iff (k key : GoString) :
    go.GoStringLt k (key ++ [W8 0]) ↔ k = key ∨ go.GoStringLt k key := by
  constructor
  · intro h
    by_cases hlt : go.GoStringLt key k
    · rcases adt.strLt_succ_le hlt with heq | hlt'
      · exact absurd (heq ▸ h) (go.goStringLt_irrefl _)
      · exact absurd (go.goStringLt_trans h hlt') (go.goStringLt_irrefl _)
    · by_cases h2 : go.GoStringLt k key
      · exact Or.inr h2
      · exact Or.inl (go.goStringLt_eq_of_not_lt h2 hlt)
  · rintro (rfl | h)
    · exact adt.strLt_append k [W8 0] (by simp)
    · exact go.goStringLt_trans h (adt.strLt_append key [W8 0] (by simp))

/-- **A permission's interval holds a key exactly when its range does**, for a non-empty key
(the affine order's `""` is the top, the model's the least key). -/
theorem inIvl_permIvl (p : Perm) (hk : p.key ≠ []) (k : GoString) :
    adt.inIvl (permIvl p) k ↔ inRange p.key p.rangeEnd k := by
  unfold adt.inIvl permIvl inRange adt.affLt
  -- `k` at or above the key: not below it
  have hge : ∀ (hk' : k ≠ []), ¬ (k ≠ [] ∧ (p.key = [] ∨ go.GoStringLt k p.key)) ↔
      go.GoStringLe p.key k := by
    intro hk'
    unfold go.GoStringLe
    constructor
    · intro h1
      by_cases hlt : go.GoStringLt k p.key
      · exact absurd ⟨hk', Or.inr hlt⟩ h1
      · by_cases h3 : go.GoStringLt p.key k
        · exact Or.inr h3
        · exact Or.inl (go.goStringLt_eq_of_not_lt h3 hlt)
    · rintro h ⟨-, h2⟩
      rcases h2 with h2 | hlt
      · exact hk h2
      · rcases h with h | h
        · exact go.goStringLt_irrefl _ (h ▸ hlt)
        · exact go.goStringLt_irrefl _ (go.goStringLt_trans h hlt)
  have hkn : go.GoStringLe p.key k → k ≠ [] := by
    rintro h rfl
    rcases h with h | h
    · exact hk h
    · exact go.goStringLt_not_nil _ h
  by_cases he : p.rangeEnd = []
  · simp only [he, ↓reduceIte]
    have hne : p.key ++ [W8 0] ≠ [] := by simp
    constructor
    · rintro ⟨h1, hk', h2⟩
      rcases h2 with h2 | h2
      · exact absurd h2 hne
      · rcases (goStringLt_succ_iff k p.key).1 h2 with h2 | h2
        · exact h2
        · exact absurd ⟨hk', Or.inr h2⟩ h1
    · rintro rfl
      refine ⟨(hge hk).2 (Or.inl rfl), hk, Or.inr ?_⟩
      exact (goStringLt_succ_iff _ _).2 (Or.inl rfl)
  · by_cases ho : isOpenEnded p.rangeEnd
    · simp only [he, ho, ↓reduceIte]
      constructor
      · rintro ⟨h1, hk', -⟩
        refine ⟨(hge hk').1 h1, ?_⟩
        first | exact Or.inl ho | exact Or.inl trivial | trivial
      · rintro ⟨h, -⟩
        refine ⟨(hge (hkn h)).2 h, hkn h, ?_⟩
        first | exact Or.inl rfl | exact Or.inl trivial | trivial
    · simp only [he, ho, ↓reduceIte]
      constructor
      · rintro ⟨h1, hk', h2⟩
        rcases h2 with h2 | h2
        · first | exact h2.elim | exact absurd h2 he
        · exact ⟨(hge hk').1 h1, Or.inr h2⟩
      · rintro ⟨h, h2⟩
        rcases h2 with h2 | h2
        · first | exact h2.elim | exact absurd h2 ho
        · exact ⟨(hge (hkn h)).2 h, hkn h, Or.inr h2⟩

/-- The queried interval is the interval of a permission with that range (a non-empty one). -/
theorem queryIvl_eq_permIvl (key rangeEnd : GoString) (he : rangeEnd ≠ []) (ty : PermType) :
    queryIvl key rangeEnd = permIvl ⟨key, rangeEnd, ty⟩ := by
  unfold queryIvl permIvl
  by_cases ho : isOpenEnded rangeEnd <;> simp [he, ho]

/-- The queried interval holds a key exactly when the request's range does. -/
theorem inIvl_queryIvl (key rangeEnd : GoString) (hk : key ≠ []) (he : rangeEnd ≠ []) (k : GoString) :
    adt.inIvl (queryIvl key rangeEnd) k ↔ inRange key rangeEnd k := by
  rw [queryIvl_eq_permIvl key rangeEnd he .read]
  exact inIvl_permIvl ⟨key, rangeEnd, .read⟩ hk k

/-- The queried interval of a request with a non-empty key and an open-ended or proper range is
below its end (`Contains`' premise). -/
theorem queryIvl_ok (key rangeEnd : GoString) (hk : key ≠ [])
    (h : isOpenEnded rangeEnd ∨ go.GoStringLt key rangeEnd) :
    adt.affLt (queryIvl key rangeEnd).1 (queryIvl key rangeEnd).2 := by
  unfold queryIvl adt.affLt
  refine ⟨hk, ?_⟩
  by_cases ho : isOpenEnded rangeEnd
  · simp [ho]
  · simp only [ho, ↓reduceIte]
    rcases h with h | h
    · exact absurd h ho
    · exact Or.inr h

/-- A key is covered by a user's permissions of a type exactly when some interval of the
tree of that type holds it (a state whose permissions' keys are non-empty). -/
theorem covers_iff (st : AuthState) (u : User) (op : PermType) (k : GoString)
    (hst : permKeysOk st) :
    (∃ p ∈ userPerms st u, p.covers op k) ↔ ∃ x ∈ ivlsOf op (userPerms st u), adt.inIvl x k := by
  unfold ivlsOf Perm.covers
  constructor
  · rintro ⟨p, hp, hg, hr⟩
    obtain ⟨r, ps, hps, hpps⟩ := mem_userPerms hp
    refine ⟨permIvl p, List.mem_map_of_mem (List.mem_filter.2 ⟨hp, hg⟩), ?_⟩
    exact (inIvl_permIvl p (hst r ps hps p hpps) k).2 hr
  · rintro ⟨x, hx, hxk⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hp, hg⟩ := List.mem_filter.1 hp
    obtain ⟨r, ps, hps, hpps⟩ := mem_userPerms hp
    exact ⟨p, hp, hg, (inIvl_permIvl p (hst r ps hps p hpps) k).1 hxk⟩

/-- **`coversPoint` is the tree's point query** (`checkKeyPoint`). -/
theorem coversPoint_iff (st : AuthState) (u : User) (op : PermType) (key : GoString)
    (hst : permKeysOk st) :
    coversPoint st u op key ↔ ∃ x ∈ ivlsOf op (userPerms st u), adt.inIvl x key :=
  covers_iff st u op key hst

/-- **`coversRange` is the tree's coverage of the queried interval** (`checkKeyInterval`), for a
request with a non-empty key and a non-empty range. -/
theorem coversRange_iff (st : AuthState) (u : User) (op : PermType) (key rangeEnd : GoString)
    (hk : key ≠ []) (he : rangeEnd ≠ []) (hst : permKeysOk st) :
    coversRange st u op key rangeEnd ↔
      ∀ k, adt.inIvl (queryIvl key rangeEnd) k → ∃ x ∈ ivlsOf op (userPerms st u), adt.inIvl x k := by
  unfold coversRange
  constructor
  · intro H k hk'
    exact (covers_iff st u op k hst).1 (H k ((inIvl_queryIvl key rangeEnd hk he k).1 hk'))
  · intro H k hk'
    exact (covers_iff st u op k hst).2 (H k ((inIvl_queryIvl key rangeEnd hk he k).2 hk'))

/-- The intervals of a list of entries, as a multiset, determine what the entries hold. -/
theorem exists_inIvl_perm {L : List adt.Entry} {xs : List adt.IvlS}
    (h : (L.map Prod.fst).Perm xs) (k : GoString) :
    (∃ z ∈ L, adt.inIvl z.1 k) ↔ ∃ x ∈ xs, adt.inIvl x k := by
  constructor
  · rintro ⟨z, hz, hzk⟩
    exact ⟨z.1, h.mem_iff.1 (List.mem_map_of_mem hz), hzk⟩
  · rintro ⟨x, hx, hxk⟩
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 (h.mem_iff.2 hx)
    exact ⟨z, hz, hxk⟩

end pure

end auth
end EtcdGrove
end Perennial
