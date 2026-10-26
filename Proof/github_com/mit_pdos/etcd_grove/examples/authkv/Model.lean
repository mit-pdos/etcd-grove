/-
**authkv's auth state and what it permits** (the auth plan's E2b, 2026-10-25; `notes/decisions.md`,
"E2b of the auth plan"). Lean-first (no Rocq counterpart).

`SetUp` (`examples/authkv/authkv.go`) leaves the store at `setupSt rev`: auth enabled, the users
`root` (the root role), `u` (role `r`) and `v` (no role), the role `r` granted `READWRITE` on
`[a, b)`. Nothing changes it afterwards (the workload has no admin request, and no principal of it
is an admin), so every check of the workload reads states of this shape, at some revision.

The program's own predicate, `Permitted(who, k)` (`permittedK`: `who` is `u` and `k ∈ [a, b)`), is
the model's verdict at that state for the principals of the workload (`granted_setupSt_point`,
`granted_setupSt_iff`): for a point request of a non-empty key, a principal named `u` or `v`
with a revision is granted exactly what `permittedK` says, whatever the operation's type; the
principals without a user (no token, or a token no provider issued: `AuthInfoFromCtx` gives none,
or a revision `0`) are granted nothing (`granted_rev0`). The ranges the workload reads are the
granted range itself (`granted_setupSt_range`) and two the role does not cover
(`not_coversRange_past`, `not_coversRange_c`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Base
public import Proof.go_etcd_io.etcd.server.v3.auth.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open auth

/-! ## The program's ranges and principals -/

/-- The range role `r` is granted, `[lo, hi)` (`authkv.go`'s `lo`, `hi`). -/
abbrev lo : GoString := go!"a"
abbrev hi : GoString := go!"b"

/-- `InRange(k)`: `k ∈ [lo, hi)`, in Go's string order. -/
def inRangeK (k : GoString) : Prop := go.GoStringLe lo k ∧ go.GoStringLt k hi

instance (k : GoString) : Decidable (inRangeK k) := by unfold inRangeK; infer_instance

/-- `Permitted(who, k)`: `who` is `u` and `k ∈ [lo, hi)`. -/
def permittedK (who k : GoString) : Prop := who = go!"u" ∧ inRangeK k

instance (who k : GoString) : Decidable (permittedK who k) := by unfold permittedK; infer_instance

/-! ## The auth state `SetUp` leaves -/

/-- Role `r`'s one permission: `[a, b)`, `READWRITE`. -/
def permR : Perm := ⟨lo, hi, .readwrite⟩

/-- **The store after `SetUp`**, at the auth revision `rev` (the set-up's admin requests bump it;
its value does not matter): auth enabled, users `root` with the root role, `u` with role `r`, `v`
with none, and role `r` with `permR`. -/
def setupSt (rev : Nat) : AuthState where
  enabled := true
  revision := rev
  users := GMap.insert go!"root" [rootRole] (GMap.insert go!"u" [go!"r"]
    (GMap.insert go!"v" [] ∅))
  roles := GMap.insert go!"r" [permR] ∅

/-! ## The verdicts at that state -/

theorem setupSt_users_u (rev : Nat) : (setupSt rev).users !! go!"u" = some [go!"r"] := by
  simp [setupSt, GMap.lookup_insert_ne, GMap.lookup_insert]

theorem setupSt_users_v (rev : Nat) : (setupSt rev).users !! go!"v" = some [] := by
  simp [setupSt, GMap.lookup_insert_ne, GMap.lookup_insert]

theorem userPerms_u (rev : Nat) : userPerms (setupSt rev) [go!"r"] = [permR] := by
  simp [userPerms, setupSt, GMap.lookup_insert]

theorem userPerms_v (rev : Nat) : userPerms (setupSt rev) [] = [] := by
  simp [userPerms]

/-- `permR` covers a key, for any operation, exactly when the key is in `[lo, hi)`. -/
theorem permR_covers (op : PermType) (k : GoString) : permR.covers op k ↔ inRangeK k := by
  simp only [Perm.covers, inRange, permR, isOpenEnded, inRangeK]
  cases op <;> simp [PermType.grants, PermType.grantsRead, PermType.grantsWrite]

theorem not_isRoot_u : ¬ isRoot [go!"r"] := by simp [isRoot, rootRole]

theorem not_isRoot_v : ¬ isRoot ([] : User) := by simp [isRoot]

/-- **A point request of `u`**: granted exactly on `[lo, hi)`. -/
theorem granted_u_point (rev r : Nat) (op : PermType) (k : GoString) (hr : r ≠ 0) (hk : k ≠ []) :
    auth.granted (setupSt rev) ⟨go!"u", r⟩ k [] op ↔ inRangeK k := by
  have hs : reqShape k [] := ⟨hk, Or.inl rfl⟩
  simp only [auth.granted, setupSt_users_u]
  constructor
  · rintro ⟨-, u, hu, hru⟩
    cases hu
    rcases hru with hroot | hc
    · exact absurd hroot not_isRoot_u
    · have := hc hs
      simp only [covers, if_pos rfl, coversPoint, userPerms_u, List.mem_singleton,
        exists_eq_left] at this
      exact (permR_covers op k).1 this
  · intro hin
    refine ⟨hr, _, rfl, Or.inr fun _ => ?_⟩
    simp only [covers, if_pos rfl, coversPoint, userPerms_u, List.mem_singleton, exists_eq_left]
    exact (permR_covers op k).2 hin

/-- **A point request of `v`**: granted nothing. -/
theorem granted_v_point (rev r : Nat) (op : PermType) (k : GoString) (hk : k ≠ []) :
    ¬ auth.granted (setupSt rev) ⟨go!"v", r⟩ k [] op := by
  have hs : reqShape k [] := ⟨hk, Or.inl rfl⟩
  simp only [auth.granted, setupSt_users_v]
  rintro ⟨-, u, hu, hru⟩
  cases hu
  rcases hru with hroot | hc
  · exact not_isRoot_v hroot
  · have := hc hs
    simp [covers, coversPoint, userPerms_v] at this

/-- **A principal without a revision** (an `AuthInfo{}`: the user name empty) is granted
nothing. -/
theorem granted_rev0 (st : AuthState) (who key rangeEnd : GoString) (op : PermType) :
    ¬ auth.granted st ⟨who, 0⟩ key rangeEnd op := by
  rintro ⟨h, -⟩; exact h rfl

/-- **The program's verdict is the model's**, for the users of the workload: a point request of
a non-empty key by `u` or `v` with a revision is granted at `setupSt` exactly when `Permitted`
says so. -/
theorem granted_setupSt_iff (rev r : Nat) (op : PermType) (who k : GoString) (hr : r ≠ 0)
    (hk : k ≠ []) (hw : who = go!"u" ∨ who = go!"v") :
    auth.granted (setupSt rev) ⟨who, r⟩ k [] op ↔ permittedK who k := by
  rcases hw with rfl | rfl
  · rw [granted_u_point rev r op k hr hk]; simp [permittedK]
  · simp only [permittedK, iff_false_intro (granted_v_point rev r op k hk), false_iff]
    rintro ⟨h, -⟩; exact absurd h (by decide)

/-- `u`'s range of `[lo, hi)`: granted. -/
theorem granted_setupSt_range (rev r : Nat) (op : PermType) (hr : r ≠ 0) :
    auth.granted (setupSt rev) ⟨go!"u", r⟩ lo hi op := by
  refine ⟨hr, _, setupSt_users_u rev, Or.inr fun _ => ?_⟩
  have hne : hi ≠ [] := by decide
  simp only [covers, if_neg hne, coversRange, userPerms_u, List.mem_singleton, exists_eq_left]
  intro k hk
  refine (permR_covers op k).2 ?_
  simp only [inRange, if_neg hne, isOpenEnded] at hk
  exact ⟨hk.1, hk.2.resolve_left (by decide)⟩

/-- The key `b` itself is in `[a, d)` but not in `[a, b)`: `u`'s range of `[a, d)` is not
covered. -/
theorem not_coversRange_past (rev : Nat) (op : PermType) :
    ¬ coversRange (setupSt rev) [go!"r"] op lo go!"d" := by
  intro h
  have hin : inRange lo go!"d" hi := by
    simp only [inRange, isOpenEnded]
    refine ⟨?_, Or.inr ?_⟩ <;> decide
  obtain ⟨p, hp, hc⟩ := h hi hin
  rw [userPerms_u, List.mem_singleton] at hp
  subst hp
  have := ((permR_covers op hi).1 hc).2
  exact (by decide : ¬ go.GoStringLt hi hi) this

/-- The key `c/` is in the prefix range of `c/` (`[c/, c0)`) but not in `[a, b)`: `u`'s range of
the prefix `c/` is not covered. -/
theorem not_coversRange_c (rev : Nat) (op : PermType) :
    ¬ coversRange (setupSt rev) [go!"r"] op go!"c/" go!"c0" := by
  intro h
  have hin : inRange go!"c/" go!"c0" go!"c/" := by
    simp only [inRange, isOpenEnded]
    refine ⟨?_, Or.inr ?_⟩ <;> decide
  obtain ⟨p, hp, hc⟩ := h _ hin
  rw [userPerms_u, List.mem_singleton] at hp
  subst hp
  have := ((permR_covers op _).1 hc).2
  exact (by decide : ¬ go.GoStringLt go!"c/" hi) this

end authkv
end EtcdGrove
end Perennial
