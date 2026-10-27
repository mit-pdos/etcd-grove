/-
Pure lemmas for `getMergedPerms`'s and `refreshRangePermCache`'s loops (the auth plan's S2,
2026-10-23): the permissions of a user's roles seen so far, the intervals of a list of
permissions as it grows, the trees' lists under `Insert` as multisets, and the count bound
(`permsFit`). See `PermTree.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.PermTree
public import Proof.go_etcd_io.etcd.server.v3.auth.Buckets

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

section pure
variable [GooseExts]

/-- The permissions of one more role. -/
theorem userPerms_take_succ (st : AuthState) (roles : List GoString) (n : Nat) (rn : GoString)
    (h : roles[n]? = some rn) :
    userPerms st (roles.take (n + 1)) = userPerms st (roles.take n) ++ (st.roles !! rn).getD [] := by
  unfold userPerms
  rw [List.take_add_one, h, List.flatMap_append]
  simp

theorem ivlsOf_append (op : PermType) (xs ys : List Perm) :
    ivlsOf op (xs ++ ys) = ivlsOf op xs ++ ivlsOf op ys := by
  unfold ivlsOf; rw [List.filter_append, List.map_append]

theorem ivlsOf_singleton (op : PermType) (p : Perm) :
    ivlsOf op [p] = if p.ty.grants op then [permIvl p] else [] := by
  unfold ivlsOf
  by_cases h : p.ty.grants op = true
  · simp [h]
  · simp [h]

theorem length_ivlsOf_le (op : PermType) (ps : List Perm) : (ivlsOf op ps).length ≤ ps.length := by
  unfold ivlsOf; rw [List.length_map]; exact List.length_filter_le _ _

/-- One more permission of the role. -/
theorem filterMap_take_succ {α β : Type} (g : α → Option β) (l : List α) (m : Nat) (x : α)
    (h : l[m]? = some x) :
    (l.take (m + 1)).filterMap g = (l.take m).filterMap g ++ (g x).toList := by
  rw [List.take_add_one, h, List.filterMap_append]
  cases hg : g x <;> simp [hg]

/-- `Insert` adds the entry's interval to the tree's intervals (as multisets). -/
theorem perm_insert_snoc {L : List adt.Entry} {xs : List adt.IvlS} (h : (L.map Prod.fst).Perm xs)
    (z : adt.Entry) : ((adt.ivtInsert z L).map Prod.fst).Perm (xs ++ [z.1]) := by
  have h1 := (adt.ivtInsert_perm z L).map Prod.fst
  rw [List.map_cons] at h1
  exact h1.trans ((h.cons z.1).trans (List.perm_append_singleton z.1 xs).symm)

/-- The permissions seen so far, and one more, are among the user's. -/
theorem prefix_length_lt (st : AuthState) (roles : List GoString) (n m : Nat) (rn : GoString)
    (h1 : roles[n]? = some rn) (ps : List Perm) (h2 : st.roles !! rn = some ps) (rr : RoleRec)
    (h3 : rr.toRole.Perm ps) (w : PermW) (hm : rr.perms[m]? = some w) (p : Perm)
    (hw : permOfWire w = some p) :
    (userPerms st (roles.take n) ++ (rr.perms.take m).filterMap permOfWire).length + 1 ≤
      (userPerms st roles).length := by
  have hsplit : roles = roles.take n ++ rn :: roles.drop (n + 1) := by
    obtain ⟨hn, hrn⟩ := List.getElem?_eq_some_iff.1 h1
    conv => lhs; rw [← List.take_append_drop n roles]
    rw [List.drop_eq_getElem_cons hn, hrn]
  have hperms : (rr.perms.take (m + 1)).filterMap permOfWire ++ (rr.perms.drop (m + 1)).filterMap permOfWire = rr.toRole := by
    rw [← List.filterMap_append, List.take_append_drop]; rfl
  rw [filterMap_take_succ permOfWire rr.perms m w hm, hw] at hperms
  have hlen : ((rr.perms.take m).filterMap permOfWire).length + 1 ≤ ps.length := by
    rw [← h3.length_eq, ← hperms]; simp
  calc (userPerms st (roles.take n) ++ (rr.perms.take m).filterMap permOfWire).length + 1
      = (userPerms st (roles.take n)).length + (((rr.perms.take m).filterMap permOfWire).length + 1) := by
        rw [List.length_append]; omega
    _ ≤ (userPerms st (roles.take n)).length + ps.length := by omega
    _ ≤ (userPerms st roles).length := by
        conv => rhs; rw [hsplit]
        unfold userPerms
        rw [List.flatMap_append, List.flatMap_cons, h2, List.length_append, List.length_append]
        simp only [Option.getD_some]
        omega

/-- `Insert`'s count bound for the tree of a type, from the user's permissions fitting. -/
theorem insert_count_ok (st : AuthState) (roles : List GoString) (n m : Nat) (rn : GoString)
    (hfit : (userPerms st roles).length < 2 ^ 63) (h1 : roles[n]? = some rn) (ps : List Perm)
    (h2 : st.roles !! rn = some ps) (rr : RoleRec) (h3 : rr.toRole.Perm ps) (w : PermW)
    (hm : rr.perms[m]? = some w) (p : Perm) (hw : permOfWire w = some p) (op : PermType)
    {L : List adt.Entry}
    (hL : (L.map Prod.fst).Perm
      (ivlsOf op (userPerms st (roles.take n) ++ (rr.perms.take m).filterMap permOfWire))) :
    L.length + 1 < 2 ^ 63 := by
  have h := prefix_length_lt st roles n m rn h1 ps h2 rr h3 w hm p hw
  have hl : L.length ≤ (userPerms st (roles.take n) ++ (rr.perms.take m).filterMap permOfWire).length := by
    have h1 : L.length = (L.map Prod.fst).length := by simp
    rw [h1, hL.length_eq]
    exact length_ivlsOf_le _ _
  omega

/-- A wire permission's model (when of a known type): the same key and range. -/
theorem permOfWire_some {w : PermW} {p : Perm} (h : permOfWire w = some p) :
    p.key = w.key ∧ p.rangeEnd = w.rangeEnd ∧
      (w.ty = W32 0 ∧ p.ty = .read ∨ w.ty = W32 1 ∧ p.ty = .write ∨
        w.ty = W32 2 ∧ p.ty = .readwrite) := by
  unfold permOfWire at h
  split at h
  · cases h; exact ⟨rfl, rfl, Or.inl ⟨‹_›, rfl⟩⟩
  split at h
  · cases h; exact ⟨rfl, rfl, Or.inr (Or.inl ⟨‹_›, rfl⟩)⟩
  split at h
  · cases h; exact ⟨rfl, rfl, Or.inr (Or.inr ⟨‹_›, rfl⟩)⟩
  cases h

theorem permOfWire_none {w : PermW} (h0 : w.ty ≠ W32 0) (h1 : w.ty ≠ W32 1) (h2 : w.ty ≠ W32 2) :
    permOfWire w = none := by
  unfold permOfWire
  split <;> first | rfl | exact absurd ‹_› h0 | exact absurd ‹_› h1 | exact absurd ‹_› h2

theorem permOfWire_read {w : PermW} (h : w.ty = W32 0) :
    permOfWire w = some ⟨w.key, w.rangeEnd, .read⟩ := by
  unfold permOfWire; simp [h]

theorem permOfWire_write {w : PermW} (h : w.ty = W32 1) :
    permOfWire w = some ⟨w.key, w.rangeEnd, .write⟩ := by
  unfold permOfWire; simp [h]

theorem permOfWire_readwrite {w : PermW} (h : w.ty = W32 2) :
    permOfWire w = some ⟨w.key, w.rangeEnd, .readwrite⟩ := by
  unfold permOfWire; simp [h]

/-- A permission's interval does not depend on its type. -/
theorem permIvl_ty (k re : GoString) (ty ty' : PermType) :
    permIvl ⟨k, re, ty⟩ = permIvl ⟨k, re, ty'⟩ := rfl

/-- The interval of a permission, by its range. -/
theorem permIvl_point (k : GoString) (ty : PermType) : permIvl ⟨k, [], ty⟩ = (k, k ++ [W8 0]) := by
  simp [permIvl]

theorem permIvl_open (k re : GoString) (ty : PermType) (h : isOpenEnded re) :
    permIvl ⟨k, re, ty⟩ = (k, []) := by
  have hne : re ≠ [] := by rw [h]; simp
  simp [permIvl, hne, h]

theorem permIvl_range (k re : GoString) (ty : PermType) (hne : re ≠ []) (h : ¬ isOpenEnded re) :
    permIvl ⟨k, re, ty⟩ = (k, re) := by
  simp [permIvl, hne, h]

end pure

end auth
end EtcdGrove
end Perennial
