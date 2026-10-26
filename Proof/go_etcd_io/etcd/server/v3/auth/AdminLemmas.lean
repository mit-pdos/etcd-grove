/-
Lemmas of the admin side's proofs (the auth plan's S4b, 2026-10-24): the roles but one, of a
prefix (`UserRevokeRole`'s and `RoleDelete`'s loops), and `userOut` of a message with its name.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.VerdictLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

namespace auth

/-- The roles but `role`, of a prefix one longer. -/
theorem filter_take_succ (l : List GoString) (role x : GoString) (n : Nat) (h : l[n]? = some x) :
    (l.take (n + 1)).filter (fun r => decide (r ≠ role)) =
      (l.take n).filter (fun r => decide (r ≠ role)) ++ (if x ≠ role then [x] else []) := by
  rw [List.take_succ, h, Option.toList_some, List.filter_append]
  by_cases hx : x = role <;> simp [hx]

/-- Filtering out `role` keeps the length iff `role` is not there. -/
theorem filter_ne_length_eq_iff (l : List GoString) (role : GoString) :
    (l.filter (fun r => decide (r ≠ role))).length = l.length ↔ role ∉ l := by
  rw [List.length_filter_eq_length_iff]
  constructor
  · intro h hm; have := h role hm; simp at this
  · intro h x hx; have : x ≠ role := fun he => h (he ▸ hx); simpa using this

end auth

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `userOut` of a message: the record, of that name. -/
theorem auth.userOut_some_named (u : Loc) (st : AuthState) (name : GoString) (hnn : u ≠ null) :
    userOut (GF := GF) u st name ⊢ ∃ (roles : User) (ur : UserRec),
      ⌜st.users !! name = some roles ∧ ur.name = name ∧ ur.roles = roles ∧
        roles.Pairwise go.GoStringLt⌝ ∗ ownUser u ur := by
  unfold userOut
  cases h : st.users !! name with
  | none =>
    have h' : st.users.lookup name = none := h
    simp only [h']
    iintro %Hn; exact absurd Hn hnn
  | some roles =>
    have h' : st.users.lookup name = some roles := h
    simp only [h']
    iintro ⟨%ur, %Hur, Hu⟩
    iexists roles, ur
    iframe Hu
    ipureintro; exact ⟨rfl, Hur.1, Hur.2.1, Hur.2.2⟩

end lemmas

end EtcdGrove
end Perennial
