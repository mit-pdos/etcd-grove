/-
Lemmas of the grants (the auth plan's S4c, 2026-10-24). Lean-first (no Rocq counterpart): the
write side's reads with the owned message (`userOutX`, `roleOutX`), and the sorted roles after
`UserGrantRole`'s append and `sort.Strings`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

namespace auth

/-- A list sorted strictly ascending has no duplicates. -/
theorem nodup_of_pairwise_lt (l : List GoString) (h : l.Pairwise go.GoStringLt) : l.Nodup :=
  h.imp fun {a b} (hlt : go.GoStringLt a b) (he : a = b) => go.goStringLt_irrefl b (he ▸ hlt)

/-- `UserGrantRole`'s roles after the append and `sort.Strings`: a permutation of the roles with
the new one, sorted (`≤` by index), of a list without duplicates, is sorted strictly. -/
theorem pairwise_lt_of_sorted_perm (l l' : List GoString) (hnd : l.Nodup) (hp : l'.Perm l)
    (hs : ∀ (i j : Nat) (xi xj : GoString), l'[i]? = some xi → l'[j]? = some xj → i < j →
      go.GoStringLe xi xj) : l'.Pairwise go.GoStringLt := by
  have hnd' : l'.Nodup := hp.nodup_iff.mpr hnd
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hle := hs i j l'[i] l'[j] (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij
  rcases hle with he | hl
  · exact absurd (hnd'.eq_of_getElem_eq hi hj he) (by omega)
  · exact hl

end auth

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem auth.userOutX_null (st : AuthState) (name : GoString) :
    userOutX (GF := GF) null st name ⊢ ⌜st.users !! name = none⌝ := by
  unfold userOutX
  cases h : st.users !! name with
  | none => iintro -; ipureintro; rfl
  | some roles =>
    iintro ⟨%ur, -, Hu⟩
    iunfold ownUserX at Hu
    icases Hu with ⟨%ms, %n, %pw, %rl, %o, %uf, %sc, Hp, -⟩
    ihave %Hnn := typedPointsto_not_null $$ Hp
    exact absurd rfl Hnn

theorem auth.userOutX_some_named (u : Loc) (st : AuthState) (name : GoString) (hnn : u ≠ null) :
    userOutX (GF := GF) u st name ⊢ ∃ (roles : User) (ur : UserRec),
      ⌜st.users !! name = some roles ∧ ur.name = name ∧ ur.roles = roles ∧
        roles.Pairwise go.GoStringLt⌝ ∗ ownUserX u ur := by
  unfold userOutX
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
