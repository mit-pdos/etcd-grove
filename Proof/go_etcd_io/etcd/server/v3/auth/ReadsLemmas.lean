/-
Lemmas of the admin reads (the auth plan's E2j, 2026-10-26): the messages `GetAllUsers` and
`GetAllRoles` return, their names made read-only (the lists read only the names). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Reads

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem userOut_nameAt (u : Loc) (st : AuthState) (n : GoString)
    (h : (st.users.lookup n).isSome) : userOut (GF := GF) u st n ⊢ |==> userNameAt u n := by
  unfold userOut
  cases hl : st.users.lookup n with
  | none => rw [hl] at h; cases h
  | some roles =>
    iintro ⟨%ur, %Hur, Hu⟩
    iunfold ownUser at Hu
    icases Hu with ⟨%ms, %nm, %pw, %rl, %o, %uf, %sc, Hp, #Hnm, -, -, -⟩
    icases typedPointsto_split _ _ _ $$ Hp with Hp
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hp
    ipersist Name
    imodintro
    iunfold userNameAt
    iexists nm
    rw [← Hur.1]
    isplitr
    · iexact Name
    · iexact Hnm

theorem roleOut_nameAt (r : Loc) (st : AuthState) (n : GoString)
    (h : (st.roles.lookup n).isSome) : roleOut (GF := GF) r st n ⊢ |==> roleNameAt r n := by
  unfold roleOut
  cases hl : st.roles.lookup n with
  | none => rw [hl] at h; cases h
  | some ps =>
    iintro ⟨%rr, %Hrr, Hr⟩
    iunfold ownRole at Hr
    icases Hr with ⟨%ms, %nm, %kp, %pl, %uf, %sc, Hp, #Hnm, -⟩
    icases typedPointsto_split _ _ _ $$ Hp with Hp
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hp
    ipersist Name
    imodintro
    iunfold roleNameAt
    iexists nm
    rw [← Hrr.1]
    isplitr
    · iexact Name
    · iexact Hnm

theorem usersOut_names (st : AuthState) :
    ∀ l : List (Loc × GoString), (∀ x ∈ l, (st.users.lookup x.2).isSome) →
      ([∗list] x ∈ l, userOut (GF := GF) x.1 st x.2) ⊢ |==> □ [∗list] x ∈ l, userNameAt x.1 x.2
  | [], _ => by
    iintro -
    imodintro
    imodintro
    iapply (BigSepL.bigSepL_nil_intro (PROP := IProp GF) (P := iprop(True)))
    itrivial
  | x :: xs, h => by
    iintro H
    ihave ⟨Hx, Hxs⟩ := (BigSepL.bigSepL_cons (PROP := IProp GF)
      (Φ := fun _ y => userOut (GF := GF) y.1 st y.2) (x := x) (xs := xs)).1 $$ H
    ihave Hx := userOut_nameAt x.1 st x.2 (h x (List.mem_cons_self ..)) $$ Hx
    ihave Hxs := usersOut_names st xs (fun y hy => h y (List.mem_cons_of_mem _ hy)) $$ Hxs
    imod Hx with #Hx
    imod Hxs with #Hxs
    imodintro
    imodintro
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)
      (Φ := fun _ y => userNameAt (GF := GF) y.1 y.2) (x := x) (xs := xs)).2
    isplitl []
    · iexact Hx
    · iexact Hxs

theorem rolesOut_names (st : AuthState) :
    ∀ l : List (Loc × GoString), (∀ x ∈ l, (st.roles.lookup x.2).isSome) →
      ([∗list] x ∈ l, roleOut (GF := GF) x.1 st x.2) ⊢ |==> □ [∗list] x ∈ l, roleNameAt x.1 x.2
  | [], _ => by
    iintro -
    imodintro
    imodintro
    iapply (BigSepL.bigSepL_nil_intro (PROP := IProp GF) (P := iprop(True)))
    itrivial
  | x :: xs, h => by
    iintro H
    ihave ⟨Hx, Hxs⟩ := (BigSepL.bigSepL_cons (PROP := IProp GF)
      (Φ := fun _ y => roleOut (GF := GF) y.1 st y.2) (x := x) (xs := xs)).1 $$ H
    ihave Hx := roleOut_nameAt x.1 st x.2 (h x (List.mem_cons_self ..)) $$ Hx
    ihave Hxs := rolesOut_names st xs (fun y hy => h y (List.mem_cons_of_mem _ hy)) $$ Hxs
    imod Hx with #Hx
    imod Hxs with #Hxs
    imodintro
    imodintro
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)
      (Φ := fun _ y => roleNameAt (GF := GF) y.1 y.2) (x := x) (xs := xs)).2
    isplitl []
    · iexact Hx
    · iexact Hxs

/-- The `i`-th name of a zipped list of the names' messages. -/
theorem zip_lookup_names {A : Type} (us : List A) (names : List GoString) (i : Nat)
    (hlen : us.length = names.length) (hi : i < us.length) :
    ∃ u n, us[i]? = some u ∧ names[i]? = some n ∧ (us.zip names)[i]? = some (u, n) := by
  refine ⟨us[i], names[i]'(hlen ▸ hi), List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem _, ?_⟩
  rw [List.getElem?_zip_eq_some]
  exact ⟨List.getElem?_eq_getElem hi, List.getElem?_eq_getElem _⟩

/-- One more element of a list copied into a slice of zero values. -/
theorem take_replicate_set {A : Type} (l : List A) (k : Nat) (z x : A) (hk : l[k]? = some x) :
    (l.take k ++ List.replicate (l.length - k) z).set k x =
      l.take (k + 1) ++ List.replicate (l.length - (k + 1)) z := by
  have hlt : k < l.length := (List.getElem?_eq_some_iff.1 hk).1
  have hm : l.length - k = (l.length - (k + 1)) + 1 := by omega
  rw [hm, List.replicate_succ, List.take_succ, hk]
  have htk : (l.take k).length = k := by simp; omega
  rw [List.set_append_right _ _ (by omega), htk, Nat.sub_self]
  simp

end lemmas

end auth
end EtcdGrove
end Perennial
