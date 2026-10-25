/-
`hasRootRole`'s proof (the auth plan's S4b, 2026-10-24): `sort.SearchStrings` (Perennial's
`sort.wp_SearchStrings`, beb785eaf) on the user's roles, sorted strictly ascending, then a
bounds-checked index. Until S4b a trust-boundary axiom (Perennial had no `SearchStrings` spec).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.hasRootRole
public import Perennial.Proof.sort

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth

namespace auth

/-- A list sorted strictly ascending is sorted ascending in `sort`'s sense. -/
theorem listSorted_of_pairwise_lt (l : List GoString) (h : l.Pairwise go.GoStringLt) :
    _root_.Perennial.sort.ListSorted go.GoStringLe l := by
  intro i j hij xi xj hi hj
  right
  have hi' : i < l.length := by
    rcases List.getElem?_eq_some_iff.mp hi with ⟨h, _⟩; exact h
  have hj' : j < l.length := by
    rcases List.getElem?_eq_some_iff.mp hj with ⟨h, _⟩; exact h
  have := List.pairwise_iff_getElem.mp h i j hi' hj' hij
  rw [List.getElem?_eq_getElem hi', Option.some.injEq] at hi
  rw [List.getElem?_eq_getElem hj', Option.some.injEq] at hj
  rw [← hi, ← hj]; exact this

/-- The binary search's answer decides membership: with every string before `i` below `x` and
every string from `i` on at least `x`, over a list sorted strictly ascending, `x` is in the list
iff `i` is an index of it holding `x`. -/
theorem mem_iff_search (l : List GoString) (x : GoString) (i : Nat)
    (hsort : l.Pairwise go.GoStringLt)
    (hlo : ∀ (j : Nat) x0, j < i → l[j]? = some x0 → go.GoStringLt x0 x)
    (hhi : ∀ (j : Nat) x0, i ≤ j → l[j]? = some x0 → go.GoStringLe x x0) :
    x ∈ l ↔ ∃ h : i < l.length, l[i] = x := by
  constructor
  · intro hx
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
    have hij : i ≤ j := Nat.le_of_not_lt fun hlt =>
      go.goStringLt_irrefl x (hlo j x hlt (by rw [List.getElem?_eq_getElem hj, hjx]))
    have hi : i < l.length := by omega
    refine ⟨hi, ?_⟩
    have hle : go.GoStringLe x l[i] := hhi i l[i] (Nat.le_refl _) (List.getElem?_eq_getElem hi)
    rcases Nat.lt_or_eq_of_le hij with hlt | heq
    · have hlt' : go.GoStringLt l[i] l[j] := List.pairwise_iff_getElem.mp hsort i j hi hj hlt
      rw [hjx] at hlt'
      rcases hle with he | hl
      · exact he.symm
      · exact absurd (go.goStringLt_trans hl hlt') (go.goStringLt_irrefl x)
    · subst heq; exact hjx
  · rintro ⟨hi, hx⟩; rw [← hx]; exact List.getElem_mem hi

end auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.hasRootRole.wp_proof : auth.hasRootRole.spec (GF := GF) (hG := hG) := by
  intro u ur
  wp_start as ⟨Hu, %Hsort⟩
  ihave #Hsortpkg : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  iunfold auth.ownUser at Hu
  icases Hu with ⟨%st, %name, %pw, %roles, %o, %uf, %sc, Hp, #Hn, #Hpw, #Hr, #Ho⟩
  wp_auto
  simp only [go_etcd_io.etcd.server.v3.auth.rootRole]
  wp_apply (_root_.Perennial.sort.wp_SearchStrings roles go!"root" .discard ur.roles)
    $$ [$Hr] as %i ⟨#Hr', %Hbnd, %Hlo, %Hhi⟩
  · ipureintro; exact auth.listSorted_of_pairwise_lt _ Hsort
  ihave %Hl := ownSlice_len _ _ _ $$ Hr
  (try wp_auto)
  have hmem := auth.mem_iff_search ur.roles auth.rootRole (sint.Z i).toNat Hsort
    (fun j x0 hj hx => Hlo j x0 (by omega) hx) (fun j x0 hj hx => Hhi j x0 (by omega) hx)
  wp_if_destruct
  · -- `idx == len(u.Roles)`: not found
    have : auth.rootRole ∉ ur.roles := fun hm => by
      obtain ⟨h, _⟩ := hmem.mp hm
      have := Hl.1; word
    iapply HΦ
    isplitl [Hp]
    · iunfold auth.ownUser
      iexists st, name, pw, roles, o, uf, sc
      iframe Hp Hn Hpw Hr Ho
    ipureintro
    simp [auth.isRoot, this]
  · -- `idx != len(u.Roles)`: the index is in bounds
    have hne : sint.Z i ≠ sint.Z roles.len := fun h => Hif (by word)
    have hlt : (sint.Z i).toNat < ur.roles.length := by have := Hl.1; word
    have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z roles.len := ⟨Hbnd.1, by have := Hl.1; word⟩
    obtain ⟨x, hx⟩ : ∃ x, ur.roles[(sint.Z i).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index roles (sint.Z i) ur.roles .discard x Hbnd.1 $$ [$Hr] as -
    · iframe; ipureintro; exact hx
    (try wp_auto)
    iapply HΦ
    isplitl [Hp]
    · iunfold auth.ownUser
      iexists st, name, pw, roles, o, uf, sc
      iframe Hp Hn Hpw Hr Ho
    ipureintro
    rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hx
    simp only [auth.isRoot]
    by_cases hr : x = auth.rootRole
    · have : auth.rootRole ∈ ur.roles := hmem.mpr ⟨hlt, by rw [hx, hr]⟩
      have hr' : x = go!"root" := hr
      simp [hr', this]
    · have : auth.rootRole ∉ ur.roles := fun hm => hr (by
        obtain ⟨_, h⟩ := hmem.mp hm; rw [← hx]; exact h)
      have hr' : ¬ x = go!"root" := hr
      simp [hr', this]

end proof

end EtcdGrove
end Perennial
