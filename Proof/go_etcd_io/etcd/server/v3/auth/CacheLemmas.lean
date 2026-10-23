/-
Lemmas for `refreshRangePermCache`'s proof (the auth plan's S2, 2026-10-23): the cache's map built
from one transaction's users is `cacheOk` in every mode, and the bookkeeping of its keys as the
users are inserted. See `InvAuth.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI Iris.ProofMode

section pure

/-- A list without duplicates: an element is not among those before it. -/
theorem nodup_not_mem_take {α : Type} {l : List α} (hn : l.Nodup) {k : Nat} {x : α}
    (h : l[k]? = some x) : x ∉ l.take k := by
  obtain ⟨hk, hx⟩ := List.getElem?_eq_some_iff.1 h
  have hsplit : l = l.take k ++ l[k] :: l.drop (k + 1) := by
    conv => lhs; rw [← List.take_append_drop k l]
    rw [List.drop_eq_getElem_cons hk]
  rw [hsplit] at hn
  obtain ⟨-, -, hdisj⟩ := List.nodup_append.1 hn
  intro hmem
  have hx' : x ∈ l[k] :: l.drop (k + 1) := by rw [hx]; exact List.mem_cons_self
  exact hdisj x hmem x hx' rfl

/-- The map's keys after inserting the `k`-th user: the users up to it. -/
theorem insert_keys_take {Mp : GMap GoString Loc} {names : List GoString} {k : Nat} {nm : GoString}
    (hnm : names[k]? = some nm) (hdom : ∀ u, (Mp !! u).isSome ↔ u ∈ names.take k) (p : Loc) :
    ∀ u, ((<[nm := p]> Mp) !! u).isSome ↔ u ∈ names.take (k + 1) := by
  intro u
  rw [List.take_add_one, hnm, Option.toList, List.mem_append, List.mem_singleton, ← hdom u]
  by_cases hu : u = nm
  · subst hu; simp
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hu)]
    simp [hu]

/-- The key is new: not among the users before it. -/
theorem insert_fresh {Mp : GMap GoString Loc} {names : List GoString} {k : Nat} {nm : GoString}
    (hn : names.Nodup) (hnm : names[k]? = some nm)
    (hdom : ∀ u, (Mp !! u).isSome ↔ u ∈ names.take k) : Mp !! nm = none := by
  have h := (hdom nm)
  have hnot := nodup_not_mem_take hn hnm
  cases hm : Mp !! nm with
  | none => rfl
  | some p => rw [hm] at h; exact absurd (h.1 rfl) hnot

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **A map built from one state is `cacheOk`**: in `on γa` the state is recorded (`authSnap`), the
map's keys are its users and the entries their permissions; in the other modes the entries. -/
theorem cacheOk_intro (M : AuthMode) (Mp : GMap GoString Loc) (sta : AuthState) :
    authSnap (GF := GF) M sta ∗ ⌜∀ u, (Mp !! u).isSome ↔ (sta.users !! u).isSome⌝ ∗
      ([∗map] u ↦ p ∈ Mp, ∃ Lr Lw, permsAt p Lr Lw ∗ ⌜cacheEntryIs sta u Lr Lw⌝) ⊢
    cacheOk M Mp := by
  cases M with
  | on γa =>
    unfold authSnap cacheOk
    iintro ⟨⟨%i, #Hst⟩, %Hdom, Hall⟩
    iexists i, sta
    iframe Hst Hall
    ipureintro; exact Hdom
  | off =>
    unfold cacheOk
    iintro ⟨-, -, Hall⟩
    iapply (BigSepM.bigSepM_mono (fun {_ _} _ => ?_)) $$ Hall
    iintro ⟨%Lr, %Lw, Hp, -⟩
    iexists Lr, Lw
    iexact Hp
  | any =>
    unfold cacheOk
    iintro ⟨-, -, Hall⟩
    iapply (BigSepM.bigSepM_mono (fun {_ _} _ => ?_)) $$ Hall
    iintro ⟨%Lr, %Lw, Hp, -⟩
    iexists Lr, Lw
    iexact Hp

end defs

end auth
end EtcdGrove
end Perennial
