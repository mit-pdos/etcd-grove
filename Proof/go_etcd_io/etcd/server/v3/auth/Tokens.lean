/-
**The issued tokens** (the auth plan's S5, 2026-10-24; `notes/decisions.md`, "S5 of the auth
plan"). Lean-first (no Rocq counterpart).

A token provider (`TokenProvider`: `tokenSimple`, `tokenJWT`, `tokenNop`) issues tokens
(`assign(ctx, username, rev)`) and later maps a token back to an auth info (`info(ctx, token,
rev)`). The binding the auth store relies on: in the mode `on γa`, `info` returns a user only for a
token that was issued to that user. It is recorded under the ghost name `γa.tok` (`AuthNames`):
`tokIssued γa token user`, persistent, an element of a ghost map keyed by the pair (a token may be
issued again after `disable()` cleared the simple provider's map, possibly to another user, so the
key is the pair, not the token). The provider holds the authority (`tokAuth`), with every element
it has issued kept persistent, so that issuing a token twice to one user is allowed
(`tokIssue`).

Not modelled: a token's expiry (the simple provider's TTL keeper deletes tokens at any time; the
JWT's claims carry an expiry): `info` may refuse any token, and the binding is only about the
tokens it accepts.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Model
public import Perennial.Ghost.GhostMap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI Iris.ProofMode

section ghost
variable {GF : BundledGFunctors} [AllG GF]

/-- **The token `token` was issued to `user`** under the names `γa` (persistent). -/
def tokIssued (γa : AuthNames) (token user : GoString) : IProp GF :=
  ghostMapElem γa.tok (token, user) DFrac.discard ()

instance tokIssued_persistent (γa : AuthNames) (token user : GoString) :
    Persistent (tokIssued (GF := GF) γa token user) := by
  unfold tokIssued; infer_instance

/-- **The provider's authority** over the tokens issued under `γt`: the pairs `S`, each with its
persistent element. -/
def tokAuth (γt : GName) (S : GMap (GoString × GoString) Unit) : IProp GF :=
  iprop(ghostMapAuth γt 1 S ∗
    □ (∀ k : GoString × GoString, ⌜S.lookup k = some ()⌝ → ghostMapElem γt k DFrac.discard ()))

/-- A fresh authority, no token issued. -/
theorem tokAlloc : ⊢ |==> ∃ γt : GName, tokAuth (GF := GF) γt ∅ := by
  unfold tokAuth
  iintro
  imod (ghost_map_alloc_empty (GF := GF) (K := GoString × GoString) (V := Unit)) with ⟨%γ, H⟩
  imodintro
  iexists γ
  iframe H
  iintro !> %k %hk
  simp at hk

/-- **Issuing** `token` to `user`: the element, whether or not it was issued before. -/
theorem tokIssue (γa : AuthNames) (S : GMap (GoString × GoString) Unit) (token user : GoString) :
    tokAuth (GF := GF) γa.tok S ⊢
      |==> ∃ S' : GMap (GoString × GoString) Unit, tokAuth γa.tok S' ∗ tokIssued γa token user := by
  unfold tokAuth tokIssued
  iintro ⟨Ha, #Hel⟩
  cases hS : S.lookup (token, user) with
  | some u =>
    imodintro
    iexists S
    iframe Ha
    isplitr
    · iexact Hel
    · cases u
      iapply Hel $$ %(token, user) %hS
  | none =>
    imod (ghost_map_insert_persist (token, user) () hS) $$ Ha with ⟨Ha, #Hnew⟩
    imodintro
    iexists S.insert (token, user) ()
    iframe Ha
    isplitr
    · iintro !> %k %hk
      by_cases hk' : k = (token, user)
      · subst hk'; iexact Hnew
      · iapply Hel $$ %k
        ipureintro
        have hne : (token, user) ≠ k := fun h => hk' h.symm
        simpa [GMap.insert, hne] using hk
    · iexact Hnew

end ghost

/-! ## The binding in a mode -/

section mode
variable {GF : BundledGFunctors} [AllG GF]

/-- **`token` was issued to `user`, in the mode `M`**: in `on γa`, `tokIssued`; in `off` and `any`,
nothing (no verdict is promised there). -/
def tokOk (M : AuthMode) (token user : GoString) : IProp GF :=
  match M with
  | .on γa => tokIssued γa token user
  | _ => iprop(True)

instance tokOk_persistent (M : AuthMode) (token user : GoString) :
    Persistent (tokOk (GF := GF) M token user) := by
  unfold tokOk; cases M <;> infer_instance

end mode

end auth
end EtcdGrove
end Perennial
