/-
**The issued tokens** (the auth plan's S5, 2026-10-24; `notes/decisions.md`, "S5 of the auth
plan"). Lean-first (no Rocq counterpart).

A token provider (`TokenProvider`: `tokenSimple`, `tokenJWT`, `tokenNop`) issues tokens
(`assign(ctx, username, rev)`) and later maps a token back to an auth info (`info(ctx, token,
rev)`). The binding the auth store relies on: in the mode `on γa`, `info` returns a user only for a
token that was issued to that user. It is recorded under the ghost name `γa.tok` (`AuthNames`):
`tokIssued γa token user`, persistent, an element of a ghost map keyed by the token: issuing a token
spends the exclusive right to issue it (`tokFresh`), so a token is issued once, to one user, even
after `disable()` cleared the simple provider's map (the auth plan's E2c, 2026-10-25; until then the
key was the pair). The provider holds the authority (`tokAuth`), with every element it has issued
kept persistent, with its spent right and its shape.

Not modelled: a token's expiry (the simple provider's TTL keeper deletes tokens at any time; the
JWT's claims carry an expiry): `info` may refuse any token, and the binding is only about the
tokens it accepts.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Model
public import Perennial.Ghost.GhostMap
public import Perennial.Proof.fmt.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI Iris.ProofMode

section ghost
variable {GF : BundledGFunctors} [AllG GF]

/-- The token the simple provider makes of a prefix and a raft index (`fmt.Sprintf("%s.%d",
prefix, index)`, `simple_token.go`'s `assign`). -/
def simpleTok (pre : GoString) (idx : w64) : GoString :=
  pre ++ go!"." ++ fmt.decimal (uint.Z idx)

/-- **A token of the simple provider's shape** (`<prefix>.<raft index>`; the auth plan's E2c,
2026-10-25). -/
def tokShape (token : GoString) : Prop := ∃ (pre : GoString) (idx : w64), token = simpleTok pre idx

/-- **The token `token` was issued to `user`** under the names `γa` (persistent): an element of a
ghost map keyed by the token (the auth plan's E2c, 2026-10-25: a token is issued once, to one user,
`tokIssued_agree`), and the token is of the simple provider's shape (`tokShape`: the only provider
proved, whose `assign` issues `<prefix>.<raft index>`, `tokIssued_shape`). -/
def tokIssued (γa : AuthNames) (token user : GoString) : IProp GF :=
  iprop(ghostMapElem γa.tok token DFrac.discard user ∗ ⌜tokShape token⌝)

instance tokIssued_persistent (γa : AuthNames) (token user : GoString) :
    Persistent (tokIssued (GF := GF) γa token user) := by
  unfold tokIssued; infer_instance

/-- **A token is issued to one user** (E2c). -/
theorem tokIssued_agree (γa : AuthNames) (token u1 u2 : GoString) :
    tokIssued (GF := GF) γa token u1 ∗ tokIssued γa token u2 ⊢ ⌜u1 = u2⌝ := by
  unfold tokIssued
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  iapply ghostMapElem_agree token γa.tok DFrac.discard DFrac.discard u1 u2 $$ H1 H2

/-- **An issued token has the simple provider's shape** (E2c). -/
theorem tokIssued_shape (γa : AuthNames) (token user : GoString) :
    tokIssued (GF := GF) γa token user ⊢ ⌜tokShape token⌝ := by
  unfold tokIssued
  iintro ⟨-, %h⟩
  ipureintro; exact h

/-- **The right to issue `token`** under the names `γa` (exclusive; the auth plan's S5b,
2026-10-24): an element of the ghost map `γa.fresh`. Whoever chooses a token (the server's
`Authenticate` path, `<prefix>.<raft index>`) holds it once; issuing it spends it (makes it
read-only, `tokIssue`), and the issued tokens' authority keeps the spent element of every token it
has issued (`tokAuth`), so a token whose right is held was not issued yet: `tokIssue` inserts it,
and `assignSimpleTokenToUser`'s panic on a token issued twice is unreachable. -/
def tokFresh (γa : AuthNames) (token : GoString) : IProp GF :=
  ghostMapElem γa.fresh token (DFrac.own 1) ()

/-- Two rights to issue tokens are for different tokens. -/
theorem tokFresh_ne (γa : AuthNames) (t1 t2 : GoString) :
    tokFresh (GF := GF) γa t1 ∗ tokFresh γa t2 ⊢ ⌜t1 ≠ t2⌝ := by
  unfold tokFresh
  iintro ⟨H1, H2⟩
  iapply ghostMapElem_ne γa.fresh t1 t2 (DFrac.own 1) () () $$ H1 H2

theorem discard_own_one_invalid : ¬ ✓ (DFrac.discard • DFrac.own (1 : Qp)) := by
  intro h
  have : ((1 : Qp).val < 1) := h
  simp at this

/-- A spent right (read-only) and a held one are for different tokens. -/
theorem tokSpent_ne (γf : GName) (t1 t2 : GoString) :
    ghostMapElem (GF := GF) γf t1 DFrac.discard () ∗ ghostMapElem γf t2 (DFrac.own 1) () ⊢
      ⌜t1 ≠ t2⌝ := by
  iintro ⟨H1, H2⟩
  iapply ghostMapElem_frac_ne γf t1 t2 DFrac.discard (DFrac.own 1) () () discard_own_one_invalid
    $$ H1 H2

/-- **The provider's authority** over the tokens issued under `γt`, with the rights under `γf`:
the issued map `S` (token to user), each entry with its persistent element, its spent right and its
shape. -/
def tokAuth (γt γf : GName) (S : GMap GoString GoString) : IProp GF :=
  iprop(ghostMapAuth γt 1 S ∗
    □ (∀ (t u : GoString), ⌜S.lookup t = some u⌝ →
      ghostMapElem γt t DFrac.discard u ∗ ghostMapElem γf t DFrac.discard () ∗ ⌜tokShape t⌝))

/-- A fresh authority, no token issued. -/
theorem tokAlloc (γf : GName) : ⊢ |==> ∃ γt : GName, tokAuth (GF := GF) γt γf ∅ := by
  unfold tokAuth
  iintro
  imod (ghost_map_alloc_empty (GF := GF) (K := GoString) (V := GoString)) with ⟨%γ, H⟩
  imodintro
  iexists γ
  iframe H
  iintro !> %t %u %hk
  simp at hk

/-- An element of the issued map is in the authority, with its shape. -/
theorem tokAuth_lookup (γt γf : GName) (S : GMap GoString GoString) (t u : GoString) :
    tokAuth (GF := GF) γt γf S ∗ ghostMapElem γt t DFrac.discard u ⊢
      tokAuth γt γf S ∗ ⌜tokShape t⌝ := by
  unfold tokAuth
  iintro ⟨⟨Ha, #Hel⟩, #He⟩
  icombine Ha He gives %hS
  ihave ⟨-, -, %Hsh⟩ := Hel $$ %t %u %hS
  iframe Ha
  isplitr
  · iexact Hel
  · ipureintro; exact Hsh

/-- **Issuing** `token` (of the simple shape) to `user`, spending the right to issue it: the issued
element and the spent right. -/
theorem tokIssue (γa : AuthNames) (S : GMap GoString GoString) (token user : GoString)
    (hsh : tokShape token) :
    tokAuth (GF := GF) γa.tok γa.fresh S ∗ tokFresh γa token ⊢
      |==> ∃ S' : GMap GoString GoString, tokAuth γa.tok γa.fresh S' ∗ tokIssued γa token user ∗
        ghostMapElem γa.fresh token DFrac.discard () := by
  unfold tokAuth tokIssued tokFresh
  iintro ⟨⟨Ha, #Hel⟩, Hfr⟩
  cases hS : S.lookup token with
  | some u =>
    ihave ⟨-, #Hsp, -⟩ := Hel $$ %token %u %hS
    ihave %Hne := tokSpent_ne γa.fresh token token $$ [$Hsp $Hfr]
    exact absurd rfl Hne
  | none =>
    imod (ghost_map_insert_persist token user hS) $$ Ha with ⟨Ha, #Hnew⟩
    imod (ghostMapElem_persist token γa.fresh (DFrac.own 1) ()) $$ Hfr with #Hsp
    imodintro
    iexists S.insert token user
    iframe Ha
    isplitr
    · iintro !> %t %u %hk
      by_cases hk' : t = token
      · subst hk'
        have hu : u = user := by simpa [GMap.insert] using hk.symm
        subst hu
        isplitr
        · iexact Hnew
        isplitr
        · iexact Hsp
        · ipureintro; exact hsh
      · iapply Hel $$ %t %u
        ipureintro
        have hne : token ≠ t := fun h => hk' h.symm
        simpa [GMap.insert, hne] using hk
    isplitr
    · isplitr
      · iexact Hnew
      · ipureintro; exact hsh
    · iexact Hsp

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

/-- **The right to issue `token`, in the mode `M`**: in `on γa`, `tokFresh`; in `off` and `any`,
nothing (S5b). -/
def freshOk (M : AuthMode) (token : GoString) : IProp GF :=
  match M with
  | .on γa => tokFresh γa token
  | _ => iprop(True)

end mode

end auth
end EtcdGrove
end Perennial
