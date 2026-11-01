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
public import Perennial.Proof.strings.Base

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
2026-10-25), its prefix without a space (`tokPrefixOk`, 2026-10-30). -/
def tokShape (token : GoString) : Prop :=
  ∃ (pre : GoString) (idx : w64), token = simpleTok pre idx ∧ tokPrefixOk pre

/-- **A token of the simple shape has no space**: its prefix has none, nor `.` or a digit. -/
theorem tokShape_noSpace (token : GoString) (h : tokShape token) : W8 32 ∉ token := by
  obtain ⟨pre, idx, rfl, hp⟩ := h
  intro hm
  simp only [simpleTok, List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · exact hp hm
  · revert hm; decide
  · rw [fmt.decimal_of_nonneg (by word)] at hm
    have := fmt.decimalNat_digits _ _ hm
    revert this; decide

/-- **The server's `"Bearer "` trim leaves a token of the simple shape as it is** (`"Bearer "` has
a space, the token none). -/
theorem tokShape_trimBearer (token : GoString) (h : tokShape token) :
    strings.trimPrefix token go!"Bearer " = token := by
  unfold strings.trimPrefix
  split
  · rename_i hp
    exfalso
    apply tokShape_noSpace token h
    obtain ⟨t, rfl⟩ := hp
    simp
  · rfl

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

/-! ### The rights to issue, by raft index (C1's A1, 2026-10-28)

`applierV3backend.Authenticate` issues `<prefix>.<index>` with the consistent index it reads: per
apply-thread step it only grows, whatever the prefix (which is random, so not known distinct). The
authority of the rights (`ghostMapAuth γf 1`, empty when `NewTokenProvider` makes the provider)
is kept with the bound `n` above every index it has handed out (`freshBelow`): for an index at or
above `n` every prefix's right is still in it (`freshBelow_mint`). -/

theorem decimalNat_inj (a b : Nat) (h : fmt.decimalNat a = fmt.decimalNat b) : a = b := by
  induction a using Nat.strongRecOn generalizing b with
  | _ a ih =>
    rw [fmt.decimalNat_eq a, fmt.decimalNat_eq b] at h
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    try simp only [List.cons.injEq, and_true] at h2
    have ha := Nat.mod_lt a (show 10 > 0 by omega)
    have hb := Nat.mod_lt b (show 10 > 0 by omega)
    have hd : a % 10 = b % 10 := by
      unfold fmt.digitByte at h2
      have := congrArg (fun w : w8 => uint.Z w) h2
      word
    by_cases hA : a < 10 <;> by_cases hB : b < 10 <;> simp only [hA, hB, ↓reduceIte] at h1
    · omega
    · exact absurd h1.symm (fmt.decimalNat_ne_nil _)
    · exact absurd h1 (fmt.decimalNat_ne_nil _)
    · have := ih (a / 10) (by omega) (b / 10) h1
      omega

/-- Two lists ending in `x ++ a`, `x ++ b` with `x` in neither `a` nor `b`: `a = b` (the part after
the last `x`). -/
theorem suffix_after_last {α : Type} (x : α) : ∀ (a b r s : List α), x ∉ a → x ∉ b →
    (a ++ x :: r = b ++ x :: s) → a = b
  | [], [], _, _, _, _, _ => rfl
  | [], y :: b, _, _, _, hb, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact absurd (List.mem_cons_self) hb
  | y :: a, [], _, _, ha, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact absurd (List.mem_cons_self) ha
  | y :: a, z :: b, r, s, ha, hb, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rw [suffix_after_last x a b r s (fun h' => ha (List.mem_cons_of_mem _ h'))
      (fun h' => hb (List.mem_cons_of_mem _ h')) h]

/-- **A simple token's index is determined by the token** (`decimal`'s digits have no `.`). -/
theorem simpleTok_idx_inj (pre pre' : GoString) (i i' : w64)
    (h : simpleTok pre i = simpleTok pre' i') : i = i' := by
  unfold simpleTok at h
  rw [fmt.decimal_of_nonneg (by word), fmt.decimal_of_nonneg (by word)] at h
  have hdot : ∀ n : Nat, W8 46 ∉ fmt.decimalNat n := by
    intro n hm
    have := fmt.decimalNat_digits n _ hm
    revert this; word
  have h' := congrArg List.reverse h
  simp only [List.append_assoc, List.reverse_append] at h'
  have hrev := suffix_after_last (W8 46) _ _ pre.reverse pre'.reverse
    (fun hm => hdot _ (List.mem_reverse.mp hm)) (fun hm => hdot _ (List.mem_reverse.mp hm))
    (by simpa using h')
  have := decimalNat_inj _ _ (List.reverse_inj.mp hrev)
  word

/-- **The rights to issue the tokens of index `n` and above, every prefix's**: the authority of the
rights `γf` whose handed-out tokens are of an index below `n`. -/
def freshBelow (γf : GName) (n : Int) : IProp GF :=
  iprop(∃ F : GMap GoString Unit, ghostMapAuth γf 1 F ∗
    ⌜∀ t, F.lookup t ≠ none → ∃ (pre : GoString) (i : w64), t = simpleTok pre i ∧ uint.Z i < n⌝)

/-- The provider's fresh authority (`NewTokenProvider`'s): nothing handed out. -/
theorem freshBelow_init (γf : GName) :
    ghostMapAuth (GF := GF) γf 1 (∅ : GMap GoString Unit) ⊢ freshBelow γf 0 := by
  iintro Ha
  unfold freshBelow
  iexists ∅
  iframe Ha
  ipureintro
  intro t ht
  simp at ht

/-- A lower bound may grow. -/
theorem freshBelow_mono (γf : GName) (n m : Int) (h : n ≤ m) :
    freshBelow (GF := GF) γf n ⊢ freshBelow γf m := by
  unfold freshBelow
  iintro ⟨%F, Ha, %HF⟩
  iexists F
  iframe Ha
  ipureintro
  intro t ht
  obtain ⟨pre, i, rfl, hi⟩ := HF t ht
  exact ⟨pre, i, rfl, by omega⟩

/-- **Minting the right to issue `<pre>.<x>`** for an index `x` at or above the bound: the bound
moves past `x`. -/
theorem freshBelow_mint (γf : GName) (n : Int) (x : w64) (pre : GoString) (hx : n ≤ uint.Z x) :
    freshBelow (GF := GF) γf n ⊢
      |==> (freshBelow γf (uint.Z x + 1) ∗ ghostMapElem γf (simpleTok pre x) (DFrac.own 1) ()) := by
  unfold freshBelow
  iintro ⟨%F, Ha, %HF⟩
  have hnone : F.lookup (simpleTok pre x) = none := by
    cases hk : F.lookup (simpleTok pre x) with
    | none => rfl
    | some _ =>
      obtain ⟨pre', i, heq, hi⟩ := HF _ (by rw [hk]; simp)
      have := simpleTok_idx_inj _ _ _ _ heq
      subst this; omega
  ihave Hins := ghost_map_insert (GF := GF) (γ := γf) (simpleTok pre x) () hnone $$ Ha
  imod Hins with ⟨Ha, Hel⟩
  imodintro
  iframe Hel
  iexists F.insert (simpleTok pre x) ()
  iframe Ha
  ipureintro
  intro t ht
  by_cases htk : t = simpleTok pre x
  · exact ⟨pre, x, htk, by omega⟩
  · have hne : simpleTok pre x ≠ t := fun h => htk h.symm
    obtain ⟨pre', i, heq, hi⟩ := HF t (by simpa [GMap.insert, hne] using ht)
    exact ⟨pre', i, heq, by omega⟩

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
