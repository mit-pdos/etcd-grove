/-
The proof of `types.IDFromString` (`id.go`: `strconv.ParseUint(s, 16, 64)`), over
`strconv.ParseUint`'s spec and `*strconv.NumError`'s `Error` and `Unwrap` (until 2026-11-27 a
trust-boundary axiom). Lean-first.

`ParseUint` reads back what `FormatUint(x, 16)` writes (`types.parseUint_idStr`), and the error it
returns otherwise, a `*NumError` over `ErrSyntax` or `ErrRange`, is an `http.errStrOk` error
(`types.errStrOk_numError`): its `Error` returns, its tree is the `*NumError` over the
`errors.New` leaf it unwraps to.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.IDFromString
public import Perennial.Spec.strconv.ParseUint
public import Perennial.Spec.strconv.NumError__Error
public import Perennial.Spec.strconv.NumError__Unwrap
public import Proof.errors.NewVar

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- `ParseUint` reads a lowercase hexadecimal digit `d < 16` as `d`. -/
theorem types.digitVal_hexDigit (d : Nat) (h : d < 16) :
    internal.strconv.digitVal (types.hexDigit d) = some d := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 ∨
      d = 10 ∨ d = 11 ∨ d = 12 ∨ d = 13 ∨ d = 14 ∨ d = 15 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> rfl

/-- `ParseUint`'s loop reads `hexNatF`'s digits (with enough fuel) of a value up to the maximum. -/
theorem types.parseDigits_hexNatF (M : Nat) :
    ∀ f n, n < f → n ≤ M → internal.strconv.parseDigits 16 M (types.hexNatF f n) 0 = .ok n := by
  intro f
  induction f with
  | zero => intro n h; omega
  | succ f ih =>
    intro n hf hn
    rw [types.hexNatF]
    split
    · next h =>
      rw [internal.strconv.parseDigits_cons_ok (types.digitVal_hexDigit n h) h (by omega)]
      simp [internal.strconv.parseDigits]
    · next h =>
      rw [internal.strconv.parseDigits_append_ok, ih (n / 16) (by omega) (by omega)]
      simp only
      have hm : n % 16 < 16 := Nat.mod_lt n (by omega)
      have he : n / 16 * 16 + n % 16 = n := by omega
      rw [internal.strconv.parseDigits_cons_ok (types.digitVal_hexDigit _ hm) hm (by omega), he]
      rfl

/-- **`ParseUint(id.String(), 16, 64)` is `id`.** -/
theorem types.parseUint_idStr (x : w64) :
    internal.strconv.parseUint (types.idStr x) 16 64 = .ok x.toNat := by
  unfold types.idStr
  rw [internal.strconv.parseUint_of_ne (types.hexNatF_ne_nil _ _ (by omega))]
  apply types.parseDigits_hexNatF _ _ _ (by omega)
  have := x.isLt
  rw [show internal.strconv.effBitSize 64 = 64 from rfl]
  omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.types.Assumptions]

/-- **A `*NumError` over an `errors.New` error is an `errStrOk` error**: its `Error()` returns
(`NumError.Error`, over the leaf's), its tree is the `*NumError` (no `Is`; `Unwrap` gives `Err`)
over the leaf, and it has no `Format` method. -/
theorem types.errStrOk_numError
    (wp_Error : _root_.Perennial.strconv.NumError.Error.spec (GF := GF) (hG := hG))
    (wp_Unwrap : _root_.Perennial.strconv.NumError.Unwrap.spec (GF := GF) (hG := hG))
    (l x : Loc) (fn s msg : GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.strconv ∗
      l ↦□ _root_.Perennial.strconv.NumError.mk fn s
        (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) ∗
      (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
        WP (App (Val #(methods (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
          go!"Error" #x)) (Val #())) {{ Φ }}) ⊢
    http.errStrOk (interface.mkOk (go.GoType.PointerType _root_.Perennial.strconv.NumError.ty) #l) := by
  iintro ⟨#Hpkg, #Hl, #HE⟩
  have hms : methodSet (go.GoType.PointerType _root_.Perennial.strconv.NumError.ty) !! go!"Error" = _ ∧
      methodSet (go.GoType.PointerType _root_.Perennial.strconv.NumError.ty) !! go!"Unwrap" = _ ∧
      methodSet (go.GoType.PointerType _root_.Perennial.strconv.NumError.ty) !! go!"Is" = _ ∧
      methodSet (go.GoType.PointerType _root_.Perennial.strconv.NumError.ty) !! go!"As" = _ ∧
      methodSet (go.GoType.PointerType _root_.Perennial.strconv.NumError.ty) !! go!"Format" = _ :=
    _root_.Perennial.strconv.numError_methodSet
  obtain ⟨hE, hU, hIs, -, hF⟩ := hms
  obtain ⟨-, hleaf, hsIs⟩ := EtcdGrove.errorString_leaf x
  obtain ⟨-, hsU1, hsU2⟩ := hleaf
  unfold http.errStrOk
  iright
  iexists ⟨go.GoType.PointerType _root_.Perennial.strconv.NumError.ty, #l⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %Φ HΦ
    iapply (wp_Error l (_root_.Perennial.strconv.NumError.mk fn s
        (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x))
      DfracDiscarded ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩ rfl)
    · iframe #
      iunfold _root_.Perennial.strconv.errorReturns
      iintro %Ψ HΨ
      iapply HE
      inext
      iapply HΨ
    · inext
      iintro %str -
      iapply HΦ
  isplitr
  · unfold http.errTreeOk
    iintro !> %target %htarget
    iexists (fun e => e = GoInterface.ok
        ⟨go.GoType.PointerType _root_.Perennial.strconv.NumError.ty, #l⟩ ∨
      e = GoInterface.ok ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩),
      (fun _ => False)
    isplitr
    · ipureintro
      refine ⟨Or.inl rfl, ?_⟩
      intro ii tii hS _ _
      rcases hS with h | h <;> cases h <;> exact ⟨_, rfl⟩
    · iintro !> %ii %hS
      rcases hS with h | h <;> cases h
      · unfold _root_.Perennial.errors.errorWalkNode
        simp only [hIs, hU, reduceCtorEq, ↓reduceIte]
        isplitr
        · ipureintro; intro h; cases h
        · iintro !> %Φ - HΦ
          wp_apply (wp_Unwrap l (_root_.Perennial.strconv.NumError.mk fn s
            (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x))
            DfracDiscarded) $$ [$Hl]
          iintro -
          iapply HΦ
          ipureintro
          refine ⟨Or.inr rfl, ?_⟩
          intro c hc
          rw [List.mem_singleton.mp hc]
          exact Or.inr rfl
      · unfold _root_.Perennial.errors.errorWalkNode
        simp only [hsIs, hsU1, hsU2, ↓reduceIte]
        isplitr
        · ipureintro; intro h; cases h
        · ipureintro; intro _ h; cases h
  · ipureintro; exact ⟨hF, hE⟩

theorem types.IDFromString.wp_proof
    (wp_ParseUint : _root_.Perennial.strconv.ParseUint.spec (GF := GF) (hG := hG))
    (wp_Error : _root_.Perennial.strconv.NumError.Error.spec (GF := GF) (hG := hG))
    (wp_Unwrap : _root_.Perennial.strconv.NumError.Unwrap.spec (GF := GF) (hG := hG)) :
    types.IDFromString.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as #Hpkg
  ihave #Hsc : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  ihave Hi := _root_.Perennial.strconv.isInit_access $$ Hsc
  icases Hi with ⟨#HErrRange, #HErrSyntax, -⟩
  wp_auto
  wp_apply (wp_ParseUint s (W64 16) (W64 64) (by decide) (by decide) (by decide) (by decide))
  iintro %x %err Hpost
  cases hp : internal.strconv.parseUint s (sint.nat (W64 16)) (sint.nat (W64 64)) with
  | ok n =>
    simp only
    icases Hpost with %Hpost
    obtain ⟨rfl, rfl⟩ := Hpost
    wp_auto
    iapply HΦ
    isplitr
    · iapply http.errStrOk_nil
    · ipureintro
      intro x' hs
      subst hs
      rw [show sint.nat (W64 16) = 16 from rfl, show sint.nat (W64 64) = 64 from rfl,
        types.parseUint_idStr] at hp
      cases hp
      exact ⟨by simp, rfl⟩
  | errSyntax =>
    simp only
    icases Hpost with ⟨-, Hn⟩
    iunfold _root_.Perennial.strconv.numErrorOf at Hn
    icases Hn with ⟨%l, %e, %Herr, Hl, #HX⟩
    iunfold _root_.Perennial.errors.newVar at HErrSyntax
    icases HErrSyntax with ⟨%xe, #HXg, -, #HXE⟩
    icombine HX HXg gives %he
    subst Herr he
    ipersist Hl
    wp_auto
    iapply HΦ
    isplitr
    · iapply (types.errStrOk_numError wp_Error wp_Unwrap l xe _ s _)
      iframe #
    · ipureintro
      intro x' hs
      subst hs
      rw [show sint.nat (W64 16) = 16 from rfl, show sint.nat (W64 64) = 64 from rfl,
        types.parseUint_idStr] at hp
      cases hp
  | errRange =>
    simp only
    icases Hpost with ⟨-, Hn⟩
    iunfold _root_.Perennial.strconv.numErrorOf at Hn
    icases Hn with ⟨%l, %e, %Herr, Hl, #HX⟩
    iunfold _root_.Perennial.errors.newVar at HErrRange
    icases HErrRange with ⟨%xe, #HXg, -, #HXE⟩
    icombine HX HXg gives %he
    subst Herr he
    ipersist Hl
    wp_auto
    iapply HΦ
    isplitr
    · iapply (types.errStrOk_numError wp_Error wp_Unwrap l xe _ s _)
      iframe #
    · ipureintro
      intro x' hs
      subst hs
      rw [show sint.nat (W64 16) = 16 from rfl, show sint.nat (W64 64) = 64 from rfl,
        types.parseUint_idStr] at hp
      cases hp

end proof

end EtcdGrove
end Perennial
