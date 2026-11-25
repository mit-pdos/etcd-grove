/-
**Test only** (the non-vacuity rule; math-rand-isinit, 2026-11-24): the hypothesis class
`math.rand.Hyps` (`Spec.lean`; rabia's and swiftpaxos's premise) holds. Its one field, `rands`,
says some pair of tokens makes `NewSource`'s, `New`'s and `(*Rand).Intn`'s specs true. Here they
are what real Go's are: `isRngSource src`, `src` is a `*rngSource` with its state's exclusive token
`rngTok`; `ownRngRand r`, `r` is a `*Rand` (never written: only `Seed`/`Read` write one) whose
source is such a `*rngSource`, with the token.

`NewSource` and `New` are names only at Perennial 47ec64a9d, and so is `(*rngSource).Int63`: their
specs are **local axioms** of this module (true of Go's code, quoted at each). `(*Rand).Intn` is
translated: its spec is **proved** here from its body (`Intn` → `Int31n`/`Int63n` → `Int31`/`Int63`
→ the source's `Int63`), as Perennial proves it over the runtime's source
(`Perennial/Proof/math/rand/Rand__*.lean`), with the token threaded through. No statement or proof
imports this module.
-/
module

public import Dsverify.Proof.math.rand.Spec
public import Perennial.Proof.math.rand.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace math.rand.instances

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section tokens
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- The exclusive token of a `*rngSource`'s state (its `tap`, `feed` and `vec`, which `Int63`
writes: Go's `rngSource` is not safe for concurrent use). Opaque: real Go's. -/
opaque rngTok : Loc → IProp GF := fun _ => iprop(True)

/-- `src` is a `*rngSource`, with its token (what `NewSource` returns). -/
def isRngSource (src : GoInterface) : IProp GF :=
  iprop(∃ p : Loc, ⌜src = interface.mkOk (go.PointerType rngSource.ty) #p⌝ ∗ rngTok p)

/-- `r` is a `*Rand` over a `*rngSource`, with the source's token (what `New` returns). -/
def ownRngRand (r : Loc) : IProp GF :=
  iprop(∃ (p : Loc) (v : Rand), r ↦□ v ∗
    ⌜v.src' = interface.mkOk (go.PointerType rngSource.ty) #p⌝ ∗ rngTok p)

/-- **Local axiom (test-only; in no statement's trust base)**: `(*rngSource).Int63()`, with the
source's token: a non-negative `int64`, the token kept. Go's `rng.go`:
`func (rng *rngSource) Int63() int64 { return int64(rng.Uint64() & rngMask) }`, and `Uint64` steps
the generator's own state (`tap`, `feed`, `vec`) and returns: no panic, no other state. -/
axiom local_rngSource_Int63 : ∀ (p : Loc),
  {{ rngTok (GF := GF) p }}
    (App (Val (p @!! go.GoType.PointerType rngSource.ty @!! go!"Int63")) (Val #()))
  {{ (x : w64), RET #x; rngTok p ∗ ⌜0 ≤ sint.Z x⌝ }}

/-- **Local axiom (test-only)**: `NewSource(seed)` returns a fresh `*rngSource`, with its token. Go's
`rand.go`: `func NewSource(seed int64) Source { return newSource(seed) }`, and `newSource` allocates
`rng := new(rngSource)`, seeds it (`rng.Seed(seed)`, writing only `rng`) and returns `rng`. -/
axiom local_NewSource : math.rand.NewSource.spec (GF := GF) isRngSource

/-- **Local axiom (test-only)**: `New(src)` of a `*rngSource` returns a fresh `*Rand` over it (its
points-to kept persistent: nothing here writes it), the source's token moved into it. Go's
`rand.go`: `func New(src Source) *Rand { s64, _ := src.(Source64); return &Rand{src: src, s64: s64} }`. -/
axiom local_New : math.rand.New.spec (GF := GF) isRngSource ownRngRand

end tokens

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : math.rand.Assumptions]

theorem Rand_Int63_rng : ∀ (r : Loc),
    {{ ownRngRand (GF := GF) r }}
      (App (Val (r @!! go.GoType.PointerType Rand.ty @!! go!"Int63")) (Val #()))
    {{ (x : w64), RET #x; ownRngRand r ∗ ⌜0 ≤ sint.Z x⌝ }} := by
  intro r
  wp_start as Hr
  iunfold ownRngRand at Hr
  icases Hr with ⟨%p, %v, #Hr, %Hsrc, Htok⟩
  ihave #Hr0 := Hr
  wp_auto
  iStructNamed Hr
  wp_auto
  simp only [Hsrc, interface.mkOk]
  wp_apply local_rngSource_Int63 $$ Htok as %x ⟨Htok, %Hx⟩
  iapply HΦ
  isplitl [Htok]
  · iunfold ownRngRand
    iexists p, v
    iframe Hr0 Htok
    ipureintro; exact Hsrc
  · ipureintro; exact Hx

theorem Rand_Int31_rng : ∀ (r : Loc),
    {{ ownRngRand (GF := GF) r }}
      (App (Val (r @!! go.GoType.PointerType Rand.ty @!! go!"Int31")) (Val #()))
    {{ (x : w32), RET #x; ownRngRand r ∗ ⌜0 ≤ sint.Z x⌝ }} := by
  intro r
  wp_start as Hr
  wp_auto
  wp_apply Rand_Int63_rng $$ Hr as %x ⟨Hr, %Hx⟩
  iapply HΦ
  iframe Hr
  ipureintro; exact math.rand.int31_nonneg_of_int63 x Hx

theorem Rand_Int31n_rng : ∀ (r : Loc) (n : w32),
    {{ ownRngRand (GF := GF) r ∗ ⌜0 < sint.Z n⌝ }}
      (App (Val (r @!! go.GoType.PointerType Rand.ty @!! go!"Int31n")) (Val #n))
    {{ (x : w32), RET #x; ownRngRand r ∗ ⌜0 ≤ sint.Z x ∧ sint.Z x < sint.Z n⌝ }} := by
  intro r n
  wp_start as ⟨Hr, %Hn⟩
  wp_auto
  wp_if_destruct
  · exfalso; word
  wp_if_destruct
  · wp_apply Rand_Int31_rng $$ Hr as %x ⟨Hr, %Hx⟩
    iapply HΦ
    iframe Hr
    ipureintro
    have hm : sint.Z (n - W32 1) = sint.Z n - 1 := by word
    have := math.rand.and_toInt_bounds x (n - W32 1) (by word)
    simp only [sint.Z] at hm this ⊢
    omega
  simp only [show ¬uint.Z n = 0 by word, ↓reduceIte]
  wp_auto
  wp_apply Rand_Int31_rng $$ Hr as %x ⟨Hr, %Hx⟩
  ihave IH : iprop(∃ (y : w32), "v" ∷ v_ptr ↦ y ∗ "Hr" ∷ ownRngRand r ∗ "%Hy" ∷ ⌜0 ≤ sint.Z y⌝)
    $$ [v Hr]
  · iexists x; iframe; ipureintro; exact Hx
  wp_for IH
  wp_if_destruct
  · wp_apply Rand_Int31_rng $$ Hr as %x' ⟨Hr, %Hx'⟩
    try wp_auto
    wp_for_post
    iframe
    iexists x'; iframe; ipureintro; exact Hx'
  · simp only [show ¬sint.Z n = 0 by word, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe Hr
    ipureintro; exact math.rand.srem_bounds y n Hy Hn

theorem Rand_Int63n_rng : ∀ (r : Loc) (n : w64),
    {{ ownRngRand (GF := GF) r ∗ ⌜0 < sint.Z n⌝ }}
      (App (Val (r @!! go.GoType.PointerType Rand.ty @!! go!"Int63n")) (Val #n))
    {{ (x : w64), RET #x; ownRngRand r ∗ ⌜0 ≤ sint.Z x ∧ sint.Z x < sint.Z n⌝ }} := by
  intro r n
  wp_start as ⟨Hr, %Hn⟩
  wp_auto
  wp_if_destruct
  · exfalso; word
  wp_if_destruct
  · wp_apply Rand_Int63_rng $$ Hr as %x ⟨Hr, %Hx⟩
    iapply HΦ
    iframe Hr
    ipureintro
    have hm : sint.Z (n - W64 1) = sint.Z n - 1 := by word
    have := math.rand.and_toInt_bounds x (n - W64 1) (by word)
    simp only [sint.Z] at hm this ⊢
    omega
  simp only [show ¬uint.Z n = 0 by word, ↓reduceIte]
  wp_auto
  wp_apply Rand_Int63_rng $$ Hr as %x ⟨Hr, %Hx⟩
  ihave IH : iprop(∃ (y : w64), "v" ∷ v_ptr ↦ y ∗ "Hr" ∷ ownRngRand r ∗ "%Hy" ∷ ⌜0 ≤ sint.Z y⌝)
    $$ [v Hr]
  · iexists x; iframe; ipureintro; exact Hx
  wp_for IH
  wp_if_destruct
  · wp_apply Rand_Int63_rng $$ Hr as %x' ⟨Hr, %Hx'⟩
    try wp_auto
    wp_for_post
    iframe
    iexists x'; iframe; ipureintro; exact Hx'
  · simp only [show ¬sint.Z n = 0 by word, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe Hr
    ipureintro; exact math.rand.srem_bounds y n Hy Hn

/-- `(*Rand).Intn`'s spec over `ownRngRand`, proved (the field `RandSpecs.Rand_Intn`). -/
theorem Rand_Intn_rng : math.rand.Rand.Intn.ownSpec (GF := GF) ownRngRand := by
  intro r n hn
  wp_start as Hr
  wp_auto
  wp_if_destruct
  · exfalso; word
  wp_if_destruct
  · have Hn32 : sint.Z (W32 (sint.Z n)) = sint.Z n := by word
    wp_apply Rand_Int31n_rng $$ [Hr] as %x ⟨Hr, %Hx⟩
    · iframe Hr; ipureintro; rw [Hn32]; exact hn
    iapply HΦ
    iframe Hr
    ipureintro
    rw [Hn32] at Hx
    word
  · wp_apply Rand_Int63n_rng $$ [Hr] as %x ⟨Hr, %Hx⟩
    · iframe Hr; ipureintro; exact hn
    try wp_auto
    iapply HΦ
    iframe Hr
    ipureintro
    word

/-- **The instance** (a theorem): `math.rand.Hyps`, from the local axioms above and the proof of
`(*Rand).Intn`. -/
theorem hyps_holds : math.rand.Hyps GF :=
  ⟨⟨isRngSource, ownRngRand, ⟨local_NewSource, local_New, Rand_Intn_rng⟩⟩⟩

end proof

end math.rand.instances
end Perennial
