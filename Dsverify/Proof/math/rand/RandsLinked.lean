/-
`math.rand.Hyps` (`Spec.lean`; until dsv-fix4 a premise of rabia's and swiftpaxos's statements)
**holds**, from per-function trust-boundary axioms over fixed tokens (`RngDefs.lean`: `isRngSource`,
`ownRngRand`, over the opaque `rngTok`): `NewSource` and `New` (names only in Perennial) are the
axioms `math.rand.NewSource.wp_proof` and `math.rand.New.wp_proof`, and so is
`(*rngSource).Int63` (`rngSource__Int63.lean`); `(*Rand).Intn` is translated, and its spec over
`ownRngRand` is **proved** here from its body (`Intn` → `Int31n`/`Int63n` → `Int31`/`Int63` → the
source's `Int63`), as Perennial proves it over the runtime's source
(`Perennial/Proof/math/rand/Rand__*.lean`), with the token threaded through. A linking module (it
applies the axioms); the kits' top-level proofs discharge the former premise with `hyps_holds`.
(Until dsv-fix4 the test-only `RandsInstancesLinked.lean`, with the three axioms local.)
-/
module

public import Dsverify.Proof.math.rand.NewSource
public import Dsverify.Proof.math.rand.New
public import Dsverify.Proof.math.rand.rngSource__Int63

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace math.rand.rng

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

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
  wp_apply math.rand.rngSource.Int63.wp_proof $$ Htok as %x ⟨Htok, %Hx⟩
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

/-- **`math.rand.Hyps` holds** (a theorem, not an instance): from the per-function axioms of
`NewSource` and `New` and the proof of `(*Rand).Intn` above. -/
theorem hyps_holds : math.rand.Hyps GF :=
  ⟨⟨isRngSource, ownRngRand, ⟨math.rand.NewSource.wp_proof, math.rand.New.wp_proof, Rand_Intn_rng⟩⟩⟩

end proof

end math.rand.rng
end Perennial
