/-
(The lab's `Harness/Proof/math/rand.lean`, run `rabia-r1wake-1`.) `math/rand`'s specs Rabia's code
and kit use, as **hypotheses** (notes/dsv-rabia.md, "The hypotheses"): Perennial translates
`math/rand` names only (the main tree proves `Float64`/`Int63n` as trust-boundary specs; the lab
proved these over its model), so the specs are the fields of the class `Hyps` (a `Prop`), which
every theorem that calls them takes as an instance argument, up to the kit's closed statement.

Each is what Go's `math/rand` does, up to the values drawn (arbitrary: a proof cannot depend on
them): `NewSource(seed)` returns some `Source`; `New(src)` a fresh `*Rand` the caller owns;
`r.Intn(n)` and the package-level `Intn(n)` (its locked global source) for `n > 0` a number in
`[0, n)`.
-/
module

public import Proof.math.rand.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- `NewSource(seed)`: some `Source`. -/
abbrev math.rand.NewSource.spec : Prop :=
  ∀ (seed : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand }}
      (App (Val (@! math.rand.NewSource)) (Val #seed))
    {{ (src : GoInterface), RET #src; True }}

/-- `New(src)`: a fresh `*Rand`, owned by the caller. -/
abbrev math.rand.New.spec : Prop :=
  ∀ (src : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand }}
      (App (Val (@! math.rand.New)) (Val #src))
    {{ (r : Loc), RET #r; ∃ v : math.rand.Rand, r ↦ v }}

/-- `r.Intn(n)` for `n > 0`, `r` owned: some `x` in `[0, n)`; `r` stays owned. -/
abbrev math.rand.Rand.Intn.spec : Prop :=
  ∀ (r : Loc) (v : math.rand.Rand) (n : w64), 0 < sint.Z n →
    {{ (r ↦ v : IProp GF) }}
      (App (Val (r @!! go.GoType.PointerType math.rand.Rand.ty @!! go!"Intn")) (Val #n))
    {{ (x : w64), RET #x; r ↦ v ∗ ⌜0 ≤ sint.Z x ∧ sint.Z x < sint.Z n⌝ }}

/-- The package-level `Intn(n)` for `n > 0`: some `x` in `[0, n)`. -/
abbrev math.rand.Intn.spec : Prop :=
  ∀ (n : w64), 0 < sint.Z n →
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand }}
      (App (Val (@! math.rand.Intn)) (Val #n))
    {{ (x : w64), RET #x; ⌜0 ≤ sint.Z x ∧ sint.Z x < sint.Z n⌝ }}

end spec

/-- **The hypotheses** (the header). -/
class math.rand.Hyps [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  NewSource : math.rand.NewSource.spec (GF := GF)
  New : math.rand.New.spec (GF := GF)
  Rand_Intn : math.rand.Rand.Intn.spec (GF := GF)
  Intn : math.rand.Intn.spec (GF := GF)

end Perennial
