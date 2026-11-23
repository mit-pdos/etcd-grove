/-
(The lab's `Harness/Proof/math/rand.lean`, run `rabia-r1wake-1`.) `math/rand`'s specs Rabia's code
and kit use, as **hypotheses** (notes/dsv-rabia.md, "The hypotheses"): Perennial translates
`math/rand` names only (the main tree proves `Float64`/`Int63n` as trust-boundary specs; the lab
proved these over its model), so the specs are the fields of the class `Hyps` (a `Prop`), which
every theorem that calls them takes as an instance argument, up to the kit's closed statement.

Each is what Go's `math/rand` does, up to the values drawn (arbitrary: a proof cannot depend on
them): `NewSource(seed)` returns a fresh `Source` with its token `isSource src`; `New(src)`, given
that token, a fresh `*Rand` with its token `ownRand r`; `r.Intn(n)`, given `r`'s token, for `n > 0`
a number in `[0, n)`; the package-level `Intn(n)` (its locked global source, safe for concurrent
use) for `n > 0` a number in `[0, n)`. The tokens are exclusive (a `Rand` and its `rngSource` are
not safe for concurrent use) and abstract: the class says some pair of predicates makes the three
specs true (`∃ isSource ownRand, RandSpecs isSource ownRand`); real Go's are "`src` is an
`*rngSource` made by `NewSource`, used by its holder alone" and "`r` is a `*Rand` made by `New` over
such a source, used by its holder alone". So `r.Intn` is not claimed of a `Rand` whose source is
`nil` (the zero `Rand`, where Go panics: #24) or any other `Source`.
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

/-- `NewSource(seed)`: a fresh `Source`, with its token. -/
abbrev math.rand.NewSource.spec (isSource : GoInterface → IProp GF) : Prop :=
  ∀ (seed : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand }}
      (App (Val (@! math.rand.NewSource)) (Val #seed))
    {{ (src : GoInterface), RET #src; isSource src }}

/-- `New(src)` of a source from `NewSource`: a fresh `*Rand`, with its token. -/
abbrev math.rand.New.spec (isSource : GoInterface → IProp GF) (ownRand : Loc → IProp GF) : Prop :=
  ∀ (src : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand ∗ isSource src }}
      (App (Val (@! math.rand.New)) (Val #src))
    {{ (r : Loc), RET #r; ownRand r }}

/-- `r.Intn(n)` for `n > 0`, `r` from `New` (its token): some `x` in `[0, n)`; the token kept. -/
abbrev math.rand.Rand.Intn.spec (ownRand : Loc → IProp GF) : Prop :=
  ∀ (r : Loc) (n : w64), 0 < sint.Z n →
    {{ ownRand r }}
      (App (Val (r @!! go.GoType.PointerType math.rand.Rand.ty @!! go!"Intn")) (Val #n))
    {{ (x : w64), RET #x; ownRand r ∗ ⌜0 ≤ sint.Z x ∧ sint.Z x < sint.Z n⌝ }}

/-- The package-level `Intn(n)` for `n > 0`: some `x` in `[0, n)`. -/
abbrev math.rand.Intn.spec : Prop :=
  ∀ (n : w64), 0 < sint.Z n →
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand }}
      (App (Val (@! math.rand.Intn)) (Val #n))
    {{ (x : w64), RET #x; ⌜0 ≤ sint.Z x ∧ sint.Z x < sint.Z n⌝ }}

end spec

/-- The specs of a `Rand` and its source, for the tokens `isSource` and `ownRand` (the header). -/
structure math.rand.RandSpecs [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics]
    (isSource : GoInterface → IProp GF) (ownRand : Loc → IProp GF) : Prop where
  NewSource : math.rand.NewSource.spec (GF := GF) isSource
  New : math.rand.New.spec (GF := GF) isSource ownRand
  Rand_Intn : math.rand.Rand.Intn.spec (GF := GF) ownRand

/-- **The hypotheses** (the header). -/
class math.rand.Hyps [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  rands : ∃ (isSource : GoInterface → IProp GF) (ownRand : Loc → IProp GF),
    math.rand.RandSpecs GF isSource ownRand
  Intn : math.rand.Intn.spec (GF := GF)

end Perennial
