/-
**Hypothesis: `math.Pow`** (notes/dsv-gryff.md, "Hypotheses"). `gryff.NewEPaxosRMWHandler` computes
the bloom filter's size with `math.Pow` on `float64`s. Perennial `7b2259a12` translates `math.Pow`
names only (`Perennial/Code/math.toml`); the lab proved this spec over its own trusted model
(`Harness/Code/math_extra.lean`, `math.ExtraAssumptions`), which is not allowed here. So it is a
premise (a `Prop` class taken as a section variable up to the top-level statement; no instance).

Why it is true of Go's `math.Pow` (`math/pow.go`): it is total on `float64` arguments (special
cases return `NaN`, `±Inf`, `0` or `1`), touches no memory and does not panic; it returns some
`float64` (here its bits, a `w64`). The spec claims nothing about the value.
-/
module

public import Perennial.Proof.math

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.lib

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]

/-- **Hypothesis** (the file header): `math.Pow(x, y)` returns some `float64`. -/
class MathPowHyp (GF : BundledGFunctors) [hG : HeapGS .hasLC GF] [go.Semantics] : Prop where
  pow : ∀ (x y : w64),
    {{ (True : IProp GF) }}
      (App (App (Val (@! math.Pow)) (Val #x)) (Val #y))
    {{ (r : w64), RET #r; True }}

end

end Perennial.gryff.lib
