/-
**Hypothesis: `math.Pow`** (notes/dsv-gryff.md, "Hypotheses"). `gryff.NewEPaxosRMWHandler` computes
the bloom filter's size with `math.Pow` on `float64`s. Perennial `7b2259a12` translates `math.Pow`
names only (`Perennial/Code/math.toml`); the lab proved this spec over its own trusted model
(`Harness/Code/math_extra.lean`, `math.ExtraAssumptions`), which is not allowed here. So it is a
premise (a `Prop` class taken as a section variable up to the top-level statement; no instance).

Why it is true of Go's `math.Pow` (`math/pow.go`): it is total on `float64` arguments (special
cases return `NaN`, `±Inf`, `0` or `1`), touches no memory and does not panic; it returns some
`float64` (here its bits, a `w64`). The spec claims nothing about the value. The spec is the main
tree's `EtcdGrove.math.Pow.spec` (`Spec/math/Pow.lean`, client-go's), one spec per function; the
main tree's `math.Pow.wp_proof` discharges it since dsv-fix4 (below); since 2026-11-26 that is a theorem
(Perennial's `math.wp_Pow`), no longer an axiom.


**dsv-fix4** (mit-pdos/etcd-grove#49 fix 4): no longer a statement premise: the top-level proof builds the instance from the main tree's `EtcdGrove.math.Pow.wp_proof` (a theorem since 2026-11-26).
-/
module

public import Spec.math.Pow

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
  pow : _root_.Perennial.EtcdGrove.math.Pow.spec (GF := GF) (hG := hG)

end

end Perennial.gryff.lib
