/-
The trust boundary: `rand.Float64` (`math/rand` is names-only in Perennial).
-/
module

public import Spec.math.rand.Float64

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary**: `rand.Float64()` returns (some `float64`), from any thread, in any state.
Go's documentation (`math/rand`, go1.27.3): "Float64 returns, as a float64, a pseudo-random number
in the half-open interval [0.0,1.0) from the default Source", and "Top-level functions, such as Float64 and Int, are safe for
concurrent use by multiple goroutines" (the package doc). Its source (`src/math/rand/rand.go`):
`func Float64() float64 { return globalRand().Float64() }`; `globalRand` loads (or installs, by a
`CompareAndSwap`) the global `*Rand` (a `runtimeSource` over `runtime.rand`, or a `lockedSource`
under `GODEBUG=randautoseed=0`), and `(*Rand).Float64` computes `float64(r.Int63()) / (1 << 63)`,
drawing again in the (probability 2⁻⁵³) case that it rounds to `1`: no panic, no state a caller
holds. The spec claims less than the documentation (no range), which is all the callers need. -/
axiom rand.Float64.wp_proof : rand.Float64.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
