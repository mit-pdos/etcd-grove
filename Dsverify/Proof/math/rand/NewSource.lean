/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4): `NewSource(seed)` returns a
fresh `*rngSource` with its token (`math.rand.isRngSource`, `RngDefs.lean`). Perennial translates
`NewSource` names only (`Perennial/Code/math/rand.toml`). Go's `rand.go`: `func NewSource(seed
int64) Source { return newSource(seed) }`, and `newSource` declares `var rng rngSource`, seeds
it (`rng.Seed(seed)`, writing only `rng`'s own state: `seed` is reduced modulo `int32max` and the
array filled from the constant table `rngCooked`) and returns `&rng` (escaping: a fresh heap object): no panic for any seed. The
field `NewSource` of the statement premise `math.rand.Hyps` (rabia, swiftpaxos) until dsv-fix4,
there for an unnamed token. Review: `notes/axiom-review/dsv-fix4/math-rand-rng.md`.
-/
module

public import Dsverify.Proof.math.rand.RngDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section ax
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- **Trust-boundary axiom** (the file header). -/
axiom math.rand.NewSource.wp_proof : math.rand.NewSource.spec (GF := GF) math.rand.isRngSource

end ax

end Perennial
