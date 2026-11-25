/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4): the package-level `Seed(seed)`
returns, nothing claimed (`math.rand.Seed.spec`, `Spec.lean`). Perennial translates `Seed` names
only (`Perennial/Code/math/rand.toml`). Go's `rand.go` (go1.27.3, lines 400-430): `Seed` reads the
`randseednop` GODEBUG setting and, unless it is `"0"`, returns at once (the default for a main module declaring go 1.24 or later; the kits' `go.mod`s declare
`go 1.27`).
**Environment claim**: the deployment does not set `GODEBUG=randseednop=0`, so `Seed` does nothing:
no precondition, no panic, nothing returned, no state changed (in particular the global generator
stays the runtime's, as Perennial's `isPkgInit math.rand` invariant says). (With
`randseednop=0` Go would reseed a `lockedSource` and swap it into `globalRandGenerator`, which that
invariant does not describe.) The statement premises `gryff.lib.RandSeedHyp` (gryff) and `raxos.hyp.RandHyp`
(QuePaxa, its own copy of the same triple) until dsv-fix4. Review:
`notes/axiom-review/dsv-fix4/math-rand-seed.md`.
-/
module

public import Dsverify.Proof.math.rand.Spec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section ax
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- **Trust-boundary axiom** (the file header). -/
axiom math.rand.Seed.wp_proof : math.rand.Seed.spec (GF := GF) (hG := hG)

end ax

end Perennial
