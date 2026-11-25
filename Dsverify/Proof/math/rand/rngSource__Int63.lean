/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4): `(*rngSource).Int63()`, with
the source's token, returns a non-negative `int64` and keeps the token. Perennial translates
`math/rand` with `(*rngSource).Int63` names only (`Perennial/Code/math/rand.toml`), so it cannot be
proved here. Go's `rng.go`: `func (rng *rngSource) Int63() int64 { return int64(rng.Uint64() &
rngMask) }`, and `Uint64` steps the generator's own state (`tap`, `feed`, `vec`: indices kept in
`[0, rngLen)` and the array `vec` of `rngLen` elements) and returns: no panic, no other state.
Used (with `New.lean`, `NewSource.lean`) to prove `(*Rand).Intn` over `ownRngRand`
(`RandsLinked.lean`), which was the statement premise `math.rand.Hyps` (rabia, swiftpaxos) until
dsv-fix4. Review: `notes/axiom-review/dsv-fix4/math-rand-rng.md`. To retire: Perennial translating
`rngSource`'s methods and `NewSource`/`New`.
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
axiom math.rand.rngSource.Int63.wp_proof : ∀ (p : Loc),
  {{ math.rand.rngTok (GF := GF) p }}
    (App (Val (p @!! go.GoType.PointerType math.rand.rngSource.ty @!! go!"Int63")) (Val #()))
  {{ (x : w64), RET #x; math.rand.rngTok p ∗ ⌜0 ≤ sint.Z x⌝ }}

end ax

end Perennial
