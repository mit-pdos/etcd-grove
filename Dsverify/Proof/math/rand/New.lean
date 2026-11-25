/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4): `New(src)` of a `*rngSource`
(with its token, `math.rand.isRngSource`) returns a fresh `*Rand` over it (`math.rand.ownRngRand`:
its points-to persistent, since nothing here writes it; the source's token moved into it).
Perennial translates `New` names only (`Perennial/Code/math/rand.toml`). Go's `rand.go`: `func
New(src Source) *Rand { s64, _ := src.(Source64); return &Rand{src: src, s64: s64} }`: an
allocation and a comma-ok type assertion, no panic. The field `New` of the statement premise
`math.rand.Hyps` (rabia, swiftpaxos) until dsv-fix4, there for unnamed tokens. Review:
`notes/axiom-review/dsv-fix4/math-rand-rng.md`.
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
axiom math.rand.New.wp_proof :
  math.rand.New.spec (GF := GF) math.rand.isRngSource math.rand.ownRngRand

end ax

end Perennial
