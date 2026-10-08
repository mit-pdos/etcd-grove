/-
`math/big.Int` ownership (port of `election_proof/inv_big.v`, where it was abstract).

`lockedRand.Intn` -- the RNG behind `raft.resetRandomizedElectionTimeout` -- goes
through `math/big`: `big.NewInt(int64(n))` builds the bound, `crypto/rand.Int` returns
a `*big.Int` below it, and `big.Int.Int64` reads the result back. `big.NewInt` and
`big.Int.Int64` are proved in Perennial (`Perennial.Proof.math.big`) against
`math.big.ownInt`, which this file names `ownBigInt`; `crypto/rand.Int` is not
translated and stays assumed (`Spec/rand_Int.lean`), stated over the same predicate.
-/
import EtcdGrove.Raft.Defs
import Perennial.Proof.math.big

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `ownBigInt p z`: the `big.Int` at `p` has value `z` (exclusive, since a `big.Int` is
mutable in Go). -/
abbrev ownBigInt (p : Loc) (z : Int) : IProp GF := _root_.Perennial.math.big.ownInt p z

end

end EtcdGrove
end Perennial
