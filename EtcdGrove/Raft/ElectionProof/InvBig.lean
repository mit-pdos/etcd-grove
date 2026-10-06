/-
Port of `election_proof/inv_big.v` (at feb5c73d4; unchanged since `main`): `math/big.Int`,
abstractly.

`lockedRand.Intn` -- the RNG behind `raft.resetRandomizedElectionTimeout` -- goes
through `math/big`: `big.NewInt(int64(n))` builds the bound, `crypto/rand.Int` returns
a `*big.Int` below it, and `big.Int.Int64` reads the result back. None of that is raft
code, none of it is translated, and none of it is in scope: the RNG is on the declared
trust boundary (main's notes/STATUS.md, "Trust base").

So this file states the one abstraction the three assumed triples share. **The whole
trust surface of this file is one line**, the abstract predicate below, and the
triples that consume it live in their own collections (`Spec/big_NewInt.lean`,
`Spec/rand_Int.lean`, `Spec/big_Int__Int64.lean`).
-/
import EtcdGrove.Raft.ElectionProof.Defs

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- `ownBigInt p z`: the `big.Int` at `p` has value `z`. Abstract, because the
representation is not translated; exclusive (not persistent), because a `big.Int` is
mutable in Go (`Set`, `Add`, … write through the pointer), so two values for one `p`
must not be simultaneously assertable. -/
axiom ownBigInt {GF : BundledGFunctors} : Loc → Int → IProp GF

end EtcdGrove
end Perennial
