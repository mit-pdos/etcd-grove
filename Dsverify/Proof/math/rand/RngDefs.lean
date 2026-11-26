/-
The vocabulary of `math/rand`'s per-function specs (`NewSource.lean`, `New.lean`,
`rngSource__Int63.lean`; dsv-fix4, mit-pdos/etcd-grove#49 fix 4; axioms until dsv-retire-2, proved from
Perennial's linked results since): fixed predicates, so that the
specs of `math.rand.Hyps` (`Spec.lean`) become axioms of the real functions (until dsv-fix4 the
statement's premise `math.rand.Hyps` said only that **some** pair of tokens makes them true).

* `rngTok p`: the exclusive token of the state of the `*rngSource` at `p` (its `tap`, `feed` and
  `vec`, which `Int63` writes: Go's `rngSource` is not safe for concurrent use): Perennial's
  `math.rand.ownRngSource p` (the source's points-to, its indices in range), since dsv-retire-2
  (#49 step 2), when Perennial translated `NewSource`, `New` and `rngSource`'s methods; until then
  an opaque predicate of trust-boundary axioms.
* `isRngSource src`: `src` is a `*rngSource`, with its token (what `NewSource` returns).
* `ownRngRand r`: `r` is a `*Rand` (never written after `New`: only `Seed`/`Read` write one) whose
  source is such a `*rngSource`, with the source's token (what `New` returns).
-/
module

public import Dsverify.Proof.math.rand.Spec
public import Perennial.Proof.math.rand.Link

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace math.rand

section tokens
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- The exclusive token of a `*rngSource`'s state (the file header): Perennial's. -/
def rngTok (p : Loc) : IProp GF := ownRngSource p

/-- `src` is a `*rngSource`, with its token (what `NewSource` returns). -/
def isRngSource (src : GoInterface) : IProp GF :=
  iprop(∃ p : Loc, ⌜src = interface.mkOk (go.PointerType rngSource.ty) #p⌝ ∗ rngTok p)

/-- `r` is a `*Rand` over a `*rngSource`, with the source's token (what `New` returns). -/
def ownRngRand (r : Loc) : IProp GF :=
  iprop(∃ (p : Loc) (v : Rand), r ↦□ v ∗
    ⌜v.src' = interface.mkOk (go.PointerType rngSource.ty) #p⌝ ∗ rngTok p)

end tokens

end math.rand
end Perennial
