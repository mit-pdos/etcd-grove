/-
**Hypothesis** `RandSeedHyp GF`: `math/rand`'s package-level `Seed(seed)` (gryff's `NewReplica`
calls `rand.Seed(time.Now().UnixNano()<<4 | int64(id))`). Perennial `7b2259a12` translates
`math/rand` names only (`Perennial/Code/math/rand.toml`: `translate = ["!*"]`); the lab proved it
over its own trusted model (`Harness/TrustedCode/math/rand.lean`), not allowed here. Go's `Seed`
has no precondition, does not panic, returns nothing, and changes only the global source's state,
which no proof here reads (the kit's code never calls the global generator otherwise). The
statement claims exactly that: the shared `math.rand.Seed.spec` (`Dsverify/Proof/math/rand/Spec.lean`,
next to dsv-rabia's `math.rand.Hyps`, which gryff does not need: it never calls `Intn` or `New`).
dsv-quepaxa's `Perennial.raxos.hyp.math.rand.Seed.spec` is textually the same triple (a duplicate to
retire there). A premise of `gryff_remote_robust`; no instance.


**dsv-fix4** (mit-pdos/etcd-grove#49 fix 4): no longer a statement premise: the top-level proof builds the instance from the trust-boundary axiom `math.rand.Seed.wp_proof` (`Dsverify/Proof/math/rand/Seed.lean`; review `notes/axiom-review/dsv-fix4/math-rand-seed.md`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Dsverify.Proof.math.rand.Spec

@[expose] public section

noncomputable section

namespace Perennial.gryff.lib

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- See the file header. -/
class RandSeedHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  seed : _root_.Perennial.math.rand.Seed.spec (GF := GF) (hG := hG)

end Perennial.gryff.lib
