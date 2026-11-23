/-
**Hypothesis** `RandSeedHyp GF`: `math/rand`'s package-level `Seed(seed)` (gryff's `NewReplica`
calls `rand.Seed(time.Now().UnixNano()<<4 | int64(id))`). Perennial `7b2259a12` translates
`math/rand` names only (`Perennial/Code/math/rand.toml`: `translate = ["!*"]`); the lab proved it
over its own trusted model (`Harness/TrustedCode/math/rand.lean`), not allowed here. Go's `Seed`
has no precondition, does not panic, returns nothing, and changes only the global source's state,
which no proof here reads (the kit's code never calls the global generator otherwise). The
statement claims exactly that. Same shape as dsv-quepaxa's `math.rand.Seed.spec`
(`Dsverify/Proof/raxos/Hyp.lean`). A premise of `gryff_remote_robust`; no instance.
-/
module

public import Perennial.Proof.ProofPrelude
public import Dsverify.Proof.math.rand.Base

@[expose] public section

noncomputable section

namespace Perennial.gryff.lib

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- See the file header. -/
class RandSeedHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  seed : ∀ (seed : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand }}
      (App (Val (@! _root_.Perennial.math.rand.Seed)) (Val #seed))
    {{ RET #(); True }}

end Perennial.gryff.lib
