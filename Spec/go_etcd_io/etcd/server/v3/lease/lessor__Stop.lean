/-
`(*lease.lessor).Stop()` (`lessor.go`). Lean-first (no Rocq counterpart); R2b-3c part 2
(2026-11-04, the user's approval), for `EtcdServer.Cleanup`; until 2026-11-18 an axiom at the trust
boundary (names-only), since the lessor-noax stage translated with its body and proved
(`Proof/.../lease/lessor__Stop.lean`), over `lessorStopTok`, now a definition.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **`le.Stop()`** of the lessor `lp`, with the right to stop it (`lessorStopTok lp`, `NewLessor`'s).
Why it is true of the Go code (`lessor.go:615-618`, at the etcd pin): `Stop` is
`close(le.stopC); <-le.doneC`. The close panics only on a closed channel: `newLessor` makes `stopC`
and only `Stop` closes it, and the right is given once and consumed here. The receive cannot panic;
it returns once `runLoop` (forked by `newLessor`) returns -- its `select` takes `stopC`'s close, and
its deferred `close(le.doneC)` runs -- or blocks, which partial correctness allows. `runLoop` runs
from `NewLessor` on (its effects are in `NewLessor`'s statement), so stopping it adds no behavior;
the lessor's other methods do not depend on it. Nothing comes back: no client needs the stopped
loop's state. (2026-11-18) Proved: the stop channels are broadcast channels (`lessorStopTok`); that
`runLoop` closes `doneC` is `NewLessor`'s (still assumed). -/
abbrev lease.lessor.Stop.spec : Prop :=
  ∀ (lp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lease.lessorStopTok lp }}
    (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!! go!"Stop"))
      (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
