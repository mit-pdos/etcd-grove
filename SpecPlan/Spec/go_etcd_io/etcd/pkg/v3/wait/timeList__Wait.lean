/-
## `(*timeList).Wait(deadline)`

**Users.** `EtcdServer.ApplyWait` (`interface.go:23`, the read loop's `ApplyWait(confirmedIndex)`,
`read.go:135`), `ApplyWaitCommit` (`server.go:630`, `waitAppliedIndex`), `srv.applyWait.Wait`
(`server.go:353`, the lessor's checkpoint wait). Concurrent callers. Snippet:
`examples/specreq/wait/wait.go` (`ReqWaitTime`).

**Proof sketch.** `Lock`; if `last ≥ d`, return `closec` (closed in `init`: the package's fact; the
invariant's `□ P last` and `P`'s downward closure give `□ P d`); else the map's channel for `d`,
made if absent (its close will carry `□ P d`: `Trigger` closes it only at a `d' ≥ d`); `Unlock`.

**Changes.** The old spec returned a `waitBcast ch Q` with `□ (Q -∗ P d)`; restated as one
predicate `timeChan`.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.pkg.v3.wait.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Wait

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.wait.Assumptions]

/-- **A channel closed once the deadline `d` is triggered** (a receive gives `□ P d`). -/
def timeList.Wait.spec : Prop :=
  ∀ (tl : Loc) (P : w64 → IProp GF) (d : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗ timeListAt tl P }}
    (App (Val (tl @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.wait.timeList.ty @!! go!"Wait"))
      (Val #d))
  {{ (ch : Loc), RET #ch; timeChan ch P d }}

end spec
end Wait
end EtcdGrove
end Perennial
