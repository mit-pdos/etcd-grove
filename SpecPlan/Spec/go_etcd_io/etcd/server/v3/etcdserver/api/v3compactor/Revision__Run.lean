/-
## `(*Revision).Run()` (`revision.go`): translated

**Users.** `start` (once).
**Proof sketch.** starts the compaction loop on a goroutine (it calls `Rev` and `Compact` until stopped): under the compactor's mutex or its context; the loop's calls through
`revGetter` and `compactable` (the handle's). **Changes**: from `specs-ref`'s `Revision__Run.lean`:
no run token (any number of calls is safe). **Margin.** None.
Changes: verify-round (A7 completeness F2): the compactor's handles carry the gate `R` of its `Compactable`
(`compactable c R`: `Compact` is safe once `□ R`, the server's start); `Run` takes `□ R`.
Changes: re-review (RR-server-core RR3, by server-core): `Run` gives the caller's `threadTok` back: the loop is a goroutine of its own (`go func()`, `revision.go:67`) and runs on its fork's fresh token (`wp_fork_tok_body`); `Run`'s own body before the `go` does nothing else. (`start` must return its caller's token: `Start.spec`.)
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Api
public import SpecPlan.Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3compactor

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Assumptions]

/-- **`Run`**: starts the compaction loop on a goroutine. -/
def Revision.Run.spec : Prop :=
  ∀ (R : IProp GF) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ isRevision p R ∗ threadTok ∗ □ R }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Revision.ty @!! go!"Run")) (Val #()))
  {{ RET #(); threadTok }}

end spec

end V3compactor
end EtcdGrove
end Perennial
