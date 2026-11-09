/-
## `(*Periodic).Run()` (`periodic.go`): translated

**Users.** `start` (once).
**Proof sketch.** starts the compaction loop on a goroutine (it calls `Rev` and `Compact` until stopped): under the compactor's mutex or its context; the loop's calls through
`revGetter` and `compactable` (the handle's). **Changes**: from `specs-ref`'s `Periodic__Run.lean`:
no run token (any number of calls is safe). **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Api
public import Spec.go_uber_org.zap.Api

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
def Periodic.Run.spec : Prop :=
  ∀ (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ isPeriodic p ∗ threadTok }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic.ty @!! go!"Run")) (Val #()))
  {{ RET #(); True }}

end spec

end V3compactor
end EtcdGrove
end Perennial
