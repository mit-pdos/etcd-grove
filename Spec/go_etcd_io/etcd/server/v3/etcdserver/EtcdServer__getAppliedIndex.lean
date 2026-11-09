/-
`(*EtcdServer).getAppliedIndex()` (`server.go:1718`): an atomic load.

**Users**: `AppliedIndex()` (the read loop's `server` interface, 2c's `readEnv`: `A i`), the request
path's gap check (`v3_server.go`, 2c), `isLearnerReady`, the lease checks. Snippet `apply.go`
(`ReqAppliedRead`).

**Proof sketch**: the load of `s.appliedIndex` in its invariant (`srvNode`). **Changes**: over
`srvApplied`. **Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The applied index**: the member has applied that far. -/
def EtcdServer.getAppliedIndex.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvNode s γ id }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"getAppliedIndex")) (Val #()))
  {{ (v : w64), RET #v; srvApplied s γ (uint.nat v) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
