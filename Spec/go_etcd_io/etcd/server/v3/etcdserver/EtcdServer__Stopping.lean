/-
`(*EtcdServer).Stopping()` (`interface.go:42-44`): `s.stopping`.

**Users**: the read loop (`readEnv`'s `Stopping` row), `revokeExpiredLeases`' per-lease wait,
`sendMergedSnap`'s goroutine.

**Proof sketch**: a read of the read-only field `s.stopping` (`srvStarted`): 2e's `stoppingCh`,
closed only by `run`'s stop (`recvAny`).

**Changes**: verify round (A7-provability F4, completeness F3): new here (the old tree's
`EtcdServer__Stopping.lean`).

**Margin**: none.
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

/-- **`Stopping()`**: the channel closed when the stop begins. -/
def EtcdServer.Stopping.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvStarted s γ id }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"Stopping")) (Val #()))
  {{ (ch : Loc), RET #ch; stoppingCh ch ∗ Read.recvAny ch }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
