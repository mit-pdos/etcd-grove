/-
`(*EtcdServer).Done()` (`interface.go:26-28`): `s.done`.

**Users**: the read loop (`read.go`, `readEnv`'s `Done` row: its `select` arm that ends the loop);
`ReadyNotify`'s and `StopNotify`'s callers use `StopNotify` (same channel).

**Proof sketch**: a read of the read-only field `s.done` (`srvStarted`'s realization); `doneCh s ch`
(2e's), and any goroutine may receive on it (closed only, by `run`'s stop: `recvAny`).

**Changes**: verify round (A7-provability F4, completeness F3): new here (the old tree's
`EtcdServer__Done.lean`), so that `start` can prove 2c's `readEnv` from callee specs.

**Margin**: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

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

/-- **`Done()`**: the channel `run`'s stop closes. -/
def EtcdServer.Done.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvStarted s γ id }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"Done")) (Val #()))
  {{ (ch : Loc), RET #ch; doneCh s ch ∗ Read.recvAny ch }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
