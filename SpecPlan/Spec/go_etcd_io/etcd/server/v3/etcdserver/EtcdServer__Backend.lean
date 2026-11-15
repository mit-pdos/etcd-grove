/-
`(*EtcdServer).Backend()` (`server.go:2416-2420`): `s.be` under `bemu`'s read lock.

**Users**: `applyAll` (`VerifyBackendConsistency(s.Backend(), ...)`), v3rpc's `newBackendQuota`
and the maintenance handlers (`Status`, `Defragment`, `Snapshot`, `Hash`).

**Proof sketch**: `bemu.RLock` (the caller's `threadTok`: the lock's reader pool, `srvNode`'s
realization); the current backend (`bemu`'s invariant: 2e's readable handle, at any later backend
too: a snapshot install swaps `s.be` under the write lock and keeps the old one readable until
the stop: 2e's `beReadable`); `RUnlock`.

**Changes**: verify round (A7-provability F7, completeness F3, A8-completeness F5): new here (the
old tree's `EtcdServer__Backend.lean`).

**Margin**: 2e's `beReadable` is still provisional (A8-provability F5: no bridge to 4a's
`Backend.isBackend` yet).
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

/-- **`Backend()`**: the member's current backend, readable. -/
def EtcdServer.Backend.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"Backend")) (Val #()))
  {{ (be : GoInterface), RET #be; ServerStorage.beReadable be ∗ threadTok }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
