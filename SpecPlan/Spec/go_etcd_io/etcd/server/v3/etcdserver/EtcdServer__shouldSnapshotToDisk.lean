/-
`(*EtcdServer).shouldSnapshotToDisk(ep)` (`server.go:1251-1253`): forced and not at the last disk
snapshot, or past it by more than `SnapshotCount`. Internal (`snapshotIfNeededAndCompactRaftLog`).

**Proof sketch**: reads `s.forceDiskSnapshot` (the thread's `forceSnapW`), `s.Cfg.SnapshotCount`
(read-only, `srvNode`), `ep`'s indices. **Changes**: over `applyThread`. **Margin**: the result's
formula is not stated (its caller's spec holds either way); a `true` implies `appliedi ≠ diskSnap`.

Changes: re-review (RR1): takes `srvStarted s γ id` (persistent; its callers `applyAll`, `apply`, `snapshotIfNeededAndCompactRaftLog` hold it): `s.Cfg.SnapshotCount` (`server.go:1252`), which `start` defaults, is read-only from then on (`srvStarted`'s).
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

def EtcdServer.shouldSnapshotToDisk.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (ep : Loc) (p : Progress),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvStarted s γ id ∗ applyThread s γ ep p }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"shouldSnapshotToDisk")) (Val #ep))
  {{ (b : Bool), RET #b; applyThread s γ ep p ∗ ⌜b = true → p.appliedi ≠ p.diskSnap⌝ }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
