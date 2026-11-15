/-
`verifyConsistentIndexIsLatest(snapshot, cindex)` (`server.go:1200-1208`): `verify.Verify` that the
consistent index is at least the snapshot's index (a panic when `ETCD_VERIFY` is on and it is not).
Internal (`snapshot`).

**Proof sketch**: the premise makes the check pass. **Changes**: over R1's `snapshotPts`.
**Margin**: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false

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

def verifyConsistentIndexIsLatest.spec : Prop :=
  ∀ (sp : Loc) (dq : DFrac) (sn : Raft.Snapshot) (ci : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      Raft.snapshotPts sp dq sn ∗ ⌜uint.nat sn.index ≤ uint.nat ci⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.verifyConsistentIndexIsLatest))
      (Val #sp)) (Val #ci))
  {{ RET #(); Raft.snapshotPts sp dq sn }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
