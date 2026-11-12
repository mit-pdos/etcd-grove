/-
## `NewMessage(rs, rc, rcSize)` (`message.go:41-48`): trusted (names only)

**Users.** 2d's `createMergedSnapshotMessage` (the raft `MsgSnap`, the backend snapshot's reader,
its size). **Why it is true.** A struct literal: the reader wrapped to `rcSize` bytes
(`ioutil.NewExactReadCloser`), the total size `proto.Size(rs) + rcSize`, a channel of capacity 1.
The axiom sweep's B3-3: a nil reader panics at the close (`rcClose`), a negative size breaks the
size's sign (the premise).
**Changes** (from `specs-ref`'s `NewMessage.lean`): the close contract and the size premise (the
sweep's decided repair). **Margin.** The size is not stated.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Api
public import SpecPlan.Spec.go_uber_org.zap.Api
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Snap

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.snap.Assumptions]

/-- **A merged snapshot message** to the raft message's recipient. -/
def NewMessage.spec : Prop :=
  ∀ (rs : Loc) (dq : DFrac) (m : Raft.Msg) (rc : GoInterface) (sz : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap ∗ Raft.msgPts rs dq m ∗ rcClose rc ∗ ⌜0 ≤ sint.Z sz⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.snap.NewMessage)) (Val #rs)) (Val #rc)) (Val #sz))
  {{ (p : Loc), RET #p; ∃ tot : w64, isMessage p m.to tot ∗ msgClose p ∗ ⌜0 ≤ sint.Z tot⌝ }}

end spec

end Snap
end EtcdGrove
end Perennial
