/-
`newRaftNode(cfg)` (`raft.go:120-153`): the member's raft node driver: raft's logger set to the
member's (zap's adapter), the tick lock, the contention detector, the channels (`readStateC` of
capacity 1, `msgSnapC` of `maxInFlightMsgSnap`, `applyc` unbuffered, `stopped`, `done`), and a
ticker of the heartbeat (none for a zero heartbeat).

**Users**: `bootstrappedRaft.newRaftNode` (`bootstrap.go:599`, batch 2e), whose result `NewServer`
copies into `s.r` (`rnInit_place`). Snippet `raftnode.go` (`ReqDriverLoop`).

**Proof sketch**: `NewRaftLoggerZap(cfg.lg)` (a `raft.Logger` meeting R1's `loggerOk`: 2e's zap
adapter, `zap_raft.go`), `raft.SetLogger` (R2's `SetLogger.spec`); the struct with its channels
(Perennial's `make`), `contention.NewTimeoutDetector` (2e's), `time.Now()`; the heartbeat is
non-negative (`time.NewTicker` panics on a negative one; a zero one gives an empty ticker whose
channel is nil: the loop never ticks, a liveness matter only). The value's resources are the
configuration's (`rnCfgOk`) and the channels' fresh invariants (`rnInit`).

**Changes** from `specs-ref`'s spec (the `RNNames` record, the storage's key, `nodeStartedFresh`):
over `rnCfgOk`/`rnInit`; any start (fresh, restart, join): the driver does not care. The heartbeat
premise is `0 ≤` (was positive; 2e's provisional slot `raftNodeBootCfg` may relax to it). A `nil`
logger (the default zap config, which `log.Fatalf`s if it cannot build one) is outside: etcd always
passes one. **Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply
public import Spec.go_uber_org.zap.Api

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

/-- **A new driver** over the configuration's node, storages and transport. -/
def newRaftNode.spec : Prop :=
  ∀ (cv : go_etcd_io.etcd.server.v3.etcdserver.raftNodeConfig) (γ : Names) (id : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      rnCfgOk cv γ id n ∗ Zap.isLogger cv.lg' ∗ ⌜0 ≤ sint.Z cv.heartbeat'⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.newRaftNode)) (Val #cv))
  {{ (r : Loc), RET #r; ∃ v, r ↦ v ∗ rnInit v γ id n }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
