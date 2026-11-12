/-
## `(*EtcdServer).monitorKVHash()` (`server.go:2274-2303`)

**Users.** `Start` (attached goroutine).

**Proof sketch.** A loop until `stopping` closes that runs the corruption checker's periodic check (a corruption raises `CORRUPT`: an `AlarmRequest`, `EnvStep.alarm` at its commit); every field it reads is in
`isServer`'s realization (the configuration's intervals, the cluster, the corruption checker
`isCorruptionChecker`, the version manager); a proposal goes through 2c's `raftRequest`, whose
apply fires nothing observable or `envUpd`'s step.

**Changes** (from `specs-ref`'s `EtcdServer__monitorKVHash.lean`, over the monitors' configuration fields and a
reader slot of `lgMu`): over `isServer`.

**Margin.** None for safety.

**Integration (I4).** Its `Hash` calls take a share of 3e's `mvccRestoreGate` from the server's
invariant (the snapshot install takes it whole: `applySnapshot`).

Changes: verify-round (A7-completeness F1): takes and gives back the goroutine's `threadTok` (`GoAttach` gives it one; `Notifier.Receive`, `Logger`, `raftRequest` take one).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`monitorKVHash`**: runs until the server stops. -/
def EtcdServer.monitorKVHash.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"monitorKVHash")) (Val #()))
  {{ RET #(); threadTok }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
