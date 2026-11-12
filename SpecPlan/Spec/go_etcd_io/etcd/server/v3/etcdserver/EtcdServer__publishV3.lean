/-
## `(*EtcdServer).publishV3(timeout)` (`server.go:1823-1872`)

**Users.** `Start` (its attached goroutine). What it does for clients: the member's name and client
URLs reach the cluster's members (`EnvStep.publish`, K5) and `ReadyNotify()` closes.

**Proof sketch.** Loop until `stopping` is closed: `raftRequest` (2c) of a `ClusterMemberAttrSet`
under a timeout context; the apply thread (2d) fires `envUpd`'s publication at its commit when the
member is still a member (else nothing: the update aborted). On `nil`, `close(s.readych)` with
`srvPublish` (once), return.

**Changes** (from `specs-ref`'s `EtcdServer__publishV3.lean`): the publication is an environment
step of W0's model (it was invisible to the old KV-only model).

**Margin.** None for safety.

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

/-- **Publishes the member's attributes** until it succeeds or the server stops. -/
def EtcdServer.publishV3.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (tmo : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ srvPublish s ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"publishV3")) (Val #tmo))
  {{ RET #(); threadTok }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
