/-
## `(*RaftCluster).SetVersionChangedNotifier(n)` (`cluster.go:252-254`): names only

**Users.** `NewServer` (`server.go:334`). **Why it is true.** A field set under the lock; the
cluster's lock invariant keeps the notifier with what `SetVersion` needs to call its `Notify`
(pkg notify's `Notifier.Notify.spec`: its update over `notifyCount`, fired in the invariant
given here). **Changes**: from `specs-ref`. Second pass (A7 completeness S1, server-core's
request 4): the notifier's `notifierAt` and an invariant holding its count are premises, so that
`SetVersion`'s `Notify` is provable; no model effect.
**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api
public import Spec.go_etcd_io.etcd.pkg.v3.notify.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Membership

open Iris Iris.BI EtcdModel Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

/-- **Sets the version-change notifier.** -/
def RaftCluster.SetVersionChangedNotifier.spec : Prop :=
  ∀ (c : Loc) (γ : CNames) (cid lid : w64) (n : Loc) (γn : Notify.NotifyNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ isCluster c γ cid lid ∗
      Notify.notifierAt n γn ∗ inv clusterNotifyN (iprop(∃ k : Nat, Notify.notifyCount γn k)) }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"SetVersionChangedNotifier")) (Val #n))
  {{ RET #(); True }}

end spec

end Membership
end EtcdGrove
end Perennial
