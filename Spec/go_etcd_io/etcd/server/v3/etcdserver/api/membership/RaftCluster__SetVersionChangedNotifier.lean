/-
## `(*RaftCluster).SetVersionChangedNotifier(n)` (`cluster.go:252-254`): names only

**Users.** `NewServer` (`server.go:334`). **Why it is true.** A field set under the lock (the
notifier fired at a version change: no model effect). **Changes**: from `specs-ref`.
**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api

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
  ∀ (c : Loc) (γ : CNames) (cid lid : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ isCluster c γ cid lid }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"SetVersionChangedNotifier")) (Val #n))
  {{ RET #(); True }}

end spec

end Membership
end EtcdGrove
end Perennial
