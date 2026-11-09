/-
## `(*RaftCluster).String()` (`cluster.go:213-229`): names only

**Users.** `NewServer` (`NewServerStats`'s argument), logging. **Why it is true.** A formatting of
the members under the lock. **Changes**: from `specs-ref`. **Margin.** The string is not stated.
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

/-- **A description of the cluster.** -/
def RaftCluster.String.spec : Prop :=
  ∀ (c : Loc) (γ : CNames) (cid lid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ isCluster c γ cid lid }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end Membership
end EtcdGrove
end Perennial
