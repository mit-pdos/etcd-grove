/-
## `(*EtcdServer).IsLearner(…)` (`server.go:2460-2468`): translated

**Users.** 2a's interceptors (`interceptor.go:53`). **Proof sketch.** The membership view's read (`RaftCluster.IsLocalMemberLearner`,
`IsMemberExist`: their updates fired by the server's invariant, which holds `clusterSt`), under the
cluster's mutex (a `threadTok`). **Changes** (from `specs-ref`): over `srvMember`. **Margin.** The
answer is a member's view at some point (2a uses it to refuse: a refusal is a `Step`).
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

/-- **`IsLearner`**: whether the local member is a learner in its view (some answer). -/
def EtcdServer.IsLearner.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat) ,
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvMember s γ id ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"IsLearner")) (Val #()))
  {{ (b : Bool), RET #b; threadTok }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
