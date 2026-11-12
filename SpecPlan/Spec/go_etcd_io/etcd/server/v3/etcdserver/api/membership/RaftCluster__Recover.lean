/-
## `(*RaftCluster).Recover(onSet)` (`cluster.go:262-304`): names only

**Users.** `bootstrap` (`Finalize`: a restart), 2d's `applySnapshot` (after a snapshot's backend is
installed and set: `SetBackend`).

**Why it is true.** Under the lock: the members, removed ids, version and downgrade state loaded
from the backend (`UnsafeLoad`: `beView`), the downgrade check (`MustDetectDowngrade`: `Fatal`,
which does not return, on a cluster version above the server's), `onSet` called with the version
(`api.UpdateCapability`, trusted), metrics. The view becomes the backend's.

**Changes** (from `specs-ref`'s `RaftCluster__Recover.lean`, and the trusted law
`clusterImageOk_restModel`, refuted in part by the sweep: its version premise): the view's update to
the backend's view; no version premise (a downgrade mismatch exits: liveness).

**Margin.** The version is not modelled.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api

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

/-- **Reloads the view from the backend.** -/
def RaftCluster.Recover.spec : Prop :=
  ∀ (c : Loc) (γ : CNames) (cid lid : w64) (f : GoFunc) (stb : ClusterSt) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ isCluster c γ cid lid ∗ beView c stb ∗
      (□ ∀ (lg v : Loc), WP (App (App (Val #f) (Val #lg)) (Val #v)) {{ fun _ => iprop(True) }}) ∗
      (AU <{ ∃∃ (st : ClusterSt), clusterSt γ st }> @ ⊤, ∅ <{ clusterSt γ (stb), COMM Q }>) }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"Recover")) (Val #f))
  {{ RET #(); Q ∗ beView c stb }}

end spec

end Membership
end EtcdGrove
end Perennial
