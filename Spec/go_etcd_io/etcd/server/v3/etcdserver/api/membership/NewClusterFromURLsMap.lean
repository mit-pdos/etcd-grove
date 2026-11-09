/-
## `NewClusterFromURLsMap(lg, token, urlsmap, opts...)` (`cluster.go:81-95`): names only

**Users.** `bootstrap` (names only), `ReqMembers`. **Why it is true.** A cluster with no backend
and local id `0` (`SetID` sets it later); one member per map entry (`NewMember` with `nil`), an
error on two equal ids or an id `0`; the cluster id from the sorted member ids (`genID`).
**Changes**: new (round 1, completeness F3). **Margin.** The cluster id is not named.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api
public import Spec.go_etcd_io.etcd.server.v3.config.Api
public import Spec.go_uber_org.zap.Api

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

/-- **A cluster view of the initial members** (or an error on a duplicate or zero id). -/
def NewClusterFromURLsMap.spec : Prop :=
  ∀ (lg : Loc) (token : GoString) (m : GoMap) (cl : List (GoString × List GoString)) (opts : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ Zap.isLogger lg ∗ Config.urlsMapStrs m cl }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.membership.NewClusterFromURLsMap)) (Val #lg)) (Val #token)) (Val #m)) (Val #opts))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (γ : CNames) (cid : w64) (ms : List Member),
          isCluster c γ cid (W64 0) ∗ clusterSt γ ⟨ms, []⟩ ∗ beView c ⟨[], []⟩ ∗
          ⌜ms.Perm (initialMembers token cl) ∧ (ms.map (·.id)).Nodup ∧ ∀ x ∈ ms, 0 < x.id⌝) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end Membership
end EtcdGrove
end Perennial
