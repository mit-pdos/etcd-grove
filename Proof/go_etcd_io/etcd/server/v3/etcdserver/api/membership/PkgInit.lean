/- Package initialization of membership and the dependencies it shares with
storage/schema when decoding the membership of a backend snapshot. -/
module
public import Proof.net.url.PkgInit
public import Proof.encoding.json.Base
public import Net.Proof.models_lab.jsoncodec.Base

public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.membership
public import Proof.go_etcd_io.raft.v3.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Base
public import Proof.go_etcd_io.etcd.api.v3.version.PkgInit
public import Proof.github_com.prometheus.client_golang.prometheus.Labels
public import Proof.github_com.prometheus.client_golang.prometheus.Metric
public import Proof.errors.NewVar
public import Perennial.Proof.internal.bytealg.Base
public import Proof.path.PkgInit

@[expose] public section

noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

-- `etcdserver/version` (types only: `DowngradeInfo`)
namespace go_etcd_io.etcd.server.v3.etcdserver.version

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.version


-- `client/pkg/v3/types` (names only: `ID.String`)
namespace go_etcd_io.etcd.client.pkg.v3.types

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.client.pkg.v3.types


-- `pkg/v3/notify` (moved from `BaseApply.lean`, 2026-10-14, unit P1b: `membership` imports it,
-- for `RaftCluster`'s field types)
namespace go_etcd_io.etcd.pkg.v3.notify

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.notify

-- `encoding/json`: its instance is in `Proof/encoding/json/Base.lean` (2026-11-23)

-- `api/membership` (names only but `RaftCluster.ID`; 2026-10-13, the request path's unit 4c: the
-- package variable `ClusterVersionMetrics`, which the server's `start` sets, holds some
-- `*GaugeVec`, with its label name `cluster_version`: D19l (iii), 2026-10-18)
-- (prove-errinits, 2026-11-19: membership imports `path` for its store paths; until then in
-- the server's `BaseApply.lean`; since L1, 2026-11-24, in `Proof/path/PkgInit.lean`)

namespace go_etcd_io.etcd.server.v3.etcdserver.api.membership

/-- (D43 M4, 2026-10-26) The package's error variables and their messages (`errors.go`: each an
`errors.New(msg)`). -/
def membershipErrMsgs : List (GoString × GoString) :=
  [(ErrIDRemoved, go!"membership: ID removed"),
    (ErrIDExists, go!"membership: ID exists"),
    (ErrIDNotFound, go!"membership: ID not found"),
    (ErrPeerURLexists, go!"membership: peerURL exists"),
    (ErrMemberNotLearner, go!"membership: can only promote a learner member"),
    (ErrTooManyLearners, go!"membership: too many learner members in cluster")]

/-- `api/membership`'s package facts: `ClusterVersionMetrics` (above), and (D43 M4, 2026-10-26)
every error variable its `errors.New` error (`errorsNewVars membershipErrMsgs`), and
(prove-ps2-metrics, 2026-11-22) the metrics of the membership writers' metric updates: the gauge
`isLearner` (its `Set` returns) and the gauge vector `knownPeers`, with its label names. -/
abbrev membershipInit : IProp GF :=
  iprop((∃ gv : Loc,
    globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.membership.ClusterVersionMetrics ↦□ gv ∗
    ⌜EtcdGrove.prometheus.vecLabels gv [go!"cluster_version"]⌝) ∗
    EtcdGrove.errorsNewVars membershipErrMsgs ∗
    (∃ g : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.membership.isLearner ↦□ GoInterface.ok g ∗
      EtcdGrove.prometheus.metric.gaugeSetSpec g) ∗
    (∃ gv : Loc, globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.membership.knownPeers ↦□ gv ∗
      ⌜EtcdGrove.prometheus.vecLabels gv [go!"Local", go!"Remote"]⌝))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership :=
  define_is_pkg_init membershipInit
instance get_isPkgInit_wf_inst [EtcdGrove.prometheus.PromRegGS GF] : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.membership

end init
end Perennial
