/-
`membership.RaftCluster.updateMembershipMetric` (`cluster.go`: the `known_peers` gauge of the
local member and `peer` set to `1` or `0`, unless the local id is `0`): the trust boundary (names
only; D43 M4, 2026-10-26). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `c.updateMembershipMetric(peer, known)` returns. Faithful: it reads `c.localID` (read-only once
`SetID` ran) and, if non-zero, sets the package's `knownPeers` gauge for the pair of ids
(`prometheus.GaugeVec.WithLabelValues(...).Set`, which neither blocks nor panics on two labels);
it writes no memory the model describes. Called by the cluster's writers under its lock. -/
abbrev membership.RaftCluster.updateMembershipMetric.spec : Prop :=
  ∀ (c : Loc) (lid peer : w64) (known : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.rcLocalIDAddr c ↦□ lid }}
    (App (App (Val (c @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!!
      go!"updateMembershipMetric")) (Val #peer)) (Val #known))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
