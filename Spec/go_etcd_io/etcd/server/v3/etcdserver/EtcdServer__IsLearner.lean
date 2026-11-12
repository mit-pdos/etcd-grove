/-
`s.IsLearner()` (`server.go`; names-only, the trust boundary of unit P3b, until D43 M4,
2026-10-26: translated over the cluster's `IsLocalMemberLearner`). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.IsLearner()` (`s.cluster.IsLocalMemberLearner()`: the local member's `IsLearner`, read
under the cluster's mutex, `isRaftCluster`) returns some boolean. (Until D43 M4, 2026-10-26, given
that the local member is in the members map, `membership.localKept`: `IsLocalMemberLearner`
panicked otherwise; the fork's fix returns `false`.) -/
abbrev EtcdServer.IsLearner.spec : Prop :=
  -- (D43 M4, 2026-10-26) at any side condition of the cluster's lock invariant
  ∀ (s c : Loc) (RM : membership.RcSide GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvClusterAddr s ↦□ c ∗ membership.isRaftClusterG c RM }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"IsLearner")) (Val #()))
  {{ (b : Bool), RET #b; True }}

/-- The static cluster's (`isRaftCluster`). -/
theorem EtcdServer.IsLearner.spec_static (h : EtcdServer.IsLearner.spec (GF := GF) (hG := hG))
    (s c : Loc) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvClusterAddr s ↦□ c ∗ membership.isRaftCluster c }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"IsLearner")) (Val #()))
  {{ (b : Bool), RET #b; True }} := by
  rw [(membership.isRaftCluster_static c).to_eq]
  exact h s c _

end spec

end EtcdGrove
end Perennial
