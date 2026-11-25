/-
`(*membership.RaftCluster).buildMembershipMetric()` (`cluster.go:846-857`; claim #34, stage 2,
2026-11-25: translated with its body, over prometheus's gauge `Set`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Build

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

/-- **`c.buildMembershipMetric()`** (its local id, members map and removed map read, at any
fraction): it returns, the memory unchanged (it sets the package's `knownPeers` gauge for each
member and removed member, when the local id is not `0`). -/
abbrev membership.RaftCluster.buildMembershipMetric.spec : Prop :=
  ∀ (c : Loc) (lid : w64) (dq1 dq2 dq3 dq4 dq5 : DFrac) (mp rp : Loc) (ms : GMap w64 Loc)
    (rm : GMap w64 Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ membership.rcLocalIDAddr c ↦{dq1} lid ∗
      membership.rcMembersAddr c ↦{dq2} mp ∗ mp ↦${dq3} ms ∗
      membership.rcRemovedAddr c ↦{dq4} rp ∗ rp ↦${dq5} rm }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"buildMembershipMetric")) (Val #()))
  {{ RET #(); membership.rcLocalIDAddr c ↦{dq1} lid ∗
      membership.rcMembersAddr c ↦{dq2} mp ∗ mp ↦${dq3} ms ∗
      membership.rcRemovedAddr c ↦{dq4} rp ∗ rp ↦${dq5} rm }}

end spec

end EtcdGrove
end Perennial
