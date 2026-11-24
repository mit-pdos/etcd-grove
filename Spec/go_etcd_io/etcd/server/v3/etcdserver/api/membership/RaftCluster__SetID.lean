/-
`(*membership.RaftCluster).SetID(localID, cid)` (`cluster.go:238-242`; claim #34, stage 2,
2026-11-25: translated with its body). Lean-first.
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

/-- **`c.SetID(lid, cid)` of a cluster not yet shared** (its local id and id owned, its members map
and removed map read at any fraction): the two fields written (and the membership metric built). -/
abbrev membership.RaftCluster.SetID.spec : Prop :=
  ∀ (c : Loc) (lid cid lid0 cid0 : w64) (dq2 dq3 dq4 dq5 : DFrac) (mp rp : Loc)
    (ms : GMap w64 Loc) (rm : GMap w64 Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ membership.rcLocalIDAddr c ↦ lid0 ∗ membership.rcCidAddr c ↦ cid0 ∗
      membership.rcMembersAddr c ↦{dq2} mp ∗ mp ↦${dq3} ms ∗
      membership.rcRemovedAddr c ↦{dq4} rp ∗ rp ↦${dq5} rm }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"SetID")) (Val #lid)) (Val #cid))
  {{ RET #(); membership.rcLocalIDAddr c ↦ lid ∗ membership.rcCidAddr c ↦ cid ∗
      membership.rcMembersAddr c ↦{dq2} mp ∗ mp ↦${dq3} ms ∗
      membership.rcRemovedAddr c ↦{dq4} rp ∗ rp ↦${dq5} rm }}

end spec

end EtcdGrove
end Perennial
