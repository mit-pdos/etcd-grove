/-
`membership.RaftCluster.ID` (`cluster.go`: `return c.cid`) over a fraction of `c.cid`'s points-to (claim
#34 stage 4, 2026-11-25): what `bootstrapNewWAL` reads before the cluster's `cid` is made read-only (the
bootstrap's `clusterBuilt` owns the field; `RaftCluster__ID.lean`'s spec takes it read-only, `clusterCid`).
Lean-first.
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

/-- `c.ID()` returns `c.cid`'s value `cid`, read at any fraction. -/
abbrev membership.RaftCluster.ID.specFrac : Prop :=
  ∀ (c : Loc) (dq : DFrac) (cid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.rcCidAddr c ↦{dq} cid }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"ID")) (Val #()))
  {{ RET #cid; membership.rcCidAddr c ↦{dq} cid }}

end spec

end EtcdGrove
end Perennial
