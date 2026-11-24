/-
`membership.RaftCluster.ID` (`cluster.go`: `return c.cid`). Lean-first (no Rocq counterpart); the
request path (`notes/decisions.md`, "The request path"); unit P1b (2026-10-14): the field's
points-to, which the server's fields carry.
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

/-- `c.ID()` returns the cluster id `cid` (`c.cid`, written once at bootstrap: read-only; the
response header's `ClusterId`). -/
abbrev membership.RaftCluster.ID.spec : Prop :=
  ∀ (c : Loc) (cid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.clusterCid c cid }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"ID")) (Val #()))
  {{ RET #cid; True }}

/-- **`c.ID()` with the id field read at any fraction** (claim #34, stage 2, 2026-11-25: `Finalize`'s
`SetID(c.nodeID, c.cl.ID())`, on the cluster before it is shared, whose `SetID` then writes the
field): the field's value, the points-to given back. -/
abbrev membership.RaftCluster.ID.specO : Prop :=
  ∀ (c : Loc) (dq : DFrac) (cid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.rcCidAddr c ↦{dq} cid }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"ID")) (Val #()))
  {{ RET #cid; membership.rcCidAddr c ↦{dq} cid }}

end spec

end EtcdGrove
end Perennial
