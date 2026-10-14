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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

end spec

end EtcdGrove
end Perennial
