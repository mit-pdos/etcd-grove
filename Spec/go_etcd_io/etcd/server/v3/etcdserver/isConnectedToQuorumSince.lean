/-
`isConnectedToQuorumSince` (`util.go`: `numConnectedSince(...) >= quorum(len(members))`). Lean-first (no Rocq counterpart); the request path (`notes/decisions.md`, "The request path");
unit P1b (2026-10-14): the transport's contract (`rafthttp.isTransporter`), the members owned.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Defs

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

/-- `isConnectedToQuorumSince(transport, since, self, members)`, the transport a
`rafthttp.isTransporter`, the members owned: some boolean (`parseProposeCtxErr` only classifies
its error by it); the members kept. -/
abbrev isConnectedToQuorumSince.spec : Prop :=
  ∀ (tr : GoInterface) (since : time.Time) (self : w64) (members : GoSlice) (ms : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ rafthttp.isTransporter tr ∗
      membership.membersAt members ms }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.isConnectedToQuorumSince)) (Val #tr)) (Val #since)) (Val #self))
      (Val #members))
  {{ (b : Bool), RET #b; membership.membersAt members ms }}

end spec

end EtcdGrove
end Perennial
