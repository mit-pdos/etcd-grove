/-
`raft.IsEmptySnap(sp)` (node.go), of etcd's raft dependency (raft v3.7), for a nil snapshot: the
raft wrapper's only case (the node contract hands out no snapshot). Lean-first (no Rocq
counterpart); see `InvRaftMsg.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftMsg
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `IsEmptySnap(nil)` is `true` (its metadata's index reads as 0). -/
abbrev IsEmptySnap.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val (@! go_etcd_io.raft.v3.IsEmptySnap)) (Val #(null : Loc)))
  {{ RET #true; True }}

end spec

end EtcdGrove
end Perennial
