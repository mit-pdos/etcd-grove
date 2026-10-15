/-
`(*raftpb.HardState).GetCommit()`, of etcd's raft dependency (raft v3.7: protobuf-go v2). Lean-first
(no Rocq counterpart); see `InvRaftMsg.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftMsg

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
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

/-- `p.GetCommit()`: the hard state's `Commit` (0 if absent or if `p` is nil). -/
abbrev raftpb.HardState.GetCommit.spec : Prop :=
  ∀ (p : Loc) (hs : HardStateModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ hardStateAt p hs }}
    (App (Val (p @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetCommit")) (Val #()))
  {{ RET #hs.commit; True }}

end spec

end EtcdGrove
end Perennial
