/-
`(*raftNode).onStop()` (raft.go): the loop's deferred shutdown.
Lean-first (no Rocq counterpart); see `InvRaftNode.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `r.onStop()`: stops the node, the ticker and the transport, closes the WAL (which succeeds,
by its contract: else `lg.Panic`) and then `done`. -/
abbrev raftNode.onStop.spec : Prop :=
  ∀ (E : RNEnv GF) (γ : RNNames) (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode E γ r ∗ rnDoneTok γ r }}
    (App (Val (r @!! go.GoType.PointerType raftNode.ty @!! go!"onStop")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
