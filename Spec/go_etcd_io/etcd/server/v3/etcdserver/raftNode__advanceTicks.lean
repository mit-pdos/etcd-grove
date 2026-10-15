/-
`(*raftNode).advanceTicks(ticks)` (raft.go): `ticks` ticks.
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

/-- `r.advanceTicks(ticks)`, for a tick's resource per tick. -/
abbrev raftNode.advanceTicks.spec : Prop :=
  ∀ (E : RNEnv GF) (γ : RNNames) (r : Loc) (ticks : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode E γ r ∗ [∗list] _u ∈ List.replicate (sint.Z ticks).toNat (), E.T }}
    (App (Val (r @!! go.GoType.PointerType raftNode.ty @!! go!"advanceTicks")) (Val #ticks))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
