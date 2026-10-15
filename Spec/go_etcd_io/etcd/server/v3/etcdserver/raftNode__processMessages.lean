/-
`(*raftNode).processMessages(ms)` (raft.go): the messages to send, filtered.
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

/-- `r.processMessages(ms)`, on the `Ready`'s messages (each one raft may send): a new slice of
some of them (a message to a removed member and all but the last `MsgAppResp` dropped, a
`MsgSnap` handed to `msgSnapC` if it has room, else dropped), in reverse order. -/
abbrev raftNode.processMessages.spec : Prop :=
  ∀ (E : RNEnv GF) (γ : RNNames) (r : Loc) (ms : GoSlice) (msL : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode E γ r ∗
      ms ↦*□ msL ∗ [∗list] m ∈ msL, rnMsgOk E m }}
    (App (Val (r @!! go.GoType.PointerType raftNode.ty @!! go!"processMessages")) (Val #ms))
  {{ (out : GoSlice), RET #out; ∃ outL : List Loc, out ↦* outL ∗ [∗list] m ∈ outL, rnMsgOk E m }}

end spec

end EtcdGrove
end Perennial
