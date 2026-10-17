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

/-- Whether `processMessages` keeps the `Ready`'s message at index `i`, given the messages' types
`tys` and what `isIDRemoved` answered for each (`rm`, one answer per index: membership changes
concurrently, so two messages to one member may get different answers): not to a removed member,
not a `MsgSnap` (type 7), and, if a `MsgAppResp` (type 4), no later `MsgAppResp` to a member not
removed. -/
def rnKeepAt (tys : List w32) (rm : List Bool) (i : Nat) : Prop :=
  rm[i]? = some false ∧ tys[i]? ≠ some (W32 7) ∧
    (tys[i]? = some (W32 4) → ∀ j : Nat, i < j → tys[j]? = some (W32 4) → rm[j]? = some true)

/-- The messages of `msL` that `processMessages` keeps (`rnKeepAt`), in `msL`'s order. -/
def rnKept (msL : List Loc) (tys : List w32) (rm : List Bool) : List Loc :=
  ((msL.zipIdx).filter fun p => @decide (rnKeepAt tys rm p.2) (Classical.propDecidable _)).map
    Prod.fst

/-- `r.processMessages(ms)`, on the `Ready`'s messages (each one raft may send): a new slice of
exactly the messages `rnKeepAt` keeps, **in the `Ready`'s order** (etcd-io/etcd#22483, fixed by
etcd-io/etcd#22485; before it, the kept messages came out in reverse order), for some answers `rm`
of `isIDRemoved` (whose spec, `isRNIDRemoved`, returns any boolean): those to a removed member
dropped, a `MsgSnap` handed to `msgSnapC` if it has room and dropped, and of the `MsgAppResp`s
only the last one to a member not removed kept. `tys` are the messages' types (`msgAt`). The
`Ready`'s slice and messages are only read (`↦*□`, `msgAt`'s discarded fraction). -/
abbrev raftNode.processMessages.spec : Prop :=
  ∀ (E : RNEnv GF) (γ : RNNames) (r : Loc) (ms : GoSlice) (msL : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode E γ r ∗
      ms ↦*□ msL ∗ [∗list] m ∈ msL, rnMsgOk E m }}
    (App (Val (r @!! go.GoType.PointerType raftNode.ty @!! go!"processMessages")) (Val #ms))
  {{ (out : GoSlice), RET #out; ∃ outL : List Loc, out ↦* outL ∗ ([∗list] m ∈ outL, rnMsgOk E m) ∗
      ∃ (tys : List w32) (rm : List Bool),
        ([∗list] m; ty ∈ msL; tys, ∃ to : w64, msgAt m to ty) ∗
        ⌜rm.length = msL.length ∧ outL = rnKept msL tys rm⌝ }}

end spec

end EtcdGrove
end Perennial
