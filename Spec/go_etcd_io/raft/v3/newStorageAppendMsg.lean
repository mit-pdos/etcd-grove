/-
## `newStorageAppendMsg(r, rd)` (internal)

`readyWithoutAccept`'s asynchronous branch (`rawnode.go:223`), unreachable under `ConfigOk`.
Mirrors the code: a `MsgStorageAppend` to the local append thread with the batch's entries, hard
state and snapshot, its responses the queued `msgsAfterAppend` and the append acknowledgement.
**Changes.** New (round 1). **Margin.** The responses are not stated (R1's `Msg` has none).
-/
module

public import Spec.go_etcd_io.raft.v3.ApiCore

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) The storage-append message of a batch. -/
def newStorageAppendMsg.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (rd : go_etcd_io.raft.v3.Ready) (k : Nat) (es : List LogEntry)
    (oh : Option HardState) (os : Option Snapshot),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ entriesRO rd.Entries' k es ∗ hsOpt rd.HardState' oh ∗
      snapOpt rd.Snapshot' os }}
    (App (App (Val (@! go_etcd_io.raft.v3.newStorageAppendMsg)) (Val #r)) (Val #rd))
  {{ (p : Loc), RET #p; ∃ mm, raftOpen r γ id o ∗ msgPts p (DFrac.own 1) mm ∗
      ⌜mm.type = MsgStorageAppend ∧ mm.to = localAppendThread ∧ mm.src = id ∧ mm.entries = es⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
