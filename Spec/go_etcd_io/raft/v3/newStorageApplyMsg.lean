/-
## `newStorageApplyMsg(r, rd)` (internal)

`readyWithoutAccept`'s asynchronous branch (`rawnode.go:372`), unreachable under `ConfigOk`.
Mirrors the code: a `MsgStorageApply` to the local apply thread with the committed entries, of term
0, its response `newStorageApplyRespMsg`'s. **Changes.** New (round 1).
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

/-- (internal) The storage-apply message of a batch. -/
def newStorageApplyMsg.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (rd : go_etcd_io.raft.v3.Ready) (k : Nat) (es : List LogEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ entriesRO rd.CommittedEntries' k es }}
    (App (App (Val (@! go_etcd_io.raft.v3.newStorageApplyMsg)) (Val #r)) (Val #rd))
  {{ (p : Loc), RET #p; ∃ mm, raftOpen r γ id o ∗ msgPts p (DFrac.own 1) mm ∗
      ⌜mm.type = MsgStorageApply ∧ mm.to = localApplyThread ∧ mm.src = id ∧ mm.term = W64 0 ∧
        mm.entries = es⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
