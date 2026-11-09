/-
## `(*raftLog).stableTo(id)` (internal)

**Users**: `raft.Step`'s `MsgStorageAppendResp` (`raft.go:1217`: the last entry of the batch the
storage wrote, when it had entries). Snippet `raftlog/ready.go` (`ReqReadyCycle`).

**Proof sketch**: `unstable.stableTo`. The storage relation is kept: the entries made stable are
`stored`'s (`StableOk`'s first conjunct: the log does not change), and the storage ends at `id`
once nothing is unstable (its second). The caller proves `StableOk` from what it knows of `stored`
(absorbed batches, each the log's entries at its hand-out; with the cluster's log matching, entries
of one index and term agree).

**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__stableTo.lean`: on `raftLog` (was the window predicate
`ownRaftLogW`); `StableOk` restated over `LogState.log`.

**Margin**: none.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiLog

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

/-- (internal) Mark the entries through `id` stable, if the log still has `id`. -/
def raftLog.stableTo.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (id : go_etcd_io.raft.v3.entryID),
  ls.StableOk (uint.nat id.index') id.term' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"stableTo")) (Val #id))
  {{ RET #(); raftLog l (ls.stableTo (uint.nat id.index') id.term') }}

end spec
end Raft
end EtcdGrove
end Perennial
