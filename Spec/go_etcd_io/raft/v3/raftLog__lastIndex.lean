/-
## `(*raftLog).lastIndex()` (internal)

**Users**: everywhere in `raft.go` (`appendEntry`, `reset`, `becomeLeader`, `stepLeader`,
`handleAppendEntries`, `loadState`, ...), `lastEntryID`, `term`. Snippet `raftlog/append.go`.
**Proof sketch**: `unstable.maybeLastIndex`, else `Storage.LastIndex` (the invariant: the storage
ends at `base + |stored|` when nothing is pending unstored). **Changes**: from
`specs-ref/Spec/go_etcd_io/raft/v3/raftLog__lastIndex.lean`.
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

/-- (internal) The log's last index (`LogState.lastIndex`). -/
def raftLog.lastIndex.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"lastIndex")) (Val #()))
  {{ RET #(W64 ls.lastIndex); raftLog l ls }}

end spec
end Raft
end EtcdGrove
end Perennial
