/-
## `(*raftLog).lastEntryID()` (internal)

**Users**: `newRaft`, `campaign`/`hup` (`raft.go:1081`), vote handling, `restore`'s log lines,
`readyWithoutAccept`'s append message. **Proof sketch**: `lastIndex`, then `term(lastIndex)`, which
succeeds: `lastIndex ≥` the storage's compaction point (the floor is at most `committed`, the base at
most `lastIndex`) and `termOf lastIndex` is defined (the last unstable entry, the snapshot, or the
stored end). **Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__lastEntryID.lean`.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiLog

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

/-- (internal) The last entry's index and term. -/
def raftLog.lastEntryID.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"lastEntryID")) (Val #()))
  {{ (t : w64), RET #(go_etcd_io.raft.v3.entryID.mk t (W64 ls.lastIndex)); raftLog l ls ∗
      ⌜ls.termOf ls.lastIndex = some t⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
