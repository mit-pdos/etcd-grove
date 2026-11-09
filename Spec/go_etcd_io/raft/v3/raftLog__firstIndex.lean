/-
## `(*raftLog).firstIndex()` (internal)

**Users**: `term`, `mustCheckOutOfBounds`, `sendSnapshot`'s log line, `stepLeader`'s
`pr.Match+1 >= firstIndex()` (`raft.go:1546`, a liveness check). **Proof sketch**: the pending
snapshot's, or `Storage.FirstIndex` (no error), between the base and the published floor.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__firstIndex.lean`: the storage's answer bounded by `compactFloor`
(it moves under concurrent compaction).
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

/-- (internal) The first index the log may answer entries for. -/
def raftLog.firstIndex.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"firstIndex")) (Val #()))
  {{ (f : w64), RET #f; raftLog l ls ∗
      ⌜ls.firstIdx ≤ uint.nat f ∧ uint.nat f ≤ ls.compactFloor + 1 ∧
       (ls.us.snap.isSome → uint.nat f = ls.firstIdx)⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
