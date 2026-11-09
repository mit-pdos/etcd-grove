/-
## `(*raftLog).commitTo(tocommit)` (internal)

**Users**: `maybeCommit`, `maybeAppend`, `handleHeartbeat` (`raft.go:1851`), `restore`'s
fast-forward (`raft.go:1933`). **Proof sketch**: the `Panicf` (`lastIndex < tocommit`) excluded by
the premise; `Wf`'s `committed ≤ end` since `lastIndex ≤ end`. **Changes**: from
`specs-ref/Spec/go_etcd_io/raft/v3/raftLog__commitTo.lean`.
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

/-- (internal) Raise `committed` to `tocommit`, which the log has. -/
def raftLog.commitTo.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (c : w64),
  (uint.nat c ≤ ls.committed ∨ uint.nat c ≤ ls.lastIndex) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"commitTo")) (Val #c))
  {{ RET #(); raftLog l { ls with committed := max ls.committed (uint.nat c) } }}

end spec
end Raft
end EtcdGrove
end Perennial
