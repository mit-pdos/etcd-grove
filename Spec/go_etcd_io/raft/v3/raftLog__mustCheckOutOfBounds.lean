/-
## `(*raftLog).mustCheckOutOfBounds(lo, hi)` (internal)

**Users**: `slice`. **Proof sketch**: the two `Panicf`s excluded by the premises; `firstIndex`.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__mustCheckOutOfBounds.lean`.
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

/-- (internal) `nil` if `lo` is at or past the first index, else `ErrCompacted`. -/
def raftLog.mustCheckOutOfBounds.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (lo hi : w64),
  uint.nat lo ≤ uint.nat hi → uint.nat hi ≤ ls.lastIndex + 1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"mustCheckOutOfBounds")) (Val #lo)) (Val #hi))
  {{ (err : GoInterface), RET #err; raftLog l ls ∗
      (⌜err = interface.nil ∧ ls.firstIdx ≤ uint.nat lo⌝ ∨
       (errIs go_etcd_io.raft.v3.ErrCompacted err ∗ ⌜uint.nat lo ≤ ls.compactFloor⌝ ∗ logCompactedLb l (uint.nat lo))) }}

end spec
end Raft
end EtcdGrove
end Perennial
