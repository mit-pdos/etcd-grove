/-
## `(*raftLog).isUpToDate(their)` (internal)

**Users**: vote handling (`raft.go:1240`). Mirrors the code (`lastEntryID`). **Changes**: from
`specs-ref/Spec/go_etcd_io/raft/v3/raftLog__isUpToDate.lean`.
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

/-- (internal) Whether a log ending at `their` is at least as up to date as this one. -/
def raftLog.isUpToDate.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (their : go_etcd_io.raft.v3.entryID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"isUpToDate")) (Val #their))
  {{ (r : Bool), RET #r; raftLog l ls ∗ ∃ t, ⌜ls.termOf ls.lastIndex = some t ∧
      r = decide (uint.nat t < uint.nat their.term' ∨
        (their.term' = t ∧ ls.lastIndex ≤ uint.nat their.index'))⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
