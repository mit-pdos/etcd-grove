/-
## `(*raftLog).hasNextCommittedEnts(allowUnstable)` (internal)

**Users**: `RawNode.HasReady` (`rawnode.go:463`). Mirrors the code (`nextCommittedEnts` is
non-empty exactly then). **Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__hasNextCommittedEnts.lean`.
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

/-- (internal) Whether `nextCommittedEnts` would return entries. -/
def raftLog.hasNextCommittedEnts.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (allow : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"hasNextCommittedEnts")) (Val #allow))
  {{ RET #(decide (ls.applyingPaused = false ∧ ls.us.snap = none ∧
        ls.applying < ls.maxAppliable allow)); raftLog l ls }}

end spec
end Raft
end EtcdGrove
end Perennial
