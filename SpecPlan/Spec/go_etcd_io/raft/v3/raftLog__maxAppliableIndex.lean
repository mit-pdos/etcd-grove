/-
## `(*raftLog).maxAppliableIndex(allowUnstable)` (internal)

**Users**: `nextCommittedEnts`, `hasNextCommittedEnts`, `acceptApplying`. Mirrors the code.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__maxAppliableIndex.lean`.
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

/-- (internal) `committed`, or the stable part's end if lower and unstable entries may not be applied. -/
def raftLog.maxAppliableIndex.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (allow : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"maxAppliableIndex")) (Val #allow))
  {{ RET #(W64 (ls.maxAppliable allow)); raftLog l ls }}

end spec
end Raft
end EtcdGrove
end Perennial
