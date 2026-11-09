/-
## `(*raftLog).hasNextOrInProgressUnstableEnts()` (internal)

**Users**: `RawNode.HasReady`, `rawnode.go:214,274`. Mirrors the code.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__hasNextOrInProgressUnstableEnts.lean`: over `LogState`.
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

/-- (internal) Whether there is any unstable entry. -/
def raftLog.hasNextOrInProgressUnstableEnts.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"hasNextOrInProgressUnstableEnts")) (Val #()))
  {{ RET #(decide (ls.us.ents ≠ [])); raftLog l ls }}

end spec
end Raft
end EtcdGrove
end Perennial
