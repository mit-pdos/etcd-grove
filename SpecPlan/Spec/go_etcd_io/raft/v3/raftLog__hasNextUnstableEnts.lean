/-
## `(*raftLog).hasNextUnstableEnts()` (internal)

**Users**: `RawNode.HasReady` (`rawnode.go:463`), `needStorageAppendMsg`. Mirrors the code.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__hasNextUnstableEnts.lean`: over `LogState`.
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

/-- (internal) Whether some unstable entry is not yet in progress. -/
def raftLog.hasNextUnstableEnts.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"hasNextUnstableEnts")) (Val #()))
  {{ RET #(decide (ls.us.nextEntries ≠ [])); raftLog l ls }}

end spec
end Raft
end EtcdGrove
end Perennial
