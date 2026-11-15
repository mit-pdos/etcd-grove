/-
## `(*raftLog).nextUnstableEnts()` (internal)

**Users**: `readyWithoutAccept` (`rawnode.go:143`: `Ready.Entries`), `hasNextUnstableEnts`.
**Proof sketch**: `unstable.nextEntries`. The slice aliases the unstable array (capacity
included); it is handed out read-only (`entriesRO`, no capacity), so a client cannot append to it.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__nextUnstableEnts.lean`: over `LogState`.
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

/-- (internal) The unstable entries not yet in progress, from `offsetInProgress`. -/
def raftLog.nextUnstableEnts.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"nextUnstableEnts")) (Val #()))
  {{ (sl : GoSlice), RET #sl; raftLog l ls ∗ entriesRO sl ls.us.offsetInProgress ls.us.nextEntries }}

end spec
end Raft
end EtcdGrove
end Perennial
