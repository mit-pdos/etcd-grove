/-
## `(*raftLog).nextUnstableSnapshot()` (internal)

**Users**: `readyWithoutAccept` (`rawnode.go:156`: `Ready.Snapshot`). **Proof sketch**:
`unstable.nextSnapshot` (a fresh clone), valid (`restore`'s premise, kept by the log; round 1, S6: the caller hands it
out with `snapValid`). **Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__nextUnstableSnapshot.lean`.
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

/-- (internal) A fresh copy of the pending snapshot if it is not in progress, else `nil`. -/
def raftLog.nextUnstableSnapshot.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (S : StorState → IProp GF) (V : Snapshot → IProp GF) (N : Namespace),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls ∗ logStorage l S V N }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"nextUnstableSnapshot")) (Val #()))
  {{ (sp : Loc), RET #sp; raftLog l ls ∗
      (match ls.us.nextSnapshot with
       | none => ⌜sp = null⌝
       | some s => snapshotPts sp (DFrac.own 1) s ∗ V s) }}

end spec
end Raft
end EtcdGrove
end Perennial
