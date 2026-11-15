/-
## `IsEmptySnap(sp)`

**Users.** etcd's `raftNode.start` (`raft.go:255`, `272`), the examples (`kvdurable/kv.go:455`).
Snippet: `readyloop.go`. **Proof sketch.** Getters through a possibly-`nil` pointer. **Changes.**
Unchanged (`nil` included).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.Api

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
variable [ctx_sem : context.Assumptions]

/-- `true` iff the snapshot's index is 0 (or the pointer `nil`). -/
def IsEmptySnap.spec : Prop :=

  ∀ (sp : Loc) (dq : DFrac) (s : Snapshot),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ (⌜sp = null ∧ s = Snapshot.empty⌝ ∨ snapshotPts sp dq s) }}
    (App (Val (@! go_etcd_io.raft.v3.IsEmptySnap)) (Val #sp))
  {{ (b : Bool), RET #b; (⌜sp = null⌝ ∨ snapshotPts sp dq s) ∗ ⌜b = decide (s.index = W64 0)⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
