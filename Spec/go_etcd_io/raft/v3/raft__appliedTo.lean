/-
## `raft.appliedTo(index, size)` (internal)

**Users.** `raft.Step`'s apply acknowledgement (`raft.go:1226`), `appliedSnap` (`:769`). **Proof
sketch.** R3's `appliedTo(max(index, applied))` (within the commit: no panic). At a joint leader
with auto-leave whose pending conf entry is applied: `confChangeToMsg(nil)` (R1: an empty
`EntryConfChangeV2`, raft's own entry: `stepIn`'s proposal case) and `raft.Step` on the closed
struct (its invariant at the new applied index: the caller's, the apply acknowledgement's view
consistent with the delivered log). Otherwise nothing more. **Changes** (from `specs-ref`'s
`raft__appliedTo.lean`): over the opened struct. **Margin.** The auto-leave proposal's result is
ignored, as in Go. Verify-round (A4 P3): the auto-leave proposal is a step from outside, so the leader branch takes the idle token (the apply acknowledgement's: `applied` has reached the published floor).
-/
module

public import Spec.go_etcd_io.raft.v3.ApiCore

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

/-- (internal) Moves the applied index; a joint leader proposes leaving. -/
def raft.appliedTo.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (i size : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ ⌜uint.nat i ≤ o.log.committed⌝ ∗
      (⌜o.view.role ≠ StateLeader⌝ ∨
        (coreInv r γ id { o with log := o.log.appliedTo (max (uint.nat i) o.log.applied) size } ∗
          coreIdle r)) }}
    (App (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"appliedTo")) (Val #i)) (Val #size))
  {{ RET #(); ∃ o', raftOpen r γ id o' ∗
      ((⌜o.view.role ≠ StateLeader ∧
          o' = { o with log := o.log.appliedTo (max (uint.nat i) o.log.applied) size }⌝) ∨
       (coreInv r γ id o' ∗ coreIdle r)) }}

end spec
end Raft
end EtcdGrove
end Perennial
