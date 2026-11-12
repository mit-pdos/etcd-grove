/-
## `JointConfig.CommittedIndex(l)`

**Users.** `ProgressTracker.Committed` (`tracker.go:162`, with the tracker's `matchAckIndexer`:
`raft.maybeCommit`, R2), `readOnly.maybeAdvance` (`read_only.go:81`, with the `readOnly` itself:
R3). Snippet `raftconf/quorum.go` (`ReqJointCommitted`, `ReqEmptyHalf`).

**Proof sketch.** `c[0].CommittedIndex(l)`, `c[1].CommittedIndex(l)` (the half specs, `P` threaded
through both), the smaller (`JointIdx`).

**Changes** (from `specs-ref`'s `quorum/JointConfig__CommittedIndex.lean`): over `jointConfigOwn`
(R3's provisional predicate, now this package's) and `JointIdx` (R3's relation, now this
package's).

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.quorum.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Quorum

open Iris Iris.BI
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.quorum.Assumptions]

/-- The largest index a strict majority of each half acknowledged (`JointIdx`). -/
def JointConfig.CommittedIndex.spec : Prop :=
  ∀ (p : Loc) (dqp : DFrac) (c : go_etcd_io.raft.v3.quorum.JointConfig) (dq : DFrac)
    (s0 s1 : GSet w64) (l : GoInterface) (P : IProp GF) (acked : w64 → Option w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗ p ↦{dqp} c ∗ jointConfigOwn c dq s0 s1 ∗ isAckedIndexer l P acked ∗ P ∗
      ⌜GMap.size s0 ≤ sortMax ∧ GMap.size s1 ≤ sortMax⌝ }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.quorum.JointConfig.ty @!! go!"CommittedIndex")) (Val #l))
  {{ (N : w64), RET #N; p ↦{dqp} c ∗ jointConfigOwn c dq s0 s1 ∗ P ∗
      ⌜JointIdx s0 s1 (fun v => (acked v).getD (W64 0)) N⌝ }}

end spec
end Quorum
end EtcdGrove
end Perennial
