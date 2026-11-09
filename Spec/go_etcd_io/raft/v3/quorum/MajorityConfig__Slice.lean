/-
## `MajorityConfig.Slice()`

**Users.** `ProgressTracker.ConfState` (`tracker.go:126`, the four lists of `ConfState`); the TLA
trace (`state_trace.go`, not in the default build).

**Proof sketch.** `range c` appending each id (a fresh slice), then `slices.Sort` (`≤ 2^62`).

**Changes** (from `specs-ref`'s `quorum/MajorityConfig__Slice.lean`): the result as `sorted s`.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.raft.v3.quorum.Api

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

/-- The voters, in increasing order, in a fresh slice. -/
def MajorityConfig.Slice.spec : Prop :=
  ∀ (p : Loc) (dqp : DFrac) (m : GoMap) (dq : DFrac) (s : GSet w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗ p ↦{dqp} m ∗ majorityOwn m dq s ∗ ⌜GMap.size s ≤ sortMax⌝ }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.quorum.MajorityConfig.ty @!! go!"Slice")) (Val #()))
  {{ (sl : GoSlice), RET #sl; p ↦{dqp} m ∗ majorityOwn m dq s ∗ sl ↦* (sorted s) }}

end spec
end Quorum
end EtcdGrove
end Perennial
