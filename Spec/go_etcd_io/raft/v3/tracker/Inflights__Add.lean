/-
## `Inflights.Add(index, bytes)`

**Users.** `Progress.SentEntries` (replicate state, entries sent). Snippet `raftconf/tracker.go`
(`ReqInflightsFull`).

**Proof sketch.** `Full()` is false (premise; Go panics "cannot add into a Full inflights"
otherwise); `next = start + count` (below `2 * size ≤ 2^63`), wrapped at `size`; `grow` when past
the buffer; the store; `count++`, `bytes +=` (wrapping, as `InflightsV.bytes`).

**Changes** (from `specs-ref`'s `tracker/Inflights__Add.lean`): the model appends `(index, bytes)`.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Tracker

open Iris Iris.BI
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.tracker.Assumptions]

/-- Records a message in flight (the ring must not be full). -/
def Inflights.Add.spec : Prop :=
  ∀ (p : Loc) (I : InflightsV) (index bytes : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ inflightsOwn p I ∗ ⌜I.full = false⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.Inflights.ty @!! go!"Add")) (Val #index)) (Val #bytes))
  {{ RET #(); inflightsOwn p { I with items := I.items ++ [(index, bytes)] } }}

end spec
end Tracker
end EtcdGrove
end Perennial
