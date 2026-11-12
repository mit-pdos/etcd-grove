/-
## `Inflights.FreeLE(to)`

**Users.** `stepLeader`'s `MsgAppResp` in replicate state (`raft.go:1562`): R2. Snippet
`raftconf/tracker.go` (`ReqInflightsFull`).

**Proof sketch.** Nothing for an empty ring or `to` below the oldest; else the loop over the
`count` messages from `start`, stopping at the first above `to`, summing their bytes (wrapping);
`count`, `bytes`, `start` updated (`start = 0` if empty).

**Changes** (from `specs-ref`'s `tracker/Inflights__FreeLE.lean`): the model's `freeLE` (drop the
acknowledged prefix).

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.tracker.Api

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

/-- Frees the messages acknowledged by `to`, oldest first. -/
def Inflights.FreeLE.spec : Prop :=
  ∀ (p : Loc) (I : InflightsV) (to : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ inflightsOwn p I }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.Inflights.ty @!! go!"FreeLE")) (Val #to))
  {{ RET #(); inflightsOwn p (I.freeLE to) }}

end spec
end Tracker
end EtcdGrove
end Perennial
