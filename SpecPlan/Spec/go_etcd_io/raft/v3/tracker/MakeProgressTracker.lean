/-
## `MakeProgressTracker(maxInflight, maxBytes)`

**Users.** `newRaft` (`raft.go:456`, then `Restore`), `appliedSnap` (`raft.go:775`): R2; the
examples' pre-check (`examples/raft/kvreconf/kv.go:223`). Snippet `raftconf/confchange.go`
(`ReqApplyLikeRaft`).

**Proof sketch.** The literal: an allocated empty incoming map, `nil` elsewhere, empty votes and
progress maps: the empty configuration in canonical form, valid; `TrackerOk` of empty maps.

**Changes** (from `specs-ref`'s `tracker/MakeProgressTracker.lean`): as `trackerOwn` at the empty
model (was the field values spelled out).

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

/-- A tracker of the empty configuration, no peer, no vote. -/
def MakeProgressTracker.spec : Prop :=
  ∀ (mi mb : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker }}
    (App (App (Val #(functions go_etcd_io.raft.v3.tracker.MakeProgressTracker [])) (Val #mi))
      (Val #mb))
  {{ (tv : go_etcd_io.raft.v3.tracker.ProgressTracker), RET #tv;
      trackerOwn tv ⟨Membership.empty, ∅, ∅, ∅, mi, mb⟩ }}

end spec
end Tracker
end EtcdGrove
end Perennial
