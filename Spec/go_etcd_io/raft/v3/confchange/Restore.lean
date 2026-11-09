/-
## `Restore(chg, cs)`

**Users.** `newRaft` (`raft.go:472`: the storage's `ConfState`, from `MakeProgressTracker`'s empty
tracker; R1's `confAt_valid` gives a valid configuration it lists, so `restore_lists` gives it back:
no panic, and `assertConfStatesEquivalent` passes), `appliedSnap` (`raft.go:776`, the snapshot's
`ConfState`, the same): R2. The examples' pre-check (`examples/raft/kvreconf/kv.go:223`: any
`ConfState`, the error handled). Snippets `raftconf/confchange.go` (`ReqRestoreEmpty`,
`ReqRestoreRoundTrip`, `ReqApplyLikeRaft`).

**Proof sketch.** `toConfChangeSingle(cs)` (fresh `ConfChangeSingle`s: `ccsPts` of the outgoing
adds and the incoming changes); the op closures (each an `opSpec` of `simple [c]`, or of
`enterJoint (cs.GetAutoLeave()) inc`, by `Changer.Simple.spec`/`EnterJoint.spec`); `chain`. No op
(an empty `ConfState`): `chain` returns the tracker's own configuration and map, at the model's
`m0`, which the precondition's resources are.

**Changes** (from `specs-ref`'s `confchange/Restore.lean`): any `ConfState` (was one the model
restores, with a premise; the error is now in the post, as Go returns it); from any tracker (was the
empty one, spelled out); the no-op case is no longer a separate disjunct: the precondition's
configuration and map are consumed and the result's given (the same maps when there is no op);
over raftpb's `confStatePts` (R1's provisional predicate, 3h's).

**Margin.** On an error nothing of the tracker is given back (the ops before the failing one replaced
it); raft panics there, the examples drop it.
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Api
public import Spec.go_etcd_io.raft.v3.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ConfChange

open Iris Iris.BI
open Classical Tracker

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.confchange.Assumptions]

/-- Replays `ConfState` `csv` from the changer's tracker: the configuration `restore` gives, or an
error. -/
def Restore.spec : Prop :=
  ∀ (chg : go_etcd_io.raft.v3.confchange.Changer) (m0 : Membership) (B : Base) (csp : Loc)
    (dq : DFrac) (csv : Raft.ConfState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ configOwn chg.Tracker'.Config' (DFrac.own 1) m0 ∗ progressMapOwn B.mp B.prs B.pv ∗
      ⌜BaseOf chg B ∧ TrackerOk m0 B.pv⌝ ∗ Raft.confStatePts csp dq csv }}
    (App (App (Val #(functions go_etcd_io.raft.v3.confchange.Restore [])) (Val #chg)) (Val #csp))
  {{ (cfg : go_etcd_io.raft.v3.tracker.Config) (trk : GoMap) (err : GoInterface),
      RET (PairV (PairV #cfg #trk) #err); Raft.confStatePts csp dq csv ∗
      result B (restore m0 csv.voters csv.learners csv.votersOutgoing csv.learnersNext
        csv.autoLeave) cfg trk err }}

end spec
end ConfChange
end EtcdGrove
end Perennial
