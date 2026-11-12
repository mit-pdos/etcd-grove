/-
Applying a configuration change (`raft.applyConfChange`, `RawNode.ApplyConfChange`),
Lean-first (2026-10-13, reconfiguration stage D): changes that leave the configuration
unchanged.

* The model of `applyConfChange`'s choice (`ccApplyM`: `LeaveJoint`, `EnterJoint` or
  `Simple`, on the `ConfChangeV2` that `AsV2` makes of the change, `ccV2Of`), and the state
  `confchange` sees of the node's configuration (`cfgState cfg`: the voters `cfg`, nothing
  else, every tracked `Progress` a non-learner). The scope of these specs is a change whose
  model answer is that same state (`ccApplyM ... (cfgState cfg) = some (cfgState cfg)`); only
  `Simple` can answer that (`ccApplyM_noop`), e.g. for a change with `NodeId = 0`, which
  `Changer.apply` skips (`ccApplyM_single_noop`).
* `ownTracker_toCC`: the node's tracker as the `Changer` reads it (`ownTrackerCC`), the old
  `Progress` objects' inflight rings set apart (`progRAt`).
* `ownResult_noop_transfer`: `Simple`'s result, with the rings moved to the new `Progress`
  objects (copies, or fresh ones), as `switchToConfig` takes it (`ownConfigV`), each new
  `Match` the old one or `0` (`MatchKept`).

Raft v3.7 retarget (stage R4): the heap section only; the model (`section model`) is in
`CCApply.lean` since stage R1, imported here.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.InvConfchange
public import Proof.go_etcd_io.raft.v3.InvTrackerC
public import Proof.go_etcd_io.raft.v3.InvConfChangeMsg
public import Proof.go_etcd_io.raft.v3.CCApply

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3


/-! ## The tracker as a `Changer` reads it, and the result as `switchToConfig` takes it -/

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- What `ownProgress pr p` holds besides the points-to, for the record `peers` holds at `k`:
the inflight ring and that the value is a non-learner `Progress` of the record. -/
def progRAt (peers : GMap w64 Progress) (k : w64) (pv : tracker.Progress) : IProp GF :=
  iprop(∃ p, ⌜peers !! k = some p⌝ ∗ ownInflights pv.Inflights' p.infl ∗
    ⌜progressAbs pv p.infl = some p⌝)

-- `domSet_gset` (a set is its own domain) is in `InvTrackerC.lean` since 2026-10-13.

end heap

end EtcdGrove
end Perennial
