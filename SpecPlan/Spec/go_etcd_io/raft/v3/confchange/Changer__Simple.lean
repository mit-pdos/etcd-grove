/-
## `Changer.Simple(ccs...)`

**Users.** `raft.applyConfChange` (`raft.go:1963`: a change that is neither a joint transition nor
the leave: etcd's `ConfChange`s, `AsV2()`), `Restore`'s ops (`restore.go:142`, `151`); the
examples' pre-check (`examples/raft/kvreconf/kv.go:236`). Snippets `raftconf/confchange.go`
(`ReqApplyLikeRaft`, `ReqLastVoter`).

**Proof sketch.** `checkAndCopy` (the working copy `ccState B cfg trk {m with autoLeave := false}`;
the input check passes at a valid `m`, `configOwn_valid`); `joint` (`configOwn` gives the outgoing
half); `apply` on `&cfg` (`ccWork`); `symdiff` of the tracker's incoming map and the copy's (both
read); `checkAndReturn`; on success `m'` is valid (`transitions_valid`), so `ccState_done`; on an
error `ccState_abort` (or nothing to give back before the copy). The receiver and the tracker's
configuration are only read.

**Changes** (from `specs-ref`'s `confchange/Changer__Simple.lean`): over `Membership` and the model's
`simple` (was `simpleM` over `CCState`, the progress flags explicit); the result `changed` carries
the progress values (`Carried`: the rings move from the tracker's `Progress` to the copies), where
the old `ownResult` gave the copies with only their learner flags.

**Margin.** On success the tracker's progress map and `Progress` structs are not given back (their
rings now belong to the copies); raft replaces them (`switchToConfig`).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.confchange.Api

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

/-- `Simple(cs...)`: `changed B (simple cs m)`. -/
def Changer.Simple.spec : Prop :=
  ∀ (p : Loc) (dqp : DFrac) (chg : go_etcd_io.raft.v3.confchange.Changer) (dqc : DFrac)
    (m : Membership) (B : Base) (sl : GoSlice) (dqs : DFrac) (cs : List Single),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dqp} chg ∗
      configOwn chg.Tracker'.Config' dqc m ∗ progressMapOwn B.mp B.prs B.pv ∗
      ⌜BaseOf chg B ∧ TrackerOk m B.pv⌝ ∗ ccsPts sl dqs cs }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.confchange.Changer.ty @!! go!"Simple")) (Val #sl))
  {{ (cfg : go_etcd_io.raft.v3.tracker.Config) (trk : GoMap) (err : GoInterface),
      RET (PairV (PairV #cfg #trk) #err);
      p ↦{dqp} chg ∗ configOwn chg.Tracker'.Config' dqc m ∗ ccsPts sl dqs cs ∗ changed B (simple cs m) cfg trk err }}

end spec
end ConfChange
end EtcdGrove
end Perennial
