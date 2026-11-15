/-
## `Changer.apply(cfg, trk, ccs...)` (internal)

**Users.** `Simple`, `EnterJoint`. The loop over the changes (`applyOne`: `makeVoter`,
`makeLearner`, `remove`, skip, or the "unexpected conf type" error), then the "removed all voters"
check. Mirrors the code (the model's `apply`); an error leaves some working copy.

**Proof sketch.** Per change (`ccsPts`: each single at `dqs`): `GetNodeId()` (`0`: skipped),
`GetType()`, then `makeVoter`/`makeLearner`/`remove` on the working copy (`ccWork`, the model's
`applyOne`), or nothing for `UpdateNode`. An unknown type: `fmt.Errorf("unexpected conf type %d",
cc.GetType())`, whose argument is a `raftpb.ConfChangeType` (it has a `String` method, so
Perennial's `fmt.Errorf.spec`, `ArgsWf`, does not apply): raftpb's assumed `fmtErrorf.spec`
(`raftpb/FmtErrorf.lean`, one `FmtArg.enum ConfChangeType.ty t` argument; under `%d` Go calls no
method): a non-nil error, `applyOne = none`. After the loop, `incoming(cfg.Voters)` empty:
`errors.New` (Perennial's), the model's "removed all voters" `none`.

**Changes.** verify-round: (A5-provability F2) the "unexpected conf type" error is proved from the
assumed `RaftPb.fmtErrorf.spec` (the old proof's local `Spec/fmt/Errorf.lean`, `argsOk`, restored as
a raftpb-local boundary); the triple is unchanged.
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

/-- (internal) The changes on the working copy: the model's `apply`. -/
def Changer.apply.spec : Prop :=
  ∀ (p : Loc) (dqp : DFrac) (chg : go_etcd_io.raft.v3.confchange.Changer) (B : Base)
    (cfgp : Loc) (trk : GoMap) (m : Membership) (sl : GoSlice) (dqs : DFrac) (cs : List Single),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dqp} chg ∗ ccWork B cfgp trk m ∗ ⌜BaseOf chg B⌝ ∗ ccsPts sl dqs cs }}
    (App (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.confchange.Changer.ty @!! go!"go.etcd.io/raft/v3/confchange.apply")) (Val #cfgp)) (Val #trk)) (Val #sl))
  {{ (err : GoInterface), RET #err; p ↦{dqp} chg ∗ ccsPts sl dqs cs ∗
      match apply cs m with
      | some m1 => ⌜err = interface.nil⌝ ∗ ccWork B cfgp trk m1
      | none => ⌜err ≠ interface.nil⌝ ∗ ∃ m1, ccWork B cfgp trk m1 }}

end spec
end ConfChange
end EtcdGrove
end Perennial
