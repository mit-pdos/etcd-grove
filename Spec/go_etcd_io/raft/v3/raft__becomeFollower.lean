/- Port of election_proof/spec_raft__becomeFollower.v (feb5c73d4). -/
module

public import Proof.go_etcd_io.raft.v3.TracedCap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `becomeFollower` is `r.step := stepFollower`, `reset`, and assignments to `lead`
and `state`; `becomeFollower` (`Defs.lean`) is exactly that, `r.step` included. The
precondition says nothing about `r.step`: the function overwrites it first, which is
why `newRaft` can call this on a struct whose `step` is still nil. The term does not
move back (`raft.reset.spec`, 2026-10-10).

One spec for both modes (Q8 stage 1, slice 3, 2026-11-09; `notes/decisions.md`, "Q8 stage 1 (slice
3)"): the hook `traceBecomeFollower` logs the `BecomeFollower` line of the new state, through the
caller's gate `HookGate s.gh.tr r E Q`, given back as `Q`. A traced caller gives it from the
simulation's capability (`raft.becomeFollower.traced`, `TracedHooks.lean`: during the node's bootstrap
segment the bootstrap line's law, after it the step-down's, with its `PhaseStepBF` and `FxPresBF`), its
struct at its configuration's voters (`V = c.voters`, which the hook's event reads); an untraced one
(`s.gh.tr = none`) from the struct's nil logger (`raft.becomeFollower.untraced`). Until slice 3 the
premise `s.gh.tr = none`. -/
abbrev raft.becomeFollower.spec : Prop :=
  ∀ (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState) (term lead : w64) (Q : IProp GF),
  uint.Z s.term ≤ uint.Z term →
  -- (Q8 stage 1, slice 3) a traced node's struct is at its configuration's voters
  (s.gh.tr ≠ none → V = c.voters) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c V r id s ∗
      -- (Q8 stage 1, slice 3) the `BecomeFollower` line's gate, the caller's
      HookGate s.gh.tr r (NodeEvOf (W64 2) id (becomeFollower s term lead) c) Q }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomeFollower"))
      (Val #term)) (Val #lead))
  {{ (pvs : GMap w64 Progress), RET #();
      ownRaftPhysCV c V r id { becomeFollower s term lead with prvals := pvs } ∗ Q }}

end spec

end EtcdGrove
end Perennial
