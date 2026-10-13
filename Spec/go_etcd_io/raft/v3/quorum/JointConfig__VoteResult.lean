/-
Port of `election_proof/spec_JointConfig__VoteResult.v` (feb5c73d4); general since
2026-10-13 (reconfiguration stage A1), Lean-first.

Lean notes:
* The reference `quorum.JointConfig__VoteResultⁱᵐᵖˡ` is to the Lean generated code
  `quorum.JointConfig.VoteResult.impl`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.InvTrackerC

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `c.VoteResult(votes)` for a joint config (`quorum.JointConfig.VoteResult.impl`,
joint.go:62), each component asked and the answers combined:

    r1 := c[0].VoteResult(votes)
    r2 := c[1].VoteResult(votes)
    if r1 == r2 { return r1 }
    if r1 == VoteLost || r2 == VoteLost { return VoteLost }
    return VotePending

**General since 2026-10-13** (reconfiguration stage A1). The receiver is any `*JointConfig`
`c` (read at any fraction: the method has a value receiver, so the body works on a copy)
whose halves `v0`, `v1` are id sets `nil` or maps (`ownIdsetQ`), and the votes any map read
at any fraction. Each half answers by `MajorityConfig.VoteResult`: `VoteWon` exactly when the
granted votes are a majority of it (`MajQ`: by convention every set is a majority of the
empty half), `VoteLost` exactly when its voters that have not rejected are not. So the joint
answer is `VoteWon` exactly when both halves win and `VoteLost` exactly when one loses: no
premise, nothing lost. (Until 2026-10-13 this was stated only for the tracker's own receiver
`&r.trk.Config.Voters` and vote map at a simple configuration, with `cfg ≠ ∅`: there the
`MajQ` of the nil second half is `True` and `MajQ cfg q` is `IsQuorum cfg q`. Its users,
`ProgressTracker.TallyVotes` and `QuorumActive`, now go through the general statement.)
The sizes bound `MajorityConfig.VoteResult`'s `int` counters. -/
abbrev quorum.JointConfig.VoteResult.spec : Prop :=
  ∀ (c : Loc) (dqc : DFrac) (a : quorum.JointConfig) (v0 v1 : Loc) (s0 s1 : GSet w64)
    (vm : Loc) (dqv : DFrac) (votes : GMap w64 Bool),
  a.arr = [v0, v1] →
  (GMap.size s0 : Int) < 2 ^ 63 → (GMap.size s1 : Int) < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗ c ↦{dqc} a ∗
      ownIdsetQ v0 (DFrac.own 1) s0 ∗ ownIdsetQ v1 (DFrac.own 1) s1 ∗ vm ↦${dqv} votes }}
    (App (Val (c @!! go.GoType.PointerType quorum.JointConfig.ty @!! go!"VoteResult"))
      (Val #vm))
  {{ (res : w8), RET #res;
      c ↦{dqc} a ∗ ownIdsetQ v0 (DFrac.own 1) s0 ∗ ownIdsetQ v1 (DFrac.own 1) s1 ∗
      vm ↦${dqv} votes ∗
      ⌜res = VoteWon ∨ res = VoteLost ∨ res = VotePending⌝ ∗
      ⌜res = VoteWon ↔ MajQ s0 (granted votes) ∧ MajQ s1 (granted votes)⌝ ∗
      -- `VoteLost` is "cannot still win", not "a majority rejected"; see `Step.lose`
      -- (`Protocol/Model.lean`) and `JLost` (`Protocol/StepC.lean`).
      ⌜res = VoteLost ↔ ¬ MajQ s0 (s0 \ rejected votes) ∨ ¬ MajQ s1 (s1 \ rejected votes)⌝ }}

end spec

end EtcdGrove
end Perennial
