/-
New in etcd-io/raft#168 (share witness), Lean-first (`notes/pr-verify/raft-168.md`).
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.quorum.MajorityConfig__VoteResultWithDifference

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `c.VoteResultWithDifference(votes)` (raft#168, joint.go): `JointConfig.VoteResult` with
each half asked through `MajorityConfig.VoteResultWithDifference`, the two counts returned as
an array:

    r1, v1 := c[0].VoteResultWithDifference(votes)
    r2, v2 := c[1].VoteResultWithDifference(votes)
    votesToWin := [2]int{v1, v2}
    if r1 == r2 { return r1, votesToWin }
    if r1 == VoteLost || r2 == VoteLost { return VoteLost, votesToWin }
    return VotePending, votesToWin

The verdict is exactly `JointConfig.VoteResult`'s (same receiver, premises and equivalences);
the array holds each half's `votesToWin`. -/
abbrev quorum.JointConfig.VoteResultWithDifference.spec : Prop :=
  ∀ (c : Loc) (dqc : DFrac) (a : quorum.JointConfig) (v0 v1 : Loc) (s0 s1 : GSet w64)
    (vm : Loc) (dqv : DFrac) (votes : GMap w64 Bool),
  a.arr = [v0, v1] →
  (GMap.size s0 : Int) < 2 ^ 63 → (GMap.size s1 : Int) < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗ c ↦{dqc} a ∗
      ownIdsetQ v0 (DFrac.own 1) s0 ∗ ownIdsetQ v1 (DFrac.own 1) s1 ∗ vm ↦${dqv} votes }}
    (App (Val (c @!! go.GoType.PointerType quorum.JointConfig.ty
      @!! go!"VoteResultWithDifference")) (Val #vm))
  {{ (res : w8) (d : GoArray w64 2), RET (PairV #res #d);
      c ↦{dqc} a ∗ ownIdsetQ v0 (DFrac.own 1) s0 ∗ ownIdsetQ v1 (DFrac.own 1) s1 ∗
      vm ↦${dqv} votes ∗
      ⌜res = VoteWon ∨ res = VoteLost ∨ res = VotePending⌝ ∗
      ⌜res = VoteWon ↔ MajQ s0 (granted votes) ∧ MajQ s1 (granted votes)⌝ ∗
      ⌜res = VoteLost ↔ ¬ MajQ s0 (s0 \ rejected votes) ∨ ¬ MajQ s1 (s1 \ rejected votes)⌝ ∗
      ⌜d.arr = [W64 (votesToWin s0 votes : Int), W64 (votesToWin s1 votes : Int)]⌝ }}

end spec

end EtcdGrove
end Perennial
