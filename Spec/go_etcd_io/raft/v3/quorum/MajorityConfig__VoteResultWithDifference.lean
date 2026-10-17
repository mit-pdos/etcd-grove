/-
New in etcd-io/raft#168 (share witness), Lean-first (`notes/pr-verify/raft-168.md`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvTrackerC

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

open Classical in
/-- How many more granted votes a majority half `s` needs to win (raft#168's "votes to win"):
`0` once the half has won (by convention every election on the empty half is won) or can no
longer win, otherwise the majority `|s|/2 + 1` less the granted votes of `s`. -/
def votesToWin (s : GSet w64) (votes : GMap w64 Bool) : Nat :=
  if MajQ s (granted votes) ∨ ¬ MajQ s (s \ rejected votes) then 0
  else GMap.size s / 2 + 1 - GMap.size (granted votes ∩ s)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `c.VoteResultWithDifference(votes)` (raft#168, majority.go), `MajorityConfig.VoteResult`
that also returns how many more granted votes would win:

    if len(c) == 0 { return VoteWon, 0 }
    ny := [2]int{}                    // no and yes counts
    var missing int
    for id := range c {
      v, ok := votes[id]
      if !ok { missing++; continue }
      if v { ny[1]++ } else { ny[0]++ }
    }
    q := len(c)/2 + 1
    if ny[1] >= q { return VoteWon, 0 }
    if ny[1]+missing >= q { return VotePending, q - ny[1] }
    return VoteLost, 0

The verdict is `MajorityConfig.VoteResult`'s, conjunct for conjunct (the same receiver and
votes, the same equivalences with `IsQuorum`): the PR's new function is the old one plus the
count. The count is `votesToWin s votes`: `0` unless the vote is pending, and then the
majority less the granted votes, at least `1`. The size bound is `VoteResult`'s (`int`
counters). -/
abbrev quorum.MajorityConfig.VoteResultWithDifference.spec : Prop :=
  ∀ (s : GSet w64) (cref mref votes_ref : Loc) (dq : DFrac) (votes : GMap w64 Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗
      ⌜(GMap.size s : Int) < 2 ^ 63⌝ ∗
      cref ↦ mref ∗ votes_ref ↦${dq} votes ∗
      (⌜mref = map.nil ∧ s = ∅⌝ ∨
       ∃ (ids : GMap w64 Unit), ⌜domSet ids = s⌝ ∗ mref ↦$ ids) }}
    (App (Val (cref @!! go.GoType.PointerType quorum.MajorityConfig.ty
      @!! go!"VoteResultWithDifference")) (Val #votes_ref))
  {{ (res : w8) (d : w64), RET (PairV #res #d);
      cref ↦ mref ∗ votes_ref ↦${dq} votes ∗
      (⌜mref = map.nil ∧ s = ∅⌝ ∨
       ∃ (ids : GMap w64 Unit), ⌜domSet ids = s⌝ ∗ mref ↦$ ids) ∗
      ⌜res = VoteWon ∨ res = VoteLost ∨ res = VotePending⌝ ∗
      ⌜s = ∅ → res = VoteWon⌝ ∗
      ⌜s ≠ ∅ → (res = VoteWon ↔ IsQuorum s (granted votes))⌝ ∗
      ⌜s ≠ ∅ → (res = VoteLost ↔ ¬ IsQuorum s (s \ rejected votes))⌝ ∗
      ⌜d = W64 (votesToWin s votes : Int)⌝ }}

end spec

end EtcdGrove
end Perennial
