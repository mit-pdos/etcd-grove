/-
Port of `election_proof/spec_MajorityConfig__VoteResult.v`.

Lean notes: `Z.of_nat (size s)` is `(GMap.size s : Int)`. The comment's remark that
`ownTracker` carries `cfg ≠ ∅` is kept from Rocq as written, though `ownTracker` no
longer does (its `Hcfg_size` comment: the premise moved to `JointConfig.VoteResult`,
`TallyVotes` and `poll` on 2026-09-29).
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

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

/-- `c.VoteResult(votes)` for a *single* majority quorum.

This is the arithmetic half of `TallyVotes`: `JointConfig.VoteResult` calls it on each
of the two components of the joint config (`quorum.go:154,158`) and combines the two
answers.

The receiver is a `*MajorityConfig`, i.e. a location `cref` holding the map value
`mref`, because the call site indexes the `JointConfig` array and takes the address of
the element. The component is described by its *id set* `s`, and the two shapes a
component can have are both allowed:

  - `mref = map.nil` -- the second component of a simple configuration
    (`ownTracker`'s `Hvoters_arr`); the nil map has no keys, so `s = ∅`;
  - a real map `mref ↦$ ids` with `domSet ids = s`.

The body (`quorum.MajorityConfig.VoteResult.impl`, majority.go:170) is

    if len(c) == 0 { return VoteWon }        // "elections on an empty
                                             //  config win", by convention
    var votedCnt, missing int
    for id := range c {
      v, ok := votes[id]
      if !ok { missing++; continue }
      if v { votedCnt++ }
    }
    q := len(c)/2 + 1
    if votedCnt >= q { return VoteWon }
    if votedCnt+missing >= q { return VotePending }
    return VoteLost

so `votedCnt = size (granted votes ∩ s)`, `missing = size (s \ domSet votes)` and, by
`IsQuorum_alt` (`InvTracker.lean`), `votedCnt ≥ q` is exactly `IsQuorum s (granted
votes)`. For `VoteLost`, `votedCnt + missing = size (s \ rejected votes)`
(`size_cfg_minus_rejected`), so `votedCnt + missing < q` is exactly
`¬ IsQuorum s (s \ rejected votes)`.

**Why the two `s ≠ ∅` premises.** At `s = ∅` the function returns `VoteWon` without
computing anything, while `IsQuorum ∅ q` unfolds to `0 < 2 * 0`, which is `False`; so
the `VoteWon` equivalence is simply false there, and the empty case is reported
separately. `ownTracker` carries `cfg ≠ ∅`, which is what lets the caller use the
equivalences for the first component; the second component *is* empty, and the caller
uses the `s = ∅` clause for it.

The size bound is needed because `len`, `votedCnt`, `missing` and `q` are `go.int`: with
`size s < 2^63` none of the additions wraps. Callers get it from `ownTracker`'s
`Hcfg_size`. -/
abbrev quorum.MajorityConfig.VoteResult.spec : Prop :=
  ∀ (s : GSet w64) (cref mref votes_ref : Loc) (dq : DFrac) (votes : GMap w64 Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗
      ⌜(GMap.size s : Int) < 2 ^ 63⌝ ∗
      cref ↦ mref ∗ votes_ref ↦${dq} votes ∗
      (⌜mref = map.nil ∧ s = ∅⌝ ∨
       ∃ (ids : GMap w64 Unit), ⌜domSet ids = s⌝ ∗ mref ↦$ ids) }}
    (App (Val (cref @!! go.GoType.PointerType quorum.MajorityConfig.ty @!! go!"VoteResult"))
      (Val #votes_ref))
  {{ (res : w8), RET #res;
      cref ↦ mref ∗ votes_ref ↦${dq} votes ∗
      (⌜mref = map.nil ∧ s = ∅⌝ ∨
       ∃ (ids : GMap w64 Unit), ⌜domSet ids = s⌝ ∗ mref ↦$ ids) ∗
      ⌜res = VoteWon ∨ res = VoteLost ∨ res = VotePending⌝ ∗
      ⌜s = ∅ → res = VoteWon⌝ ∗
      ⌜s ≠ ∅ → (res = VoteWon ↔ IsQuorum s (granted votes))⌝ ∗
      ⌜s ≠ ∅ → (res = VoteLost ↔ ¬ IsQuorum s (s \ rejected votes))⌝ }}

end spec

end EtcdGrove
end Perennial
