/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/proto/Steps.lean (241f27e).
-/
/-
`proto` — every step preserves `PInv` and only grows the history (`Grows`); the initial state
satisfies `PInv`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.BecomeLeader
public import Dsverify.Proof.github_com.hashicorp.raft.proto.Ack
public import Dsverify.Proof.github_com.hashicorp.raft.proto.Follower
public import Dsverify.Proof.github_com.hashicorp.raft.proto.LeaderAppend
public import Dsverify.Proof.github_com.hashicorp.raft.proto.Misc

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

theorem grows_refl (σ : PState) : Grows σ σ := by
  exact grows_refl' σ

theorem grows_trans {σ1 σ2 σ3 : PState} : Grows σ1 σ2 → Grows σ2 σ3 → Grows σ1 σ3 := by
  exact grows_trans'

/-- The bootstrapped state (stage 4: the bootstrap voters `cv g.data` with log `[g]`, term 1; the
other servers empty, term 0). -/
theorem init_inv (srvs : List SID) (g : Entry) (cv : List w8 → List SID) (hnd : srvs.Nodup)
    (hg1 : g.term = 1) (hgk : g.kind = kConfig) (hcv : cfgValid srvs (cv g.data)) :
    PInv (init srvs g cv) := by
  exact init_inv' srvs g cv hnd hg1 hgk hcv

theorem setTerm_inv (σ : PState) (i : SID) (t : Nat) :
    PInv σ → setTermPre σ i t → PInv (setTerm σ i t) ∧ Grows σ (setTerm σ i t) := by
  exact setTerm_inv' σ i t

theorem newTerm_inv (σ : PState) (i : SID) :
    PInv σ → newTermPre σ i → PInv (newTerm σ i) ∧ Grows σ (newTerm σ i) := by
  exact newTerm_inv' σ i

theorem recordCand_inv (σ : PState) (c : SID) :
    PInv σ → recordCandPre σ c → PInv (recordCand σ c) ∧ Grows σ (recordCand σ c) := by
  exact recordCand_inv' σ c

theorem grantVote_inv (σ : PState) (j c : SID) :
    PInv σ → grantVotePre σ j c → PInv (grantVote σ j c) ∧ Grows σ (grantVote σ j c) := by
  exact grantVote_inv' σ j c

theorem becomeLeader_inv (σ : PState) (c : SID) :
    PInv σ → becomeLeaderPre σ c → PInv (becomeLeader σ c) ∧ Grows σ (becomeLeader σ c) := by
  exact becomeLeader_inv' σ c

theorem leaderAppend_inv (σ : PState) (i : SID) (es : RLog) :
    PInv σ → leaderAppendPre σ i es →
      PInv (leaderAppend σ i es) ∧ Grows σ (leaderAppend σ i es) := by
  exact fun h hp => la_inv h hp

/-- (stage 4) **leaderAppendCfg** keeps the invariant: the new entry's R-commit is the precondition's
commit (`ICfgR`); the commitment's configuration becomes the parent of the latest (the window).
(Review tier-2 1) Its `ILC` obligation is a fourth use of `CL0`: appending `Y` at `p` makes
`(T, k, p)` admissible (`cfgAdm` with `q = p`) for every `k < p`, and a quorum of `Y`'s voters may
already have acknowledged `k`; as at an acknowledgement, take the least leader lacking it and apply
`CL0` to its election log. -/
theorem leaderAppendCfg_inv (σ : PState) (i : SID) (e : Entry) :
    PInv σ → leaderAppendCfgPre σ i e →
      PInv (leaderAppendCfg σ i e) ∧ Grows σ (leaderAppendCfg σ i e) := by
  exact fun h hp => lac_inv h hp

/-- (stage 4) **installCfg** keeps the invariant: the commitment's configuration becomes the latest. -/
theorem installCfg_inv (σ : PState) (T : Nat) :
    PInv σ → installCfgPre σ T → PInv (installCfg σ T) ∧ Grows σ (installCfg σ T) := by
  exact fun h hp => installCfg_inv' h hp

theorem truncate_inv (σ : PState) (i : SID) (prev pt : Nat) (ents : RLog) (lci j : Nat) :
    PInv σ → truncatePre σ i prev pt ents lci j →
      PInv (truncate σ i (prev + 1 + j)) ∧ Grows σ (truncate σ i (prev + 1 + j)) := by
  exact truncate_inv' σ i prev pt ents lci j

theorem followerStore_inv (σ : PState) (i : SID) (prev pt : Nat) (ents : RLog) (lci j : Nat) :
    PInv σ → followerStorePre σ i prev pt ents lci j →
      PInv (followerStore σ i (ents.drop j)) ∧ Grows σ (followerStore σ i (ents.drop j)) := by
  exact fun h hp => followerStore_inv' h hp

theorem ack_inv (σ : PState) (i : SID) (k : Nat) :
    PInv σ → ackPre σ i k → PInv (ack σ i (σ.term i) k) ∧ Grows σ (ack σ i (σ.term i) k) := by
  exact ack_inv' σ i k

theorem commit_inv (σ : PState) (T k : Nat) :
    PInv σ → commitPre σ T k → PInv (commit σ T k) ∧ Grows σ (commit σ T k) := by
  exact commit_inv' σ T k

theorem learnCommit_inv (σ : PState) (i : SID) (k T' : Nat) :
    PInv σ → learnCommitPre σ i k T' →
      PInv (learnCommit σ i k T') ∧ Grows σ (learnCommit σ i k T') := by
  exact learnCommit_inv' σ i k T'

/-- **publish** (stage 2) keeps the invariant. -/
theorem publish_inv (σ : PState) (i : SID) (k : Nat) :
    PInv σ → publishPre σ i k →
      PInv (publish σ (σ.term i) k) ∧ Grows σ (publish σ (σ.term i) k) := by
  exact publish_inv' σ i k

theorem setCidx_inv (σ : PState) (i : SID) (c : Nat) :
    PInv σ → setCidxPre σ i c → PInv (setCidx σ i c) ∧ Grows σ (setCidx σ i c) := by
  exact setCidx_inv' σ i c

end proto
end github_com.hashicorp.raft
end Perennial
