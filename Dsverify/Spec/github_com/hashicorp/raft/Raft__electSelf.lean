/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__electSelf.lean (241f27e).
-/
/-
`raft.(*Raft).electSelf`'s spec (main goroutine; internal to MAIN-C). Starts the election of
term `s.term + 1` (protocol steps `newTerm`+`recordCand` at the `currentTerm` store, the self
vote `grantVote`), asks every other voter for its vote in a goroutine, and returns the vote
channel: a bag of `*voteResult` carrying, per voter, its token of this election (`voteP`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.main.MainCLemmas
public import Dsverify.Proof.github_com.hashicorp.raft.iface.Net

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `(*Raft).electSelf()`: the candidate `i` moves to `s.term + 1`, votes for itself if it is a voter of its latest configuration (FOLLOW-10: a non-voter candidate,
`timeoutNow`, does not) and asks each voter
of its latest configuration (stage 4: `cfgOfC γ.cv s.log`, the voters its quorum is of,
`gprot.becomeLeader_upd`; stage 3: the fixed voters) for its vote; the answers come on the returned
channel (`voteP`). (Review T1-4) Its log as a prefix of the leader log of its last term (`llogPre`,
`gprot.llogPre_srv`: the election log, for `leader_votes_agree` after the log changed); (tier-2 2)
both halves of its commitment's configuration for the new term at `0` (`electTerm_upd`'s, for
`becomeLeader_upd`). -/
abbrev github_com.hashicorp.raft.Raft.electSelf.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
      mainOwnAt r γ rc i s stCandidate ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"electSelf")) (Val #()))
  {{ (ch : Loc), RET #ch; ∃ (γv : GName) (γc : ChanNames) (s1 : SState),
      mainOwnAt r γ rc i s1 stCandidate ∗
      ⌜s1.term = s.term + 1 ∧ s1.log = s.log ∧
        (s1.vterm = s.term + 1 ∧ s1.vcand = i ∨ i ∉ cfgOfC γ.cv s.log)⌝ ∗
      candIs γ i (s.term + 1) s.log.length (lastTerm s.log) ∗ pubOwn γ i (s.term + 1) 0 ∗
      llogPre γ (lastTerm s.log) s.log ∗ ccfgOwn γ i (s.term + 1) 0 ∗ ccfgOwn γ i (s.term + 1) 0 ∗
      isChanBag (V := Loc) γc ch (voteP γ i (s.term + 1) (cfgOfC γ.cv s.log) γv) ∗ rtok tid }}

end spec

end Perennial
