/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__runCandidate.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).runCandidate`: a pre-election, then an election of term `s.term + 1`,
counting distinct granted votes (`voteTally`) up to a quorum (`becomeLeader_upd` before
`setState(Leader)`), or stepping down on a newer term (`setTerm_upd`), or timing out.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__runCandidate
public import Dsverify.Proof.github_com.hashicorp.raft.main.Respond
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__electSelf
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__preElectSelf
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__quorumSize
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__processRPC
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getState
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLeader
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setState
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__config
public import Dsverify.Spec.github_com.hashicorp.raft.randomTimeout
public import Dsverify.Spec.github_com.hashicorp.raft.deferError__respond
public import Dsverify.Proof.github_com.hashicorp.raft.DeferRespond
public import Dsverify.Proof.github_com.hashicorp.raft.main.CfgReq
public import Dsverify.Proof.github_com.hashicorp.raft.handlers.Elect

@[expose] public section

set_option linter.deprecated false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

open proto gprot

theorem nodup_len_le {α} [DecidableEq α] : ∀ {G L : List α}, G.Nodup → (∀ x ∈ G, x ∈ L) →
    G.length ≤ L.length
  | [], _, _, _ => Nat.zero_le _
  | x :: G, L, h1, h2 => by
    have hx : x ∈ L := h2 x (List.mem_cons_self ..)
    have hnd := List.nodup_cons.1 h1
    have ih := nodup_len_le (L := L.erase x) hnd.2 (fun y hy => by
      have hne : y ≠ x := fun h => hnd.1 (h ▸ hy)
      exact (List.mem_erase_of_ne hne).2 (h2 y (List.mem_cons_of_mem _ hy)))
    rw [List.length_erase_of_mem hx] at ih
    have : 0 < L.length := List.length_pos_of_mem hx
    simp only [List.length_cons]; omega

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- The candidate loop's election state while still `Candidate` (entered at protocol state `s0`):
the pre-election (no vote channel, term unchanged, no vote counted, the pre-vote channel) or the
election of `s.term` (no pre-vote channel, the vote channel, the distinct granted votes `G`
counted in `g`, (review T1-4) the election log `L` as a persistent fact (`llogPre`; the vote
channel's configuration is `L`'s, fixed at `electSelf`) with its recorded `candIs`, and either the
current log is `L`, with the term's publication bound (stage 2: `electTerm_upd`'s `pubOwn`, for the
leader state) and (stage 4, tier-2 2) both halves of the commitment's configuration at `0`
(`electTerm_upd`'s, for `becomeLeader_upd`), or (stage 2: a transfer candidate stored entries of the
term's leader) another leader of the term, so the election cannot be won (`leader_votes_agree`
over `L`)); (stage 4) the granted voters are of `L`'s configuration, and `L` is `Lq`, the log whose
configuration `votesNeeded` was last computed from (`quorumSize`; at the loop's start `s0.log`, after
the pre-vote the log at `electSelf`: fork fix 02f88d5, finding candidate-stale-quorum). -/
def candPhase (γ : GNames) (i : SID) (s0 s : SState) (vch pch : Loc) (g : w64) (Lq : RLog) : IProp GF :=
  iprop((⌜vch = chan.nil ∧ s.term = s0.term ∧ g = W64 0⌝ ∗
      ∃ γp : ChanNames, isChanBag (V := Loc) γp pch (pvP γ (s0.term + 1))) ∨
    (⌜pch = chan.nil⌝ ∗ ∃ (γv : GName) (γc : ChanNames) (G : List SID) (L : RLog),
      isChanBag (V := Loc) γc vch (voteP γ i s.term (cfgOfC γ.cv L) γv) ∗ voteTally γ i s.term γv G ∗
      candIs γ i s.term L.length (lastTerm L) ∗ llogPre γ (lastTerm L) L ∗
      ((⌜L = s.log⌝ ∗ pubOwn γ i s.term 0 ∗ ccfgOwn γ i s.term 0 ∗ ccfgOwn γ i s.term 0) ∨
       (∃ ℓ : SID, ⌜ℓ ≠ i⌝ ∗ leaderIs γ s.term ℓ)) ∗
      ⌜uint.nat g = G.length ∧ G.length ≤ γ.srvs.length ∧ (∀ j ∈ G, j ∈ cfgOfC γ.cv L) ∧
        L = Lq⌝))

theorem candPhase_keep (γ : GNames) (i : SID) (s0 s s' : SState) (vch pch : Loc) (g : w64) (Lq : RLog)
    (h : s'.term = s.term ∧ s'.log = s.log) :
    candPhase (GF := GF) γ i s0 s vch pch g Lq ⊢ candPhase γ i s0 s' vch pch g Lq := by
  try unfold candPhase
  rw [h.1, h.2]

/-- The term has another leader (a transfer candidate stored its entries): the election is dead. -/
theorem candPhase_dead (γ : GNames) (i : SID) (s0 s s' : SState) (vch pch : Loc) (g : w64) (Lq : RLog)
    (h : s'.term = s.term) (ℓ : SID) (hℓ : ℓ ≠ i) :
    leaderIs (GF := GF) γ s.term ℓ ∗ candPhase γ i s0 s vch pch g Lq ⊢ candPhase γ i s0 s' vch pch g Lq := by
  unfold candPhase
  iintro ⟨#Hl, (⟨%Hp, Hb⟩ | ⟨%Hp, %γv, %γc, %G, %L, Hb, Ht, #Hc, #Hlp, -, %Hg⟩)⟩
  · ileft; iframe; ipureintro; rw [h]; exact Hp
  · iright
    isplitr; · ipureintro; exact Hp
    iexists γv, γc, G, L
    rw [h]
    iframe
    iframe #
    isplitr
    · iright
      first | (iexists ℓ; iframe Hl; ipureintro; exact hℓ) | (ipureintro; exact hℓ)
    ipureintro; exact Hg

/-- The stable store and the protocol state out of `mainOwnAt`, given back after a term store
(`setCurrentTerm`) as a follower or candidate, (review T1-1) to a term at least the current one
(`mainOwnAt`'s committed index is committed by a commit of a term `≤ s.term`, `cmtIdx`). -/
theorem mainOwnAt_term (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (st : w32) :
    mainOwnAt r γ rc i s st ⊢ ∃ sst : StableAbs, rc.ownS sst ∗ srvOwn γ i s ∗
      (∀ (t : w64), ⌜st ≠ stLeader⌝ -∗ ⌜s.term ≤ uint.nat t⌝ -∗
        rc.ownS (StableAbs.mk (sst.ints.insert (go!"CurrentTerm" : List w8) t) sst.bytes) -∗
        srvOwn γ i { s with term := uint.nat t } -∗
        mainOwnAt r γ rc i { s with term := uint.nat t } st) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

/-- The term store's ghost update for adopting an existing term `t ≥ s.term` (`setTerm_upd`). -/
theorem setTerm_cb [hRB : ReceiptBoundLe GF (2 ^ 62)] (γ : GNames) (i : SID) (s : SState) (t : Nat)
    (hle : s.term ≤ t) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ termOk γ t ⊢
      ∀ t0 : Nat, termCouple γ i t0 ={⊤ \ ↑termN}=∗ termCouple γ i t ∗ srvOwn γ i { s with term := t } := by
  have hgt : (↑gprotN : CoPset) ⊆ ⊤ \ ↑termN := by unfold gprotN termN raftN; solve_ndisj
  iintro ⟨#HI, Hs, #Hok⟩ %t0 Htc
  imod termCouple_agree γ _ hgt i s t0 $$ [HI Hs Htc] with ⟨Hs, Htc, %ht0⟩
  · iframe; iframe #
  subst ht0
  imod setTerm_upd γ _ hgt i s t hle $$ [HI Hs Htc Hok] with ⟨Hs, Htc, -⟩
  · iframe; iframe #
  imodintro
  iframe

include sem package_sem in
theorem obsArg_follower' (γ : GNames) (i : SID) (s : SState) :
    ⊢ obsArg (GF := GF) γ i s (interface.mkOk RaftState.ty #(W32 0)) :=
  obsArg_follower γ i s

/-- The protocol state and the `state` ghost half out of `mainOwnAt`, given back with any state
(`Leader` with a `leaderIs` witness, the term's publication bound `0` and, stage 4, the main
goroutine's half of the commitment's configuration at the latest configuration and the election
log's length `len0Is`, which covers the commit index and the latest configuration's index). -/
theorem mainOwnAt_lead (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (st : w32) :
    mainOwnAt r γ rc i s st ⊢ srvOwn γ i s ∗ ghostVar rc.names.state (1 : Qp).half st ∗
      (∀ st' : w32, srvOwn γ i s -∗ ghostVar rc.names.state (1 : Qp).half st' -∗
        (⌜st' ≠ stLeader⌝ ∨ leaderIs γ s.term i ∗ pubOwn γ i s.term 0 ∗
          ccfgOwn γ i s.term (lastCfgIdx s.log) ∗ len0Is γ s.term s.log.length ∗
          ⌜s.cidx ≤ s.log.length⌝) -∗ mainOwnAt r γ rc i s st') := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

theorem voteTally_facts (γ : GNames) (i : SID) (T : Nat) (γv : GName) (G : List SID) :
    voteTally (GF := GF) γ i T γv G ⊢ voteTally γ i T γv G ∗ ⌜G.Nodup ∧ ∀ j ∈ G, j ∈ γ.srvs⌝ := by
  unfold voteTally
  iintro ⟨H, %h⟩
  iframe H
  ipureintro; exact ⟨h, h⟩

include sem package_sem in
theorem obsArg_leader' (γ : GNames) (i : SID) (s : SState) :
    obsArg (GF := GF) γ i s (interface.mkOk RaftState.ty #(W32 2)) ⊣⊢
      srvOwn γ i s ∗ leaderIs γ s.term i := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

/-- The protocol state out of `mainOwnAt` (and back). -/
theorem mainOwnAt_srv (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (st : w32) :
    mainOwnAt r γ rc i s st ⊢ srvOwn γ i s ∗ (srvOwn γ i s -∗ mainOwnAt r γ rc i s st) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end defs

end github_com.hashicorp.raft

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.Raft.runCandidate.wp_proof
    (wp_getState : github_com.hashicorp.raft.raftState.getState.spec (GF := GF) (hG := hG))
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_preElectSelf : github_com.hashicorp.raft.Raft.preElectSelf.spec (GF := GF) (hG := hG))
    (wp_electSelf : github_com.hashicorp.raft.Raft.electSelf.spec (GF := GF) (hG := hG))
    (wp_BoolLoad : sync.atomic.Bool.Load.spec (GF := GF) (hG := hG))
    (wp_BoolStore : sync.atomic.Bool.Store.spec (GF := GF) (hG := hG))
    (wp_config : github_com.hashicorp.raft.Raft.config.spec (GF := GF) (hG := hG))
    (wp_randomTimeout : github_com.hashicorp.raft.randomTimeout.spec (GF := GF) (hG := hG))
    (wp_quorumSize : github_com.hashicorp.raft.Raft.quorumSize.spec (GF := GF) (hG := hG))
    (wp_processRPC : github_com.hashicorp.raft.Raft.processRPC.spec (GF := GF) (hG := hG))
    (wp_setState : github_com.hashicorp.raft.Raft.setState.spec (GF := GF) (hG := hG))
    (wp_setCurrentTerm : github_com.hashicorp.raft.Raft.setCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_setLeader : github_com.hashicorp.raft.Raft.setLeader.spec (GF := GF) (hG := hG))
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG))
    (wp_Clone : github_com.hashicorp.raft.Configuration.Clone.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.runCandidate.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
