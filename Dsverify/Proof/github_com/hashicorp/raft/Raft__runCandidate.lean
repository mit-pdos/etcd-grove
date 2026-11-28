/-
(hraft_robust R4a: over the crash views.) Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__runCandidate.lean (241f27e).
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
public import Dsverify.Proof.github_com.hashicorp.raft.DurHelpers
public import Dsverify.Proof.github_com.hashicorp.raft.handlers.Base

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
    mainOwnAt r γ rc i s st ⊢ ∃ (sst : StableAbs) (g : w64), stVS rc sst g ∗ srvV rc s ∗
      ghostVar rc.dur.pw 1 (none : Option Pend) ∗
      (∀ (t : w64), ⌜st ≠ stLeader⌝ -∗ ⌜s.term ≤ uint.nat t⌝ -∗
        stVS rc (StableAbs.mk (sst.ints.insert (go!"CurrentTerm" : List w8) t) sst.bytes) g -∗
        srvV rc { s with term := uint.nat t } -∗ ghostVar rc.dur.pw 1 (none : Option Pend) -∗
        mainOwnAt r γ rc i { s with term := uint.nat t } st) := by
  unfold mainOwnAt
  iintro ⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %c, Hs, Hpw, ⟨%g, HS, %Hg⟩, %Hvm, Hll, Hst, Hl, H⟩
  iexists sst, g
  iframe HS Hs Hpw
  iintro %t %hst %hle HS Hs Hpw
  iexists a, _, cfg, ccfg, cidx, li, lch, γl, bs, c
  icases H with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, Hcm, H13⟩
  ihave Hcm := cmtIdx_mono γ s.term (uint.nat t) s.log s.log (uint.nat cidx) hle rfl $$ Hcm
  isplitl [Hs]
  · iexact Hs
  isplitl [Hpw]
  · iexact Hpw
  isplitl [HS]
  · iexists g; iframe HS; ipureintro; exact Hg
  isplitr
  · ipureintro
    exact voteMatches_term sst s t (uint.nat t) Hvm hle
  iframe
  ileft; ipureintro; exact hst

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
    mainOwnAt r γ rc i s st ⊢ srvV rc s ∗ ghostVar rc.names.state (1 : Qp).half st ∗
      (∀ st' : w32, srvV rc s -∗ ghostVar rc.names.state (1 : Qp).half st' -∗
        (⌜st' ≠ stLeader⌝ ∨ leaderIs γ s.term i ∗ pubOwn γ i s.term 0 ∗
          ccfgOwn γ i s.term (lastCfgIdx s.log) ∗ len0Is γ s.term s.log.length ∗
          ⌜s.cidx ≤ s.log.length⌝) -∗ mainOwnAt r γ rc i s st') := by
  unfold mainOwnAt
  iintro ⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %c, Hs, H2, H3, H4, H5, Hst, -, H⟩
  iframe Hs Hst
  iintro %st' Hs Hst Hl
  iexists a, sst, cfg, ccfg, cidx, li, lch, γl, bs, c
  icases H with ⟨H6, H7, H8, %Ha, H10, H11, H12, H13, H14, H15, H16, %Hcc, H17⟩
  iframe
  isplitl [Hl]
  · icases Hl with (%Hl | ⟨Hl, Hp, Hcc0, #Hn0, %Hci⟩)
    · ileft; ipureintro; exact Hl
    · iright
      iframe Hl Hcc0
      isplitl [Hp]
      · iexists 0; iframe; ipureintro; omega
      iexists s.log.length
      iframe Hn0
      isplitr; · ileft; ipureintro; exact Hci
      ileft; ipureintro; right
      rw [Hcc.1]; exact (lastCfgIdx_spec s.log).1
  isplitr; · ipureintro; exact Ha
  ipureintro; exact Hcc

theorem voteTally_facts (γ : GNames) (i : SID) (T : Nat) (γv : GName) (G : List SID) :
    voteTally (GF := GF) γ i T γv G ⊢ voteTally γ i T γv G ∗ ⌜G.Nodup ∧ ∀ j ∈ G, j ∈ γ.srvs⌝ := by
  unfold voteTally
  iintro ⟨H, %h⟩
  iframe H
  ipureintro; exact ⟨h, h⟩

include sem package_sem in
theorem obsArg_leader' (γ : GNames) (i : SID) (s : SState) :
    obsArg (GF := GF) γ i s (interface.mkOk RaftState.ty #(W32 2)) ⊣⊢ leaderIs γ s.term i :=
  obsArg_leader γ i s

/-- The protocol state out of `mainOwnAt` (and back). -/
theorem mainOwnAt_srv (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (st : w32) :
    mainOwnAt r γ rc i s st ⊢ srvV rc s ∗ (srvV rc s -∗ mainOwnAt r γ rc i s st) := by
  unfold mainOwnAt
  iintro ⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %c, Hs, H⟩
  iframe Hs
  iintro Hs
  iexists a, sst, cfg, ccfg, cidx, li, lch, γl, bs, c
  iframe

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
    github_com.hashicorp.raft.Raft.runCandidate.spec (GF := GF) (hG := hG) :=
  fun r γ rc i s0 tid => by
  wp_start as ⟨#Hr, Hm, Htok⟩
  ihave ⟨#HInv, #Hvi⟩ := isRaft_proto r γ rc i $$ Hr
  ihave #Htc := isRaft_termCell r γ rc i $$ Hr
  ihave #Hdur := isRaft_durInv r γ rc i $$ Hr
  ihave #Hsc := isRaft_stateCell r γ rc i $$ Hr
  ihave #Hcft := isRaft_cftCell r γ rc i $$ Hr
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨-, #HlocalID, #HlocalAddr, #Hpvd, -⟩
  wp_apply wp_with_defer as %defer Hdefer
  icases mainOwnAt_srv r γ rc i s0 stCandidate $$ Hm with ⟨Hsrv, Hm⟩
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  ihave H2 := srvOwn_facts_R γ rc i gd_top s0 $$ [$HInv $Hdur $Hsrv]
  imod H2 $$ Hnc with ⟨Hnc, Hsrv, -, %Hsf0⟩
  iframe Hnc
  imodintro
  have hs0 : s0.term < 2 ^ 62 := Hsf0.2.2.2.2.2.1
  wp_apply (wp_getCurrentTerm.1 r γ rc i s0) $$ [Hsrv] with Hsrv
  · iframe; iframe #
  ihave Hm := Hm $$ Hsrv
  wp_apply (wp_cft_Load wp_BoolLoad r) $$ [Hcft] as %bc -
  · iexact Hcft
  -- a candidate from a leadership transfer skips the pre-vote (stage 2)
  rw [show (!bc) = decide (bc = false) by cases bc <;> rfl]
  ipersist r
  ihave %hcv := isRaft_cv r γ rc i $$ Hr
  wp_join iprop(∃ (s1 : SState) (vch1 pch1 : Loc), mainOwnAt r γ rc i s1 stCandidate ∗
      voteCh_ptr ↦ vch1 ∗ prevoteCh_ptr ↦ pch1 ∗ rtok tid ∗ candPhase γ i s0 s1 vch1 pch1 (W64 0) s0.log ∗
      ⌜s1.log = s0.log⌝)
    with [Hm Htok voteCh prevoteCh] as ⟨%s1, %vch1, %pch1, Hm, voteCh, prevoteCh, Htok, Hph1, %Hs1l⟩
  · wp_apply (wp_preElectSelf r γ rc i s0 stCandidate) $$ [Hm Htok] as %pch ⟨%γp, Hm, #Hpb, Htok⟩
    · iframe; iframe #
    wp_join_done
    iexists s0, _, pch
    iframe
    isplitl
    · try unfold candPhase
      ileft
      isplitr; · ipureintro; exact ⟨rfl, rfl, rfl⟩
      iexists γp; iexact Hpb
    ipureintro; rfl
  · wp_apply (wp_electSelf r γ rc i s0) $$ [Hm Htok]
      as %vch' ⟨%γv, %γc, %s2, Hm, %Hs2, #Hcand, Hpub, #Hlp, Hc1, Hc2, #Hvb, Htok⟩
    · iframe; iframe #
    obtain ⟨hs2t, hs2l, -⟩ := Hs2
    wp_join_done
    iexists s2, vch', _
    iframe
    isplitl
    · try unfold candPhase
      rw [hs2t, hs2l]
      iright
      isplitr; · ipureintro; rfl
      iexists γv, γc, [], s0.log
      iframe #
      isplitr; · iapply voteTally_nil
      isplitl [Hpub Hc1 Hc2]; · ileft; iframe; ipureintro; rfl
      ipureintro; simp
    ipureintro; exact hs2l
  wp_apply (wp_config r γ rc i) $$ [$Hr] with %c %Hc
  wp_apply wp_randomTimeout with %tch0 Htch0
  icases mainOwnAt_split r γ rc i s1 stCandidate $$ Hm with ⟨%cfg, %ccfg, %cidx, %li, Hcfgs, #Hcfg, %Hli, Hst, Hm⟩
  icases cfgAtIs_srvsV γ s1.log _ cfg hcv Hli $$ Hcfg with ⟨%ss, #Hss, %Hsv⟩
  obtain ⟨Hsok, Hvs⟩ := Hsv
  rw [Hs1l] at Hvs
  have hvb : (srvVoters ss).length < 2 ^ 32 := Nat.lt_of_le_of_lt (srvVoters_length_le ss) Hsok.2.1
  wp_apply (wp_quorumSize r ccfg cfg cidx li ss (DFrac.own 1) DFrac.discard) $$ [Hcfgs Hss] with ⟨Hcfgs, -⟩
  · iframe; iframe #; ipureintro; have := Hsok.2.1; omega
  ihave Hm := Hm $$ %stCandidate [] Hcfgs Hst
  · ipureintro; right; rfl
  ihave HI : (∃ (s : SState) (st : w32) (vch pch' tch : Loc) (et : time.Duration) (pg pr g : w64)
      (Lq : RLog) (vn : w64),
      "Hm" ∷ mainOwnAt r γ rc i s st ∗
      "voteCh" ∷ voteCh_ptr ↦ vch ∗ "prevoteCh" ∷ prevoteCh_ptr ↦ pch' ∗
      "electionTimer" ∷ electionTimer_ptr ↦ tch ∗ "electionTimeout" ∷ electionTimeout_ptr ↦ et ∗
      "preVoteGrantedVotes" ∷ preVoteGrantedVotes_ptr ↦ pg ∗
      "preVoteRefusedVotes" ∷ preVoteRefusedVotes_ptr ↦ pr ∗
      "grantedVotes" ∷ grantedVotes_ptr ↦ g ∗
      "Htimer" ∷ (⌜tch = chan.nil⌝ ∨ ∃ γt, isChanBag (V := time.Time) γt tch (fun _ => iprop(True))) ∗
      "Htok" ∷ rtok tid ∗ "votesNeeded" ∷ votesNeeded_ptr ↦ vn ∗
      "%Hvn" ∷ ⌜uint.nat vn = (cfgOfC γ.cv Lq).length / 2 + 1 ∧ (cfgOfC γ.cv Lq).length < 2 ^ 32⌝ ∗
      "Hphase" ∷ (⌜st ≠ stCandidate ∧ st ≠ stLeader⌝ ∨ (⌜st = stCandidate⌝ ∗ candPhase γ i s0 s vch pch' g Lq)) : IProp GF)
    $$ [Hm voteCh prevoteCh electionTimer electionTimeout preVoteGrantedVotes preVoteRefusedVotes
      grantedVotes Htch0 Htok Hph1 votesNeeded]
  · iexists s1, stCandidate, _, _, _, _, _, _, _, s0.log, _
    iframe
    isplitr; · ipureintro; rw [Hvs]; exact ⟨by word, hvb⟩
    iright
    isplitr; · ipureintro; rfl
    iexact Hph1
  ihave #Hch := isRaft_chans r γ rc i $$ Hr
  unfold raftChans
  unfold deadField deadChan
  icases Hch with ⟨⟨%applyCh, #HapplyCh, %γa, #Happly⟩, ⟨%vchn, #Hvf, %γvn, #Hvbn⟩,
    ⟨%ltch, #Hltf, %γlt, #Hltb⟩, -, -, -, -, ⟨%cch, #Hcchf, %γq, #Hcchb⟩, ⟨%c3, #Hf3, %γ3, #Hb3⟩,
    ⟨%c1, #Hf1, %γ1, #Hb1⟩, ⟨%c5, #Hf5, %γ5, #Hb5⟩, ⟨%c8, #Hf8, %γ8, #Hb8⟩,
    ⟨%c10, #Hf10, %γ10, #Hb10⟩, ⟨%c11, #Hf11, %γ11, #Hb11⟩⟩
  ihave ⟨%x, %rpcCh, #Htrans, #HrpcCh, #Htr⟩ := isRaft_transport r γ rc i $$ Hr
  unfold isTransport isRpcChan
  icases Htr with ⟨⟨%γrpc, #Hrpc⟩, -⟩
  ihave ⟨%eNL, #HeNL⟩ := isRaftErr_of_init (GF := GF) RaftErr.notLeader $$ Hpkg
  ihave #HgNL0 := isRaftErr_global RaftErr.notLeader eNL $$ HeNL
  ihave #HgNL : (globalAddr ErrNotLeader ↦□ eNL : IProp GF) $$ []
  · have e : RaftErr.notLeader.var = ErrNotLeader := rfl
    rw [← e]
    iexact HgNL0
  wp_for HI
  icases mainOwnAt_state' r γ rc i s st $$ Hm with ⟨Hst, Hm⟩
  wp_apply (wp_getState.1 r rc st) $$ [$Hsc $Hst] with Hst
  ihave Hm := Hm $$ Hst
  wp_if_destruct
  · -- still a candidate
    have hst : st = stCandidate := of_decide_eq_true (go.IntoValInj.intoVal_inj Hif)
    subst hst
    icases Hphase with (%Hne | ⟨-, Hphase⟩)
    · exact absurd rfl Hne.1
    wp_apply_core chan.wp_select_blocking_nil
    -- rpcCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft
      iapply bag_clause' γrpc rpcCh (rpcP γ rc.snapP i) _ _ $$ Hrpc
      inext
      iintro %v Hv
      wp_auto
      wp_apply (wp_processRPC r γ rc i v s stCandidate) $$ [Hm Hv Htok] with ⟨%s', %st', Hm, Htok, Hkeep⟩
      · iframe; iframe #
      wp_for_post
      iframe
      iexists s', st', _, _, _, _, _, _, _, Lq, vn
      iframe
      isplitr; · ipureintro; exact Hvn
      icases Hkeep with (%Hkeep | ⟨%hk, %ℓ, %hℓ, #Hl⟩)
      · rcases Hkeep with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
        · ileft; ipureintro; subst h; decide
        · iright
          isplitr; · ipureintro; rfl
          iapply candPhase_keep γ i s0 s s' _ _ _ _ h $$ Hphase
        · iright
          isplitr; · ipureintro; rfl
          iapply candPhase_keep γ i s0 s s' _ _ _ _ h $$ Hphase
      · have h1 := hk.1
        have h3 := hk.2
        subst h1
        iright
        isplitr; · ipureintro; rfl
        iapply candPhase_dead γ i s0 s s' _ _ _ _ h3 ℓ hℓ $$ [$Hl $Hphase]
    -- prevoteCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · unfold candPhase
      icases Hphase with (⟨%Hpa, %γp', #Hpb'⟩ | ⟨%Hpnil, Hrest⟩)
      · obtain ⟨rfl, Hst0, rfl⟩ := Hpa
        ileft
        iapply bag_clause' γp' pch' (pvP γ (s0.term + 1)) _ _ $$ Hpb'
        inext
        iintro %v Hv
        unfold pvP
        icases Hv with ⟨%rp, Hrp, Hterm⟩
        wp_auto
        wp_if_destruct
        · -- a newer term: step down
          have hgt : s0.term + 1 < uint.nat rp.Term' := by word
          icases Hterm with (%Heq | #Hok)
          · exfalso; omega
          icases mainOwnAt_split r γ rc i s stCandidate $$ Hm with
            ⟨%cfg', %ccfg', %cidx', %li', Hcfgs, -, -, Hst, Hm⟩
          wp_apply (wp_setState r γ rc i stCandidate (W32 0) s) $$ [Hst Htok] with ⟨Hst, -, Htok⟩
          · iframe; iframe #
            isplitr
            · ipureintro; left; rfl
            iapply obsArg_follower' γ i s
          ihave Hm := Hm $$ %(W32 0) [] Hcfgs Hst
          · ipureintro; left; decide
          icases mainOwnAt_term r γ rc i s (W32 0) $$ Hm with ⟨%sst, %g, HownS, Hsrv, Hpw, Hm⟩
          wp_apply (wp_setCurrentTerm r γ rc i s sst g rp.Term' (.set (uint.nat rp.Term'))) $$ [HownS Hsrv Hpw]
              with ⟨Hsrv, Hpw, -, HownS, -⟩
          · iframe; iframe #
            isplitl []
            · simp only [tpRes]; iframe #
            · ipureintro; left; exact ⟨rfl, by omega⟩
          ihave Hm := Hm $$ %rp.Term' [] [] HownS Hsrv Hpw
          · ipureintro; decide
          · ipureintro; omega
          wp_for_post
          wp_apply (wp_cft_Store wp_BoolStore r) $$ [Hcft]
          · iexact Hcft
          iapply HΦ; iframe; iapply mainOwnAt_mainOwn (st := W32 0) (h := by decide) $$ Hm
        generalize rp.Granted' = gr
        wp_join iprop(∃ pg' pr' : w64, preVoteGrantedVotes_ptr ↦ pg' ∗ preVoteRefusedVotes_ptr ↦ pr')
          with [preVoteGrantedVotes preVoteRefusedVotes]
          as ⟨%pg', %pr', preVoteGrantedVotes, preVoteRefusedVotes⟩
        wp_if_destruct
        · -- the pre-vote is won: the election
          wp_apply wp_randomTimeout with %tch' Htch'
          -- (fork fix 02f88d5) the quorum of the latest configuration, the one `electSelf` asks
          icases mainOwnAt_split r γ rc i s stCandidate $$ Hm with
            ⟨%cfg2, %ccfg2, %cidx2, %li2, Hcfgs, #Hcfg2, %Hli2, Hst, Hm⟩
          icases cfgAtIs_srvsV γ s.log _ cfg2 hcv Hli2 $$ Hcfg2 with ⟨%ss2, #Hss2, %Hsv2⟩
          obtain ⟨Hsok2, Hvs2⟩ := Hsv2
          wp_apply (wp_quorumSize r ccfg2 cfg2 cidx2 li2 ss2 (DFrac.own 1) DFrac.discard) $$ [Hcfgs Hss2]
            with ⟨Hcfgs, -⟩
          · iframe; iframe #; ipureintro; have := Hsok2.2.1; omega
          ihave Hm := Hm $$ %stCandidate [] Hcfgs Hst
          · ipureintro; right; rfl
          have hvb2 : (srvVoters ss2).length < 2 ^ 32 :=
            Nat.lt_of_le_of_lt (srvVoters_length_le ss2) Hsok2.2.1
          wp_apply (wp_electSelf r γ rc i s) $$ [Hm Htok]
            as %vch' ⟨%γv, %γc, %s2, Hm, %Hs2, #Hcand, Hpub, #Hlp, Hc1, Hc2, #Hvb, Htok⟩
          · iframe; iframe #
          obtain ⟨hs2t, hs2l, -⟩ := Hs2
          wp_if_destruct <;>
            (wp_for_post
             iframe
             iexists s2, stCandidate, vch', chan.nil, tch', _, _, _, W64 0, s.log,
               W64 ((srvVoters ss2).length / 2 + 1 : Nat)
             iframe
             isplitr; · ipureintro; rw [Hvs2]; exact ⟨by word, hvb2⟩
             iright
             isplitr; · ipureintro; rfl
             try unfold candPhase
             rw [hs2t, hs2l]
             iright
             isplitr; · ipureintro; rfl
             iexists γv, γc, [], s.log
             iframe #
             isplitr; · iapply voteTally_nil
             isplitl [Hpub Hc1 Hc2]; · ileft; iframe; ipureintro; rfl
             ipureintro; exact ⟨by simp, by simp, by simp, rfl⟩)
        · wp_if_destruct <;>
            (wp_for_post
             iframe
             iexists s, stCandidate, chan.nil, pch', _, _, _, _, W64 0, Lq, vn
             iframe
             isplitr; · ipureintro; exact Hvn
             iright
             isplitr; · ipureintro; rfl
             try unfold candPhase
             ileft
             isplitr; · ipureintro; exact ⟨rfl, Hst0, rfl⟩
             iexists γp'; iexact Hpb')
      · iright; iapply chan.nilClausePre_recv Loc _ _ Hpnil
    -- voteCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · try unfold candPhase
      icases Hphase with (⟨%Hpa, %γp', #Hpb'⟩ | ⟨%Hpnil, %γv, %γc, %G, %L, #Hvb, Htally, #Hcand, #Hlp, Hcnd, %Hg⟩)
      · obtain ⟨Hvnil, -, -⟩ := Hpa
        iright; iapply chan.nilClausePre_recv Loc _ _ Hvnil
      ileft
      iapply bag_clause' γc vch (voteP γ i s.term (cfgOfC γ.cv L) γv) _ _ $$ Hvb
      inext
      iintro %v Hv
      unfold voteP
      icases Hv with ⟨%rp, %j, Hrp, Htokj, %Hj, #Hto, Hgr⟩
      wp_auto
      icases mainOwnAt_srv r γ rc i s stCandidate $$ Hm with ⟨Hsrv, Hm⟩
      iapply wp_ncfupd _ _ rfl
      iintro Hnc
      ihave H2 := srvOwn_facts_R γ rc i gd_top s $$ [$HInv $Hdur $Hsrv]
      imod H2 $$ Hnc with ⟨Hnc, Hsrv, -, %Hsf⟩
      iframe Hnc
      imodintro
      have hs : s.term < 2 ^ 62 := Hsf.2.2.2.2.2.1
      wp_apply (wp_getCurrentTerm.1 r γ rc i s) $$ [Hsrv] with Hsrv
      · iframe; iframe #
      ihave Hm := Hm $$ Hsrv
      wp_if_destruct
      · -- a newer term: step down
        have hgt : s.term < uint.nat rp.Term' := by word
        icases mainOwnAt_split r γ rc i s stCandidate $$ Hm with
          ⟨%cfg', %ccfg', %cidx', %li', Hcfgs, -, -, Hst, Hm⟩
        wp_apply (wp_setState r γ rc i stCandidate (W32 0) s) $$ [Hst Htok] with ⟨Hst, -, Htok⟩
        · iframe; iframe #
          isplitr
          · ipureintro; left; rfl
          iapply obsArg_follower' γ i s
        ihave Hm := Hm $$ %(W32 0) [] Hcfgs Hst
        · ipureintro; left; decide
        icases mainOwnAt_term r γ rc i s (W32 0) $$ Hm with ⟨%sst, %g, HownS, Hsrv, Hpw, Hm⟩
        wp_apply (wp_setCurrentTerm r γ rc i s sst g rp.Term' (.set (uint.nat rp.Term'))) $$ [HownS Hsrv Hpw]
            with ⟨Hsrv, Hpw, -, HownS, -⟩
        · iframe; iframe #
          isplitl []
          · simp only [tpRes]; iframe #
          · ipureintro; left; exact ⟨rfl, by omega⟩
        ihave Hm := Hm $$ %rp.Term' [] [] HownS Hsrv Hpw
        · ipureintro; decide
        · ipureintro; omega
        wp_for_post
        wp_apply (wp_cft_Store wp_BoolStore r) $$ [Hcft]
        · iexact Hcft
        iapply HΦ; iframe; iapply mainOwnAt_mainOwn (st := W32 0) (h := by decide) $$ Hm
      -- count the vote
      generalize hgr : rp.Granted' = gr
      wp_join iprop(∃ (g' : w64) (G' : List SID), grantedVotes_ptr ↦ g' ∗
          voteTally γ i s.term γv G' ∗ ⌜uint.nat g' = G'.length ∧ G'.length ≤ γ.srvs.length ∧
            (∀ j ∈ G', j ∈ cfgOfC γ.cv L)⌝)
        with [grantedVotes Htally Htokj Hgr]
        as ⟨%g', %G', grantedVotes, Htally, %Hg'⟩
      · iexists g, G
        iframe
        ipureintro; exact ⟨Hg.1, Hg.2.1, Hg.2.2.1⟩
      · icases Hgr with (%Hf | #Hv)
        · exact absurd Hf (by decide)
        ihave Htally := voteTally_add γ i s.term γv G j (mem_cfgOfC_srvs γ hcv L j Hj) $$ [Htally Htokj Hv]
        · iframe; iframe #
        icases voteTally_facts γ i s.term γv (j :: G) $$ Htally with ⟨Htally, %HG⟩
        have hlen := nodup_len_le HG.1 HG.2
        have hsub : ∀ x ∈ j :: G, x ∈ cfgOfC γ.cv L := by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact Hj
          · exact Hg.2.2.1 x hx
        have hlenL := nodup_len_le HG.1 hsub
        rw [Hg.2.2.2] at hlenL
        iexists _, (j :: G)
        iframe
        ipureintro
        refine ⟨?_, hlen, ?_⟩
        · simp only [List.length_cons] at hlenL ⊢
          have := Hg.1; have := Hvn.2; word
        · intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact Hj
          · exact Hg.2.2.1 x hx
      wp_if_destruct
      · -- a quorum: become the leader
        icases voteTally_votes γ i s.term γv G' $$ Htally with ⟨Hvotes, %HG⟩
        have hLq : L = Lq := Hg.2.2.2
        have hq : (cfgOfC γ.cv L).length < 2 * G'.length := by
          rw [hLq]; have := Hg'.1; have := Hvn.1; have := Hvn.2; word
        have hQ : isQuorumOf (cfgOfC γ.cv L) G' := ⟨HG.1, Hg'.2.2, hq⟩
        icases Hcnd with (⟨%HLs, Hpub, Hc1, Hc2⟩ | ⟨%ℓ, %hℓ, #Hl⟩)
        rotate_left
        · -- the term has another leader: no quorum of votes for `i` (election safety)
          imod leader_votes_agree γ ⊤ (by solve_ndisj) ℓ i s.term L.length (lastTerm L) L G' ⟨rfl, rfl⟩ hQ
            $$ [HInv Hcand Hlp Hl Hvotes] with %heq
          · iframe; iframe #
          exact absurd heq hℓ
        subst HLs
        icases mainOwnAt_lead r γ rc i s stCandidate $$ Hm with ⟨Hsrv, Hst, Hm⟩
        iapply wp_ncfupd _ _ rfl
        iintro Hnc
        ihave H3 := becomeLeader_upd_R γ rc i gd_top s G' hQ $$ [$HInv $Hdur $Hsrv $Hcand $Hvotes $Hc1 $Hc2]
        imod H3 $$ Hnc with ⟨Hnc, Hsrv, #Hlead, #Hlen0, Hcc1, Hcc2⟩
        iframe Hnc
        imodintro
        wp_apply (wp_setState r γ rc i stCandidate (W32 2) s) $$ [Hst Htok] with ⟨Hst, Hobs, Htok⟩
        · iframe; iframe #
          isplitr
          · ipureintro; right; right; rfl
          iapply (obsArg_leader' γ i s).2
          iframe #
        ihave Hm := Hm $$ %(W32 2) Hsrv Hst [Hlead Hpub Hcc1]
        · iright; iframe Hpub Hcc1; iframe #; ipureintro
          have := Hsf.2.1; have := Hsf.2.2.1; omega
        wp_apply (wp_setLeader r γ rc i) $$ [Htok] with Htok
        · iframe #; iexact Htok
        wp_for_post
        wp_apply (wp_cft_Store wp_BoolStore r) $$ [Hcft]
        · iexact Hcft
        iapply HΦ; iframe; iapply mainOwn_intro; iframe; iright; iframe Hcc2; iexact Hlen0
      wp_for_post
      iframe
      iexists s, stCandidate, _, _, _, _, _, _, g', Lq, vn
      iframe
      isplitr; · ipureintro; exact Hvn
      iright
      isplitr; · ipureintro; rfl
      try unfold candPhase
      iright
      isplitr; · ipureintro; exact Hpnil
      iexists γv, γc, G', L
      iframe
      iframe #
      ipureintro; exact ⟨Hg'.1, Hg'.2.1, Hg'.2.2, Hg.2.2.2⟩
    -- configurationChangeCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft
      iapply bag_clause' γ3 c3 (ccfP γ) _ _ $$ Hb3
      inext
      iintro %f Hf
      unfold ccfP
      icases Hf with ⟨%rq, %lv, %t, %v0, -, -, -, -, -, Hde⟩
      wp_auto
      wp_apply (deferError.respond_ccFuture wp_respond f cfgChangeQ eNL) $$ [Hde] with -
      · ileft; iframe
        unfold cfgChangeQ
        iright; ileft; iexists RaftErr.notLeader; iexact HeNL
      wp_for_post
      iframe
      iexists s, stCandidate, _, _, _, _, _, _, _, Lq, vn
      iframe
      isplitr; · ipureintro; exact Hvn
      iright
      isplitr; · ipureintro; rfl
      iexact Hphase
    -- applyCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft
      iapply bag_clause' γa applyCh (applyP γ rc i) _ _ $$ Happly
      inext
      iintro %v Hv
      unfold applyP
      icases Hv with (⟨%d, %n, %lv, %tm, Hlog, %Hty, #Hdata, -, Hresp, Hdisp, Hde, Hop⟩ |
        ⟨%lv, %tm, %sc, Hlog, %Hty, #Hdata, -, Hresp, Hdisp, #Hsc, Hde⟩)
      · wp_auto
        wp_apply (deferError.respond_logFuture wp_respond v (futQ γ rc v d n) eNL) $$ [Hde Hop] with -
        · ileft; iframe
          unfold futQ
          ileft; iframe; ileft; iframe #
        wp_for_post
        iframe
        iexists s, stCandidate, _, _, _, _, _, _, _, Lq, vn
        iframe
        isplitr; · ipureintro; exact Hvn
        iright
        isplitr; · ipureintro; rfl
        iexact Hphase
      ihave %HnNL := isRaftErr_nonnil RaftErr.notLeader eNL $$ HeNL
      wp_auto
      wp_apply (deferError.respond_logFuture wp_respond v (barrierQ γ rc i sc) eNL) $$ [Hde] with -
      · ileft; iframe
        unfold barrierQ
        ileft; ipureintro; exact HnNL
      wp_for_post
      iframe
      iexists s, stCandidate, _, _, _, _, _, _, _, Lq, vn
      iframe
      isplitr; · ipureintro; exact Hvn
      iright
      isplitr; · ipureintro; rfl
      iexact Hphase
    -- verifyCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft
      iapply bag_clause' γvn vchn (verifyP γ rc i vchn) _ _ $$ Hvbn
      inext
      iintro %v Hv
      ihave %HnNL := isRaftErr_nonnil RaftErr.notLeader eNL $$ HeNL
      icases mainOwnAt_registry r γ rc i s stCandidate $$ Hm with ⟨Hreg, Hm⟩
      wp_auto
      wp_apply (wp_verify_reject γ rc i vchn v eNL HnNL) $$ [Hreg Hv] with Hreg
      · iframe
      wp_for_post
      iframe
      iexists s, stCandidate, _, _, _, _, _, _, _, Lq, vn
      iframe
      isplitl [Hm Hreg]
      · iapply Hm $$ Hreg
      isplitr; · ipureintro; exact Hvn
      iright
      isplitr; · ipureintro; rfl
      iexact Hphase
    -- userRestoreCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft; iapply dead_clause' γ5 c5 _ _ $$ Hb5
    -- leadershipTransferCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft
      iapply bag_clause' γlt ltch (ltfP γ i) _ _ $$ Hltb
      inext
      iintro %f Hf
      wp_auto
      wp_apply (wp_lt_reject γ i f eNL) $$ [Hf]
      · iframe
      wp_for_post
      iframe
      iexists s, stCandidate, _, _, _, _, _, _, _, Lq, vn
      iframe
      isplitr; · ipureintro; exact Hvn
      iright
      isplitr; · ipureintro; rfl
      iexact Hphase
    -- configurationsCh (stage 3: takeSnapshot's request)
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft
      iapply bag_clause' γq cch (cfgReqP γ rc i) _ _ $$ Hcchb
      inext
      iintro %f Hf
      unfold cfgReqP
      icases Hf with ⟨%x, %m, %hx, #Hbx, ⟨%cf0, Hcf⟩, Hde⟩
      imod mainOwnAt_cfgReq r γ rc i s stCandidate m x hx $$ [$HInv $Hbx $Hm]
        with ⟨%ccfg2, %cfg2, %cidx2, %li2, %ss2, Hcfgs, #Hcfg2, #Hlat, #Hsnap, #Hdx, #Hax, #Hcx, Hm⟩
      ihave #Hcfg' := Hcfg2
      unfold cfgVal
      icases Hcfg' with ⟨#Hss2, %Hssok⟩
      unfold cfgOpt
      icases Hlat with ⟨%ls, #Hls, -⟩
      wp_auto
      wp_apply (configurations.wp_Clone wp_Clone _ ccfg2 cfg2 cidx2 li2 ss2 ls DFrac.discard
        DFrac.discard) $$ [$Hcfgs $Hss2 $Hls] as %cf ⟨Hcfgs, -, -, Hcs, %Hci⟩
      ihave Hm := Hm $$ Hcfgs
      imod ownSlice_persist $$ Hcs with #Hcs
      wp_apply (deferError.respond_cfgFuture wp_respond f (cfgReqQ γ rc i f x) interface.nil)
        $$ [Hde Hcf] with -
      · ileft; iframe
        unfold cfgReqQ
        ileft
        isplitr; · ipureintro; rfl
        iexists cf
        iframe
        iframe Hdx Hax Hcx
        iexists ss2
        rw [Hci]
        iframe Hsnap
        unfold cfgVal
        iframe Hcs
        ipureintro; exact Hssok
      wp_for_post
      iframe
      iexists s, stCandidate, _, _, _, _, _, _, _, Lq, vn
      iframe
      isplitr; · ipureintro; exact Hvn
      iright
      isplitr; · ipureintro; rfl
      iexact Hphase
    -- bootstrapCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft; iapply dead_clause' γ8 c8 _ _ $$ Hb8
    -- leaderNotifyCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft; iapply dead_clause' γ10 c10 _ _ $$ Hb10
    -- followerNotifyCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft; iapply dead_clause' γ11 c11 _ _ $$ Hb11
    -- electionTimer
    iapply BigAndL.bigAndL_cons.2; isplit
    · icases Htimer with (%Hnil | ⟨%γt, #Ht⟩)
      · iright; iapply chan.nilClausePre_recv time.Time _ _ Hnil
      ileft
      iapply bag_clause' γt tch _ _ _ $$ Ht
      inext
      iintro %v -
      wp_auto
      wp_for_post
      wp_apply (wp_cft_Store wp_BoolStore r) $$ [Hcft]
      · iexact Hcft
      iapply HΦ; iframe; iapply mainOwnAt_mainOwn (st := stCandidate) (h := by decide) $$ Hm
    -- shutdownCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft; iapply dead_clause' γ1 c1 _ _ $$ Hb1
    iapply BigAndL.bigAndL_nil.2
    itrivial
  -- no longer a candidate: the deferred store, and return
  split
  · rename_i h; exfalso; exact Hif (by rw [h])
  wp_auto
  wp_apply (wp_cft_Store wp_BoolStore r) $$ [Hcft]
  · iexact Hcft
  icases Hphase with (%Hne | ⟨%Heq, -⟩)
  · iapply HΦ; iframe; iapply mainOwnAt_mainOwn r γ rc i s st Hne.2 $$ Hm
  · exfalso; subst Heq; exact Hif rfl

end proof

end Perennial
