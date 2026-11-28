/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__leaderLoop.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).leaderLoop`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__leaderLoop
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__config
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getState
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__processRPC
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setState
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__configurationChangeChIfStable
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__appendConfigurationEntry
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__getLeadershipTransferInProgress
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCommitIndex
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setCommitIndex
public import Dsverify.Spec.github_com.hashicorp.raft.commitment__getCommitIndex
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setCommittedConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.hasVote
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__processLogs
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__dispatchLogs
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__checkLeaderLease
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__verifyLeader_
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__pickServer
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLeadershipTransferInProgress
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__leadershipTransfer_
public import Dsverify.Spec.github_com.hashicorp.raft.followerReplication__cleanNotify
public import Dsverify.Spec.github_com.hashicorp.raft.deferError__respond
public import Dsverify.Proof.github_com.hashicorp.raft.DeferRespond
public import Dsverify.Proof.github_com.hashicorp.raft.leader.VerifyCase
public import Dsverify.Proof.github_com.hashicorp.raft.leader.Futures
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Snap
public import Dsverify.Proof.github_com.hashicorp.raft.main.CfgReq
public import Dsverify.Proof.github_com.hashicorp.raft.leader.MainCfg
public import Dsverify.Proof.github_com.hashicorp.raft.leader.Ccf
public import Spec.fmt.Errorf
public import Perennial.Proof.fmt.VisitModel
public import Perennial.Spec.time.After
public import Perennial.Spec.fmt.Errorf

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft
open proto gprot

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A select case receiving from a bag channel: its handler runs with the bag's predicate. -/
theorem bag_recv_clause {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] [Pos.Countable V]
    {t : go.GoType} [IntoValTyped (GF := GF) V t]
    (ch : Loc) (γc : ChanNames) (P : V → IProp GF) (h : Expr) (Ψ : val → IProp GF) :
    £ 1 ∗ £ 1 ∗ isChanBag γc ch P ∗ ▷ (∀ v, P v -∗ WP (App h (Val (PairV #v #true))) {{ Ψ }}) ⊢
      chan.blockingClausePre (.CommClause (.RecvCase t (Val #ch)) h) Ψ := by
  iintro ⟨Hl1, Hl2, #Hb, HΦ⟩
  simp only [chan.blockingClausePre]
  iexists V, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
  isplitr; · ipureintro; rfl
  isplitr; · iapply is_bag_is_chan γc ch P $$ Hb
  iapply bag_recv_au γc ch P (fun v ok => iprop(WP (App h (Val (PairV #v #ok))) {{ Ψ }}))
    $$ [Hl1 Hl2] Hb HΦ
  iframe

/-- A nonblocking receive from a bag channel. -/
theorem bag_nb_recv_au {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] [Pos.Countable V]
    (γc : ChanNames) (ch : Loc) (P : V → IProp GF) (Φ : V → Bool → IProp GF) :
    ⊢ isChanBag γc ch P -∗ (∀ v, P v -∗ Φ v true) -∗ nonblockingRecvAu γc V Φ iprop(True) := by
  rw [isChanBag_unseal]; unfold isChanBagDef nonblockingRecvAu nonblockingRecvAuInner
  iintro ⟨#Hch, #Hinv⟩ HΦ
  isplit
  · iapply ncfupd_of_fupd
    iinv Hinv with Hi Hclose
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    unfold chanBagInv
    icases Hi with ⟨%st, Hoc0, Hi⟩
    iexists st
    iframe Hoc0
    rcases st with (_ | ⟨v0, buff'⟩) | _ | v | _ | _ | _ | _
    all_goals dsimp only
    case Buffered.cons =>
      iintro Hoc
      icases BigSepL.bigSepL_cons.1 $$ Hi with ⟨HP, Hi⟩
      imod Hmask with -
      imod Hclose $$ [Hoc Hi] with -
      · inext; iexists .Buffered buff'; iframe
      imodintro
      iapply HΦ $$ HP
    case SndPending =>
      iintro Hoc
      imod Hmask with -
      imod Hclose $$ [Hoc] with -
      · inext; iexists .RcvCommit; iframe
      imodintro
      iapply HΦ $$ Hi
    all_goals first | itrivial | (iexfalso; iexact Hi)
  · itrivial

/-- A select case receiving from a channel that is never sent on. -/
theorem dead_recv_clause {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] [Pos.Countable V]
    {t : go.GoType} [IntoValTyped (GF := GF) V t]
    (ch : Loc) (γc : ChanNames) (h : Expr) (Ψ : val → IProp GF) :
    £ 1 ∗ £ 1 ∗ isChanBag (V := V) γc ch (fun _ => iprop(False)) ⊢
      chan.blockingClausePre (.CommClause (.RecvCase t (Val #ch)) h) Ψ := by
  iintro ⟨Hl1, Hl2, #Hb⟩
  iapply bag_recv_clause ch γc _ h Ψ
  iframe; iframe #
  inext; iintro %v Hf; iexfalso; iexact Hf

variable [package_sem : github_com.hashicorp.raft.Assumptions]

theorem ml_mainOwnAt_state (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (st : w32) :
    mainOwnAt r γ rc i s st ⊢ ghostVar rc.names.state (1 : Qp).half st ∗
      (ghostVar rc.names.state (1 : Qp).half st -∗ mainOwnAt r γ rc i s st) := by
  unfold mainOwnAt
  iintro ⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %c, H1, H2, H3, H4, H5, Hst, H7⟩
  iframe Hst
  iintro Hst
  iexists a, sst, cfg, ccfg, cidx, li, lch, γl, bs, c
  iframe

/-- (stage 2) The leader loop's deferred functions (`defer func() { close(leftLeaderLoop) }()`,
one per leadership transfer started): the chain stored at `defer` runs safely. -/
def deferOk (defer : Loc) : IProp GF :=
  iprop(∃ f : GoFunc, defer ↦ f ∗ WP (App (Val #f) (Val #())) {{ v, ⌜v = #()⌝ }})


variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

theorem sorted_lt (fs : List InflightItem) (h : (fs.map InflightItem.k).Pairwise (· < ·))
    (t u : Nat) (x y : InflightItem) (ht : fs[t]? = some x) (hu : fs[u]? = some y) (htu : t < u) :
    x.k < y.k := by
  have htl : t < fs.length := (List.getElem?_eq_some_iff.mp ht).1
  have hul : u < fs.length := (List.getElem?_eq_some_iff.mp hu).1
  have := List.Pairwise.rel_getElem_of_lt (i := t) (j := u) (by simpa using htl) (by simpa using hul) h htu
  simp only [List.getElem_map] at this
  rw [(List.getElem?_eq_some_iff.mp ht).2, (List.getElem?_eq_some_iff.mp hu).2] at this
  exact this

/-- The commit step's group (the inflight prefix of indexes `≤ c`, of length `k`): an index past
`c` that is inflight is in the rest. -/
theorem commit_drop_cover (fs : List InflightItem) (k c : Nat)
    (hkc : ∀ t x, t < k → fs[t]? = some x → x.k ≤ c) (x' : Nat) (hx' : c < x')
    (hin : x' ∈ fs.map InflightItem.k) : x' ∈ (fs.drop k).map InflightItem.k := by
  obtain ⟨t, ht⟩ := List.mem_iff_getElem?.mp hin
  rw [List.getElem?_map] at ht
  cases hft : fs[t]? with
  | none => rw [hft] at ht; cases ht
  | some y =>
    rw [hft] at ht; simp only [Option.map_some, Option.some.injEq] at ht
    by_cases htk : t < k
    · have := hkc t y htk hft; omega
    · rw [List.mem_iff_getElem?]
      refine ⟨t - k, ?_⟩
      rw [List.getElem?_map, List.getElem?_drop, show k + (t - k) = t by omega, hft]
      simp [ht]

/-- The commit step's group: if `c` is inflight, the group is not empty and its last index is at
least `c` (inflight indexes increase; the group stops at the first index past `c`). -/
theorem commit_in_group (fs : List InflightItem) (hs : (fs.map InflightItem.k).Pairwise (· < ·))
    (k c : Nat) (hkc : ∀ t x, t < k → fs[t]? = some x → x.k ≤ c)
    (hbrk : ∀ x, fs[k]? = some x → c < x.k) (hin : c ∈ fs.map InflightItem.k) :
    0 < k ∧ ∀ y, fs[k - 1]? = some y → c ≤ y.k := by
  obtain ⟨t, ht⟩ := List.mem_iff_getElem?.mp hin
  rw [List.getElem?_map] at ht
  cases hft : fs[t]? with
  | none => rw [hft] at ht; cases ht
  | some x =>
    rw [hft] at ht; simp only [Option.map_some, Option.some.injEq] at ht
    have htk : t < k := by
      rcases Nat.lt_or_ge t k with hn | hn
      · exact hn
      exfalso
      have hlt : k < fs.length := by
        have := (List.getElem?_eq_some_iff.mp hft).1; omega
      obtain ⟨z, hz⟩ : ∃ z, fs[k]? = some z := ⟨fs[k], List.getElem?_eq_getElem hlt⟩
      have hcz := hbrk z hz
      rcases Nat.lt_or_eq_of_le hn with h | h
      · have := sorted_lt fs hs k t z x hz hft h; omega
      · subst h; rw [hz] at hft; cases hft; omega
    refine ⟨by omega, fun y hy => ?_⟩
    rcases Nat.lt_or_eq_of_le (show t ≤ k - 1 by omega) with h | h
    · have := sorted_lt fs hs t (k - 1) x y hft hy h; omega
    · subst h; rw [hy] at hft; cases hft; omega

/-- The leader's commit step (`setCommitIndex(commitment.getCommitIndex())`): publish and learn the
commitment's commit index `c` (`learnCommitLeader`, which raises the publications' bound to
`max m c`), then store it (`setCidx_upd`). -/
theorem commit_learn (γ : GNames) (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (c c0 m : Nat) :
    gprot.Inv (GF := GF) γ ∗ srvOwn γ i s ∗ durView γ i (1 : Qp).half s.dur.1 ∗ leaderIs γ s.term i ∗
      (⌜c = 0⌝ ∨ ∃ k p, ⌜c ≤ k⌝ ∗ commitIs γ s.term k p) ∗ cidxCouple γ i c0 ∗ pubOwn γ i s.term m ⊢ |={E}=>
      ∃ s1 : SState, srvOwn γ i s1 ∗ durView γ i (1 : Qp).half s1.dur.1 ∗ cidxCouple γ i c ∗
        pubOwn γ i s.term (Max.max m c) ∗ (⌜c = 0⌝ ∨ pubIs γ s.term c) ∗
        ⌜s1.term = s.term ∧ s1.log = s.log ∧ s1.vterm = s.vterm ∧ s1.vcand = s.vcand ∧
          s.dur.1 ≤ s1.dur.1 ∧ c ≤ s1.dur.1 ∧ s1.cidx = c⌝ := by
  iintro ⟨#HI, Hs, Hd, #Hl, Hc, Hcc, Hpo⟩
  icases Hc with (%Hc | #Hc)
  · subst Hc
    imod gprot.cidxCouple_agree γ E hE i s c0 $$ [Hs Hcc] with ⟨Hs, Hcc, %Hc0⟩
    · iframe; iframe #
    subst Hc0
    imod gprot.setCidx_upd γ E hE i s 0 (Nat.zero_le _) $$ [Hs Hcc] with ⟨Hs, Hcc⟩
    · iframe; iframe #
    iexists { s with cidx := 0 }
    rw [Nat.max_zero]
    iframe
    isplitr; · ileft; ipureintro; rfl
    ipureintro; exact ⟨rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.zero_le _, rfl⟩
  · icases Hc with ⟨%k, %p, %hck, #Hc⟩
    imod gprot.learnCommitLeader γ E hE i s c k p m hck $$ [Hs Hd Hpo] with ⟨%d, Hs, Hd, -, Hpo, #Hpub, %Hdd⟩
    · iframe; iframe #
    imod gprot.cidxCouple_agree γ E hE i { s with dur := d } c0 $$ [Hs Hcc] with ⟨Hs, Hcc, %Hc0⟩
    · iframe; iframe #
    subst Hc0
    imod gprot.setCidx_upd γ E hE i { s with dur := d } c (by simp only; omega) $$ [Hs Hcc]
      with ⟨Hs, Hcc⟩
    · iframe; iframe #
    iexists { s with dur := d, cidx := c }
    iframe
    isplitr; · iright; iexact Hpub
    ipureintro
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩ <;> simp only <;> omega

/-- (hub L1) `configurationChangeChIfStable`'s result gives back `mainOwnAt` (the select's other cases). -/
theorem cch_mainOwnAt (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (ch : Loc)
    (B C : IProp GF) :
    ((⌜ch = chan.nil⌝ ∗ mainOwnAt r γ rc i s stLeader) ∨ (mainOwnAtSt r γ rc i s ∗ B ∗ C)) ⊢
      mainOwnAt r γ rc i s stLeader := by
  iintro (⟨-, H⟩ | ⟨H, -, -⟩)
  · iexact H
  · iapply mainOwnAtSt_mainOwnAt $$ H

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

set_option maxHeartbeats 8000000 in
theorem github_com.hashicorp.raft.Raft.leaderLoop.wp_proof
    (wp_config : github_com.hashicorp.raft.Raft.config.spec (GF := GF) (hG := hG))
    (wp_After : time.After.spec (GF := GF) (hG := hG))
    (wp_getState : github_com.hashicorp.raft.raftState.getState.spec (GF := GF) (hG := hG))
    (wp_processRPC : github_com.hashicorp.raft.Raft.processRPC.spec (GF := GF) (hG := hG))
    (wp_setState : github_com.hashicorp.raft.Raft.setState.spec (GF := GF) (hG := hG))
    (wp_configurationChangeChIfStable :
      github_com.hashicorp.raft.Raft.configurationChangeChIfStable.spec (GF := GF) (hG := hG))
    (wp_getLeadershipTransferInProgress :
      github_com.hashicorp.raft.Raft.getLeadershipTransferInProgress.spec (GF := GF) (hG := hG))
    (wp_setLeadershipTransferInProgress :
      github_com.hashicorp.raft.Raft.setLeadershipTransferInProgress.spec (GF := GF) (hG := hG))
    (wp_getCommitIndex : github_com.hashicorp.raft.raftState.getCommitIndex.spec (GF := GF) (hG := hG))
    (wp_setCommitIndex : github_com.hashicorp.raft.raftState.setCommitIndex.spec (GF := GF) (hG := hG))
    (wp_cmGetCommitIndex : github_com.hashicorp.raft.commitment.getCommitIndex.spec (GF := GF) (hG := hG))
    (wp_setCommittedConfiguration :
      github_com.hashicorp.raft.Raft.setCommittedConfiguration.spec (GF := GF) (hG := hG))
    (wp_hasVote : github_com.hashicorp.raft.hasVote.spec (GF := GF) (hG := hG))
    (wp_processLogs : github_com.hashicorp.raft.Raft.processLogs.spec (GF := GF) (hG := hG))
    (wp_dispatchLogs : github_com.hashicorp.raft.Raft.dispatchLogs.spec (GF := GF) (hG := hG))
    (wp_checkLeaderLease : github_com.hashicorp.raft.Raft.checkLeaderLease.spec (GF := GF) (hG := hG))
    (wp_verifyLeader : github_com.hashicorp.raft.Raft.verifyLeader.spec (GF := GF) (hG := hG))
    (wp_pickServer : github_com.hashicorp.raft.Raft.pickServer.spec (GF := GF) (hG := hG))
    (wp_leadershipTransfer : github_com.hashicorp.raft.Raft.leadershipTransfer.spec (GF := GF) (hG := hG))
    (wp_cleanNotify : github_com.hashicorp.raft.followerReplication.cleanNotify.spec (GF := GF) (hG := hG))
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG))
    (wp_Clone : github_com.hashicorp.raft.Configuration.Clone.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_appendConfigurationEntry :
      github_com.hashicorp.raft.Raft.appendConfigurationEntry.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.leaderLoop.spec (GF := GF) (hG := hG) :=
  fun r γ rc i s tid => by
  wp_start as ⟨#Hr, Hm, Hl, Htok, ⟨%n0v, #Hn0v, %Hn0vl⟩⟩
  ihave ⟨#HInv, #Hvoter⟩ := isRaft_proto r γ rc i $$ Hr
  ihave ⟨%eNL, #HeNL⟩ := isRaftErr_of_init (GF := GF) RaftErr.notLeader $$ Hpkg
  ihave #HgNL0 := isRaftErr_global RaftErr.notLeader eNL $$ HeNL
  ihave #HgNL : (globalAddr ErrNotLeader ↦□ eNL : IProp GF) $$ []
  · have e : RaftErr.notLeader.var = ErrNotLeader := rfl
    rw [← e]; iexact HgNL0
  ihave %HeNLne := isRaftErr_nonnil RaftErr.notLeader eNL $$ HeNL
  ihave ⟨%eTP, #HeTP⟩ := isRaftErr_of_init (GF := GF) RaftErr.leadershipTransferInProgress $$ Hpkg
  ihave #HgTP0 := isRaftErr_global RaftErr.leadershipTransferInProgress eTP $$ HeTP
  ihave #HgTP : (globalAddr ErrLeadershipTransferInProgress ↦□ eTP : IProp GF) $$ []
  · have e : RaftErr.leadershipTransferInProgress.var = ErrLeadershipTransferInProgress := rfl
    rw [← e]; iexact HgTP0
  ihave %HeTPne := isRaftErr_nonnil RaftErr.leadershipTransferInProgress eTP $$ HeTP
  wp_apply wp_with_defer as %defer Hdefer
  ihave Hdefer : deferOk defer $$ [Hdefer]
  · unfold deferOk; iexists _; iframe
    wp_auto; ipureintro; rfl
  wp_apply (wp_config r γ rc i) $$ [$Hr] as %cfgv %Hcfgok
  ihave #HtimeI : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_apply (time.After.spec_pkgInit wp_After _) $$ [$HtimeI] as %lc %γlc #Hlease
  ipersist r
  ihave HI : (∃ (s' : SState) (st : w32) (lc : Loc) (γlc : ChanNames) (sdb : Bool),
      "Hm" ∷ mainOwnAt r γ rc i s' st ∗
      "%Hst" ∷ ⌜(st ≠ stLeader ∨ s'.term = s.term) ∧ (sdb = true → st ≠ stLeader)⌝ ∗
      "Hl" ∷ (∃ L : RLog, leaderOwnC r γ rc i s.term L ∗
        ⌜st = stLeader → L = s'.log ∧ n0v < s'.log.length⌝) ∗
      "Htok" ∷ rtok tid ∗
      "stepDown" ∷ stepDown_ptr ↦ sdb ∗
      "lease" ∷ lease_ptr ↦ lc ∗ "#Hlease" ∷ isChanBag γlc lc (fun _ => iprop(True)) ∗
      "Hdefer" ∷ deferOk defer : IProp GF)
    $$ [Hm Hl Htok stepDown lease Hdefer]
  · iexists s, stLeader, lc, γlc, false; iframe; iframe #
    isplitr; · ipureintro; exact ⟨Or.inr rfl, by simp⟩
    iexists s.log; iframe; ipureintro; intro _; exact ⟨rfl, Hn0vl⟩
  ihave #Hcells := isRaft_cells r γ rc i $$ Hr
  unfold raftCells
  icases Hcells with ⟨#HtermC, #HcidxC, #HlogC, #HstC, #HappC, -, -⟩
  imod gprot.isSrv_mem γ ⊤ (by solve_ndisj) i $$ [] with %Hivoter
  · iframe #
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨-, #HlocalID, -, -, -, -⟩
  ihave #Hifs := isRaft_ifaces r γ rc i $$ Hr
  unfold raftIfaces
  icases Hifs with ⟨%logsI, %stableI, %snapsI, %transI, %fsmI, %rpcCh, %eof, -, -, -, -, -, -, -, -, -,
    #Htrans, -, #HrpcF, -⟩
  unfold isTransport
  icases Htrans with ⟨#HrpcCh, -⟩
  unfold isRpcChan
  icases HrpcCh with ⟨%γrpc, #HrpcBag⟩
  ihave #Hchans := isRaft_chans r γ rc i $$ Hr
  unfold raftChans deadField deadChan
  icases Hchans with ⟨⟨%applyCh, #HapplyF, %γap, #HapplyBag⟩, ⟨%vch, #HvchF, %γv, #HvBag⟩,
    ⟨%ltCh, #HltF, %γlt, #HltBag⟩, ⟨%fsmCh, #HfsmF, #HfsmSpsc⟩, -, -, -,
    ⟨%csCh, #HcsF, %γcs, #HcsBag⟩, -,
    ⟨%shCh, #HshF, %γsh, #HshBag⟩, ⟨%urCh, #HurF, %γur, #HurBag⟩,
    ⟨%bsCh, #HbsF, %γbs, #HbsBag⟩,
    ⟨%lnCh, #HlnF, %γln, #HlnBag⟩, ⟨%fnCh, #HfnF, %γfn, #HfnBag⟩⟩
  wp_for HI
  ihave ⟨Hstv, Hmclose⟩ := ml_mainOwnAt_state r γ rc i s' st $$ Hm
  wp_apply (wp_getState.1 r rc st) $$ [$HstC $Hstv] as Hstv
  ihave Hm := Hmclose $$ Hstv
  wp_if_destruct
  · have hst : st = stLeader := by
      have h := go.intoVal_inj Hif
      simpa [stLeader] using h
    subst hst
    obtain ⟨Hst, Hsdb⟩ := Hst
    have hsdb : sdb = false := by
      cases sdb
      · rfl
      · exact absurd rfl (Hsdb rfl)
    subst hsdb
    rcases Hst with Hst | Hterm
    · exact absurd rfl Hst
    clear Hif
    icases Hl with ⟨%L, Hl, %HL⟩
    obtain ⟨HL', Hlen⟩ := HL rfl
    subst HL'
    icases leaderOwnM_fields r γ rc i s.term _ _ $$ Hl with ⟨%cc, %sd, %cm, Hcc, #Hccn, Hsd, #Hsdn,
      Hcm, #Hcmi, Hlclose⟩
    wp_auto
    wp_apply (lc := 2) (wp_configurationChangeChIfStable r γ rc i s' cm)
      $$ [$Hr $Hm $Hcm] as %cch ⟨Hcm, Hcch⟩
    · rw [Hterm]; iexact Hcmi
    ihave Hl := Hlclose $$ Hcc Hsd Hcm
    unfold notifyChan
    icases Hsdn with ⟨%γsd, #Hsdb⟩
    icases Hccn with ⟨%γccn, #Hccb⟩
    wp_apply_core chan.wp_select_blocking_nil
    -- rpcCh
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      iapply bag_recv_clause rpcCh γrpc (rpcP γ rc.snapP i)
      iframe; iframe #
      inext
      iintro %v Hv
      ihave Hm := cch_mainOwnAt r γ rc i s' cch _ _ $$ Hcch
      wp_auto
      wp_apply (wp_processRPC (rpc := v) (s := s') (st := stLeader) (tid := tid))
        $$ [$Hr $Hm $Hv $Htok] as ⟨%s2, %st2, Hm, Htok, Hst2⟩
      icases Hst2 with (%Hst2 | ⟨%Hc, -⟩)
      · wp_for_post
        iframe
        iexists s2, st2, lc, γlc, false
        iframe; iframe #
        rcases Hst2 with h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · isplitr; · ipureintro; exact ⟨Or.inl (by rw [h]; decide), by simp⟩
          iexists s'.log; iframe; ipureintro; intro h'; rw [h] at h'; exact absurd h' (by decide)
        · isplitr; · ipureintro; exact ⟨Or.inr (h2.trans Hterm), by simp⟩
          iexists s'.log; iframe; ipureintro; intro _; rw [h3]; exact ⟨rfl, Hlen⟩
        · isplitr; · ipureintro; exact ⟨Or.inl (by rw [h1]; decide), by simp⟩
          iexists s'.log; iframe; ipureintro; intro h'; rw [h1] at h'; exact absurd h' (by decide)
      · exfalso; exact absurd Hc.2.1 (by decide)
    -- stepDown
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      iapply bag_recv_clause sd γsd (fun _ => iprop(True))
      iframe; iframe #
      inext
      iintro %v Hv
      ihave Hm := cch_mainOwnAt r γ rc i s' cch _ _ $$ Hcch
      wp_auto
      ihave ⟨Hstv, Hmclose⟩ := ml_mainOwnAt_state' r γ rc i s' stLeader $$ Hm
      rw [show (Follower : val) = #stFollower from rfl]
      wp_apply (wp_setState r γ rc i stLeader stFollower s' tid) $$ [$Hr $Hstv $Htok] as ⟨Hstv, -, Htok⟩
      · isplitr; · ipureintro; left; rfl
        iapply ml_obsArg_follower γ i s'
      ihave Hm := Hmclose $$ %stFollower Hstv %(by decide)
      wp_for_post
      iframe
      iexists s', stFollower, lc, γlc, false
      iframe; iframe #
      isplitr; · ipureintro; exact ⟨Or.inl (by decide), by simp⟩
      iexists s'.log; iframe; ipureintro; intro h'; exact absurd h' (by decide)
    -- leadershipTransferCh
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      iapply bag_recv_clause ltCh γlt (ltfP γ i)
      iframe; iframe #
      inext
      iintro %fut Hfut
      ihave Hm := cch_mainOwnAt r γ rc i s' cch _ _ $$ Hcch
      unfold ltfP
      icases Hfut with ⟨%idp, %ap, HID, HAddr, Htarget, Hresp⟩
      wp_auto
      wp_apply (wp_getLeadershipTransferInProgress r γ rc i) $$ [$Hr] as %b -
      wp_if_destruct
      · -- start a transfer
        wp_apply (chan.wp_make1 (V := Unit)) as %llc %γll ⟨#Hllch, %Hllcap, Hllown⟩
        imod (alloc_broadcast_chan (E := ⊤) iprop(True) γll llc) $$ Hllch Hllown with Hllb
        iunfold deferOk at Hdefer
        icases Hdefer with ⟨%f, Hdf, Hwpf⟩
        wp_auto
        ipersist leftLeaderLoop
        icases ownBroadcastChan_open _ _ _ _ $$ Hllb with ⟨%γi, #Hint, Hown⟩
        ihave #HllU : ownBroadcastChan llc γll iprop(True) .Unknown $$ []
        · iapply ownBroadcastChan_close _ _ _ .Unknown γi; iframe #
        ihave Hllb : ownBroadcastChan llc γll iprop(True) .Pending $$ [Hown]
        · iapply ownBroadcastChan_close _ _ _ .Pending γi; iframe; iframe #
        ihave Hdefer : deferOk defer $$ [Hdf Hwpf Hllb]
        · unfold deferOk; iexists _; iframe Hdf
          wp_auto
          wp_apply (wp_broadcast_chan_close llc γll iprop(True)) $$ [$Hllb] as -
          · imodintro; itrivial
          wp_bind (App (Val #f) (Val #()))
          iapply wp_wand $$ Hwpf
          iintro %v' %hv'
          subst hv'
          ipureintro; rfl
        wp_apply (chan.wp_make1 (V := Unit)) as %stc %γst ⟨#Hstch, %Hstcap, Hstown⟩
        imod (alloc_broadcast_chan (E := ⊤) iprop(True) γst stc) $$ Hstch Hstown with Hstb
        icases ownBroadcastChan_open _ _ _ _ $$ Hstb with ⟨%γi2, #Hint2, Hown2⟩
        ihave #HstU : ownBroadcastChan stc γst iprop(True) .Unknown $$ []
        · iapply ownBroadcastChan_close _ _ _ .Unknown γi2; iframe #
        ihave Hstb : ownBroadcastChan stc γst iprop(True) .Pending $$ [Hown2]
        · iapply ownBroadcastChan_close _ _ _ .Pending γi2; iframe; iframe #
        wp_apply (chan.wp_make2 (V := GoInterface) (W64 1)) as %dch %γd ⟨#Hdch, %Hdcap, Hdown⟩
        · ipureintro; decide
        imod (start_bag (fun _ => iprop(True)) _ dch γd trivial) $$ Hdch Hdown with #Hdb
        ipersist stopCh
        ipersist doneCh
        ipersist future
        wp_apply wp_fork $$ [Hresp Hstb]
        · -- the transfer's other goroutine (timeout, leader loop left, or done)
          wp_auto
          wp_apply wp_with_defer as %gd Hgd
          wp_apply (wp_config r γ rc i) $$ [$Hr] as %c2 %Hc2
          ihave #HtimeI : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
          · iPkgInit
          wp_apply (lc := 2) (time.After.spec_pkgInit wp_After _) $$ [$HtimeI] as %tc %γtc #Htc
          wp_join (v := executeVal) iprop(True) at (SelectStmt _) with [Hresp Hstb Hlc1 Hlc2]
          · wp_apply_core chan.wp_select_blocking
            -- the timer
            iapply BigAndL.bigAndL_cons.2
            isplit
            · iapply bag_recv_clause tc γtc (fun _ => iprop(True))
              iframe; iframe #
              inext
              iintro %tv -
              wp_auto
              wp_apply (wp_broadcast_chan_close stc γst iprop(True)) $$ [$Hstb] as -
              · imodintro; itrivial
              ihave #HfmtS : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
              · first | iPkgInit | iframe
              wp_apply (wp_Errorf _ slice.nil [] (DFrac.own 1)) $$ [$HfmtS] as %e -
              · isplitr
                · iapply ownSlice_nil
                · iapply (_root_.Perennial.fmt.argsOk_of_argsWf (by intro ii h; simp at h))
              wp_apply (wp_ltFuture_respond fut (fun _ => iprop(True)) (interface.ok e)) $$ [Hresp] as -
              · ileft; iframe
              wp_apply (wp_bag_receive γd dch (fun _ => iprop(True))) $$ [$Hdb] as %dv -
              wp_join_done
              itrivial
            -- the leader loop left
            iapply BigAndL.bigAndL_cons.2
            isplit
            · dsimp only [chan.blockingClausePre]
              iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, llc, γll
              isplitr; · ipureintro; rfl
              isplitr; · iapply ownBroadcastChan_is_chan $$ HllU
              iapply broadcast_chan_receive _ _ _ _ .Unknown $$ HllU
              iintro -
              wp_auto
              wp_apply (wp_broadcast_chan_close stc γst iprop(True)) $$ [$Hstb] as -
              · imodintro; itrivial
              wp_apply (wp_ltFuture_respond fut (fun _ => iprop(True)) interface.nil) $$ [Hresp] as -
              · ileft; iframe
              wp_apply (wp_bag_receive γd dch (fun _ => iprop(True))) $$ [$Hdb] as %dv -
              wp_join_done
              itrivial
            -- done
            iapply BigAndL.bigAndL_cons.2
            isplit
            · iapply bag_recv_clause dch γd (fun _ => iprop(True))
              iframe; iframe #
              inext
              iintro %err -
              wp_auto
              cases err with
              | ok e =>
                wp_auto
                wp_apply (wp_ltFuture_respond fut (fun _ => iprop(True)) (GoInterface.ok e)) $$ [Hresp]
                  as -
                · ileft; iframe
                wp_join_done
                itrivial
              | nil =>
                wp_auto
                wp_apply (wp_config r γ rc i) $$ [$Hr] as %c3 %Hc3
                ihave #HtimeI : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
                · iPkgInit
                wp_apply (lc := 2) (time.After.spec_pkgInit wp_After _) $$ [$HtimeI] as %tc2 %γtc2 #Htc2
                wp_apply_core chan.wp_select_blocking
                iapply BigAndL.bigAndL_cons.2
                isplit
                · iapply bag_recv_clause tc2 γtc2 (fun _ => iprop(True))
                  iframe; iframe #
                  inext
                  iintro %tv -
                  wp_auto
                  ihave #HfmtS : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
                  · first | iPkgInit | iframe
                  wp_apply (wp_Errorf _ slice.nil [] (DFrac.own 1)) $$ [$HfmtS] as %e -
                  · isplitr
                    · iapply ownSlice_nil
                    · iapply (_root_.Perennial.fmt.argsOk_of_argsWf (by intro ii h; simp at h))
                  wp_apply (wp_ltFuture_respond fut (fun _ => iprop(True)) (interface.ok e)) $$ [Hresp]
                    as -
                  · ileft; iframe
                  wp_join_done
                  itrivial
                iapply BigAndL.bigAndL_cons.2
                isplit
                · dsimp only [chan.blockingClausePre]
                  iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, llc, γll
                  isplitr; · ipureintro; rfl
                  isplitr; · iapply ownBroadcastChan_is_chan $$ HllU
                  iapply broadcast_chan_receive _ _ _ _ .Unknown $$ HllU
                  iintro -
                  wp_auto
                  wp_apply (wp_ltFuture_respond fut (fun _ => iprop(True)) interface.nil) $$ [Hresp] as -
                  · ileft; iframe
                  wp_join_done
                  itrivial
                iapply BigAndL.bigAndL_nil.2; itrivial
            iapply BigAndL.bigAndL_nil.2; itrivial
          iintro -
          wp_auto
          wp_apply (wp_setLeadershipTransferInProgress r γ rc i false) $$ [$Hr]
          ipureintro; trivial
        icases leaderOwnM_repl r γ rc i s.term _ _ $$ Hl with ⟨%rs, %rmap, Hrs, Hrsm, #Hshared, %Hcov,
          Hlclose⟩
        wp_if_destruct
        · -- no target: the most up-to-date follower
          imod mainOwnAt_leader_cfg r γ rc i s' $$ [$HInv $Hm] with ⟨Hm, %Hl1⟩
          icases mainOwnAt_conf r γ rc i s' stLeader $$ Hm with ⟨%ccfg, %cfg, %cidx, %li, Hconf, #Hcfg,
            -, %Hli, Hmclose⟩
          iunfold cfgAtIs at Hcfg
          icases Hcfg with (⟨%h0, -⟩ | ⟨%ss, %ec, #Hcv0, -⟩)
          · exfalso; omega
          wp_apply (wp_pickServer r γ rc i s.term ccfg cfg cidx li ss rs rmap)
            $$ [$Hr $Hconf $Hcv0 $Hrs $Hrsm $Hshared] as %p ⟨Hconf, Hrs, Hrsm, Hp⟩
          ihave Hm := Hmclose $$ Hconf
          icases Hp with (%Hpn | ⟨%j, %st, Hpj, %hst⟩)
          · subst Hpn
            wp_auto
            ihave #HfmtS : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
            · first | iPkgInit | iframe
            wp_apply (wp_Errorf _ slice.nil [] (DFrac.own 1)) $$ [$HfmtS] as %e -
            · isplitr
              · iapply ownSlice_nil
              · iapply (_root_.Perennial.fmt.argsOk_of_argsWf (by intro ii h; simp at h))
            wp_apply (wp_bag_send γd dch (interface.ok e) (fun _ => iprop(True))) $$ [$Hdb]
            ihave Hl := Hlclose $$ Hrs Hrsm
            wp_for_post
            iframe
            iexists s', stLeader, lc, γlc, false; iframe; iframe #
            isplitr; · ipureintro; exact ⟨Or.inr (Hterm), by simp⟩
            iexists s'.log; iframe; ipureintro; intro _; exact ⟨rfl, Hlen⟩
          · ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hpj
            iStructNamed Hpj
            ipersist ID
            ipersist Address
            wp_if_destruct
            · exact absurd rfl Hpnn
            · wp_apply (wp_map_lookup2 ServerID.ty (go.GoType.PointerType followerReplication.ty) rs rmap
                j (DFrac.own 1)) $$ [$Hrsm] as Hrsm
              rw [hst.1]
              simp only [Option.getD_some, Option.isSome_some]
              wp_auto
              wp_apply (wp_setLeadershipTransferInProgress r γ rc i true) $$ [$Hr]
              ihave #Hsh := BigSepM.bigSepM_lookup hst.1 $$ Hshared
              wp_bind (Fork _)
              iapply wp_fork_rtok
              · inext
                iintro %t Htk
                wp_apply (wp_leadershipTransfer r γ rc i s.term j j st stc dch γst γd iprop(True) t)
                  $$ [$Hr $Hsh $HstU $Hdb $Htk] as Htk
                iframe; ipureintro; simp
              inext
              wp_auto
              ihave Hl := Hlclose $$ Hrs Hrsm
              wp_for_post
              iframe
              iexists s', stLeader, lc, γlc, false; iframe; iframe #
              isplitr; · ipureintro; exact ⟨Or.inr (Hterm), by simp⟩
              iexists s'.log; iframe; ipureintro; intro _; exact ⟨rfl, Hlen⟩
        · -- a target given (any server `j ≠ i`; stage 4: maybe without a replication goroutine)
          icases Htarget with (⟨%h1, %h2⟩ | ⟨%j, #Hidp, #Hap, #Hjv, %Hji⟩)
          · exact absurd h1 Hif
          wp_auto
          wp_apply (wp_map_lookup2 ServerID.ty (go.GoType.PointerType followerReplication.ty) rs rmap
            j (DFrac.own 1)) $$ [$Hrsm] as Hrsm
          cases hst : rmap !! j with
          | none =>
            simp only [Option.getD_none, Option.isSome_none]
            wp_auto
            wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
              (Val (LiteralValueV _)))
            iapply wp_slice_literal (V := GoInterface) (t := go.any)
              [interface.mkOk ServerID.ty #j]
            wp_auto
            isplitl []; · ipureintro; rfl
            iintro %asl ⟨Hasl, -⟩
            wp_auto
            -- `%s` of the `ServerID` (a named string with no methods): Perennial's `fmt.Errorf`
            ihave #HfmtS : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
            · first | iPkgInit | iframe
            wp_apply (wp_Errorf _ _ [interface.mkOk ServerID.ty #j] (DFrac.own 1)) $$ [$HfmtS $Hasl]
              as %e2 -
            · iapply _root_.Perennial.fmt.argsOk_intro (by rfl)
              simp only [_root_.Perennial.fmt.argsOkAt]
              isplitr
              · iapply _root_.Perennial.fmt.argOkAt_of_argWf
                intro ii hii
                cases hii
                refine EtcdGrove.fmt.argWf_of_argsWf
                  (_root_.Perennial.fmt.ArgsWf.cons_named_string _ _ _ ?_ ?_ ?_ ?_ _root_.Perennial.fmt.ArgsWf.nil)
                · unfold ServerID.ty; intro h; cases h
                · unfold ServerID.ty
                  simp only [_root_.Perennial.fmt.IsIntType]
                  simp only [not_or]
                  repeat' apply And.intro
                  all_goals first | (intro h; cases h) | (intro h; injection h with h1; simp at h1) | simp
                · exact go.IsUnderlying.is_underlying
                · exact _root_.Perennial.fmt.NoFmtMethods.of_methodSetIs_nil _
              · itrivial
            wp_apply (wp_bag_send γd dch (interface.ok e2) (fun _ => iprop(True))) $$ [$Hdb]
            ihave Hl := Hlclose $$ Hrs Hrsm
            wp_for_post
            iframe
            iexists s', stLeader, lc, γlc, false; iframe; iframe #
            isplitr; · ipureintro; exact ⟨Or.inr (Hterm), by simp⟩
            iexists s'.log; iframe; ipureintro; intro _; exact ⟨rfl, Hlen⟩
          | some st =>
            simp only [Option.getD_some, Option.isSome_some]
            wp_auto
            wp_apply (wp_setLeadershipTransferInProgress r γ rc i true) $$ [$Hr]
            ihave #Hsh := BigSepM.bigSepM_lookup hst $$ Hshared
            wp_bind (Fork _)
            iapply wp_fork_rtok
            · inext
              iintro %t Htk
              wp_apply (wp_leadershipTransfer r γ rc i s.term j j st stc dch γst γd iprop(True) t)
                $$ [$Hr $Hsh $HstU $Hdb $Htk] as Htk
              iframe; ipureintro; simp
            inext
            wp_auto
            ihave Hl := Hlclose $$ Hrs Hrsm
            wp_for_post
            iframe
            iexists s', stLeader, lc, γlc, false; iframe; iframe #
            isplitr; · ipureintro; exact ⟨Or.inr (Hterm), by simp⟩
            iexists s'.log; iframe; ipureintro; intro _; exact ⟨rfl, Hlen⟩

      · -- a transfer is in progress
        wp_apply (wp_ltFuture_respond fut (fun _ => iprop(True)) eTP) $$ [Hresp] as -
        · ileft; iframe
        wp_for_post
        iframe
        iexists s', stLeader, lc, γlc, false; iframe; iframe #
        isplitr; · ipureintro; exact ⟨Or.inr (Hterm), by simp⟩
        iexists s'.log; iframe; ipureintro; intro _; exact ⟨rfl, Hlen⟩
    -- commitCh
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      iapply bag_recv_clause cc γccn (fun _ => iprop(True))
      iframe; iframe #
      inext
      iintro %v Hv
      ihave Hm := cch_mainOwnAt r γ rc i s' cch _ _ $$ Hcch
      wp_auto
      iunfold mainOwnAt at Hm
      icases Hm with ⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %cp, Hsrv, Hdur, HownS, %Hvm, HlastLog,
        Hstv, Hldr0, HlogPend, Hreg, Happ, %Ha, Hprod, Hpdn, Hcomp, %Hcp, Hconf, #Hcfg, #Hccfg, %Hli, #Hcmt,
        #Hlch, #Hlchan, Hlown, %Hlcap⟩
      icases Hldr0 with (%Hc | ⟨#Hldr, ⟨%m, Hpo, %Hma⟩, Hccm, %n0m, #Hn0m, Hcix, #Hcl⟩)
      · exact absurd rfl Hc
      unfold leaderOwnM
      icases Hl with ⟨%cc', %cm', %infl, %fs, %rs, %rmap, %nt, %sd', %n0, #Hldr', #Hlen0, Hcc, #Hccn',
        Hcm, #Hcmi', Hinfl, Hinfls, Hinflc, %Hfs, Hfs, Hrs, Hrsm, Hrmap, Hnt, HNMp, Hsd, #Hsdn', %Hcov,
        %pb, #Hpb, %Hpbc⟩
      ihave %Hnn := len0Is_agree γ s'.term n0m n0 $$ [Hn0m Hlen0]
      · rw [Hterm]; iframe #
      subst Hnn
      ihave Hpo : pubOwn γ i s.term m $$ [Hpo]
      · rw [← Hterm]; iexact Hpo
      imod pb_le (γ := γ) ⊤ (by solve_ndisj) i s.term pb m $$ [Hpo] with ⟨Hpo, %Hpbm⟩
      · iframe; iframe #
      wp_apply (wp_getCommitIndex.1 r γ i s') $$ [$Hsrv $HInv $HcidxC] as Hsrv
      imod gprot.srvOwn_facts γ ⊤ (by solve_ndisj) i s' $$ [Hsrv] with ⟨Hsrv, -, %Hfacts0⟩
      · iframe; iframe #
      wp_apply (wp_cmGetCommitIndex γ i s.term cm') $$ [$Hcmi'] as %c Hc
      ihave #Hc := Hc
      ihave %Hcn0 : ⌜uint.nat c = 0 ∨ n0m < uint.nat c⌝ $$ []
      · icases Hc with (%Hc | ⟨%n0', %k, %pk, #Hn0', %Hk, -⟩)
        · ipureintro; left; rw [Hc]; rfl
        · ihave %He := len0Is_agree γ s.term n0m n0' $$ [$Hlen0 $Hn0']
          ipureintro; right; omega
      wp_apply (wp_setCommitIndex r γ i c (iprop(∃ s1 : SState, srvOwn γ i s1 ∗
          durView γ i (1 : Qp).half s1.dur.1 ∗ pubOwn γ i s.term (Max.max m (uint.nat c)) ∗
          (⌜uint.nat c = 0⌝ ∨ pubIs γ s.term (uint.nat c)) ∗
          ⌜s1.term = s'.term ∧ s1.log = s'.log ∧ s1.vterm = s'.vterm ∧ s1.vcand = s'.vcand ∧
            s'.dur.1 ≤ s1.dur.1 ∧ uint.nat c ≤ s1.dur.1 ∧ s1.cidx = uint.nat c⌝)))
        $$ [Hsrv Hdur Hpo] as ⟨%s1, Hsrv, Hdur, Hpo, #Hpubc, %Hs1⟩
      · iframe #
        iintro %c0 Hcc
        rw [← Hterm]
        imod commit_learn γ (⊤ \ ↑cidxN) (by unfold gprotN cidxN raftN; solve_ndisj) i s' (uint.nat c) c0 m
          $$ [Hsrv Hdur Hcc Hpo] with ⟨%s1, Hsrv, Hdur, Hcc, Hpo, Hpubc, %Hs1⟩
        · iframe; iframe #
          rw [Hterm]
          icases Hc with (%Hc | ⟨%n0', %k, %pk, -, %Hk, #Hc⟩)
          · ileft; ipureintro; rw [Hc]; rfl
          · iright; iexists k, pk; iframe Hc; ipureintro; exact Hk.2
        imodintro
        iframe
        ipureintro; exact Hs1
      imod gprot.srvOwn_facts γ ⊤ (by solve_ndisj) i s1 $$ [Hsrv] with ⟨Hsrv, -, %Hfacts1⟩
      · iframe; iframe #
      obtain ⟨hs1t, hs1l, hs1vt, hs1vc, hs1d, hcd, hs1c⟩ := Hs1
      have hsc63 : s'.cidx < 2 ^ 62 := by
        have := Hfacts0.2.2.1; have := Hfacts0.2.1; have := Hfacts0.2.2.2.2.2.2.1; omega
      have hli63 : uint.nat li ≤ s'.log.length := by rw [Hli.1]; exact (lastCfgIdx_spec s'.log).1
      wp_join iprop(∃ (ccfg' : Configuration) (cidx' : w64) (sdb' : Bool),
          r.[Raft, go!"configurations"] ↦ configurations.mk ccfg' cidx' cfg li ∗
          cfgAtIs γ s'.log (uint.nat cidx') ccfg' ∗ cmtIdx γ s'.term s'.log (uint.nat cidx') ∗
          (⌜cidx' ≠ li ∨ uint.nat li ≤ n0m⌝ ∨
            ∃ k p : Nat, commitIs γ s'.term k p ∗ ⌜uint.nat li ≤ k⌝) ∗
          ⌜cidx' = li ∨ (uint.nat cidx' = lastCfgIdx (s'.log.take (uint.nat li - 1)) ∧ a < uint.nat li ∧
              uint.nat c < uint.nat li)⌝ ∗
          stepDown_ptr ↦ sdb' ∗ commitIndex_ptr ↦ c ∗ srvOwn γ i s1) with [Hconf stepDown commitIndex Hsrv]
        as ⟨%ccfg', %cidx', %sdb', Hconf, #Hccfg', #Hcmt', #Hcl', %Hcfg', stepDown, commitIndex, Hsrv⟩
      · wp_if_destruct
        · -- the latest configuration becomes the committed one
          have hlic : uint.nat li ≤ uint.nat c := by word
          have hli1 : 1 ≤ uint.nat li := by word
          wp_apply (wp_setCommittedConfiguration r ccfg cfg cidx li cfg li) $$ [$Hconf] as Hconf
          ihave Hcfg2 := Hcfg
          iunfold cfgAtIs at Hcfg2
          icases Hcfg2 with (⟨%h0, -⟩ | ⟨%ss, %ec, Hcv0, %Hec⟩)
          · exfalso; omega
          iunfold cfgVal at Hcv0
          icases Hcv0 with ⟨#Hss, %Hssok⟩
          wp_apply (wp_hasVote cfg ss DFrac.discard i) $$ [$Hss] as -
          · ipureintro; exact Hssok.1
          imod cmtIdx_dur γ ⊤ (by solve_ndisj) i s1 (uint.nat li) (by omega) $$ [Hsrv]
            with ⟨Hsrv, #Hcmtl⟩
          · iframe; iframe #
          ihave #Hclc : (⌜li ≠ li ∨ uint.nat li ≤ n0m⌝ ∨
              ∃ k p : Nat, commitIs γ s'.term k p ∗ ⌜uint.nat li ≤ k⌝ : IProp GF) $$ []
          · icases Hc with (%Hc0 | ⟨%n0', %k, %pk, -, %Hk, #Hck⟩)
            · exfalso; subst Hc0; have : uint.nat (W64 0) = 0 := rfl; omega
            · iright; iexists k, pk; rw [Hterm]; iframe #; ipureintro; omega
          wp_if_destruct
          · isplitr; · ipureintro; trivial
            iexists cfg, li, false; iframe
            rw [← hs1t, ← hs1l]
            iframe #
            ipureintro; exact Or.inl rfl
          · isplitr; · ipureintro; trivial
            iexists cfg, li, true; iframe
            rw [← hs1t, ← hs1l]
            iframe #
            ipureintro; exact Or.inl rfl
        · have hcl : uint.nat c < uint.nat li := by word
          isplitr; · ipureintro; trivial
          iexists ccfg, cidx, false; iframe; iframe #
          ipureintro
          rcases Hli.2 with h | ⟨h1, h2⟩
          · left; exact h
          · right; exact ⟨h1, h2, hcl⟩
      · -- `latestIndex ≤ oldCommitIndex`: the latest configuration is the committed one
        have hle : uint.nat li ≤ s'.cidx := by word
        iexists ccfg, cidx, false; iframe; iframe #
        have hcidx : cidx = li := by
          rcases Hli.2 with h | ⟨-, h⟩
          · exact h
          · exfalso; omega
        ipureintro
        exact Or.inl hcidx
      wp_apply (wp_map_make1 (K := w64) (V := Loc) go.uint64 (go.GoType.PointerType logFuture.ty))
        as %gfm Hgfm
      wp_join iprop(∃ (k : Nat) (M : GMap w64 Loc) (lidx : w64),
          groupReady_ptr ↦ W64 k ∗ gfm ↦$ M ∗ lastIdxInGroup_ptr ↦ lidx ∗
          ⌜k ≤ fs.length ∧ (∀ t x, t < k → fs[t]? = some x → x.k ≤ uint.nat c) ∧
            (k = 0 → lidx = W64 0) ∧ (0 < k → ∃ x, fs[k - 1]? = some x ∧ uint.nat lidx = x.k) ∧
            (∀ x, fs[k]? = some x → uint.nat c < x.k)⌝ ∗
          ([∗map] key ↦ f ∈ M, ∃ e, futResp γ rc i f (uint.nat key) e ∗
            ⌜ent s1.log (uint.nat key) = some e⌝) ∗
          ([∗list] x ∈ fs.drop k, futResp γ rc i x.f x.k x.e ∗ llogIdx γ s.term x.k x.e) ∗
          commitIndex_ptr ↦ c ∗ infl ↦* fs.map InflightItem.f ∗
          r.[Raft, go!"leaderState"].[leaderState, go!"inflight"] ↦ infl ∗ srvOwn γ i s1 ∗
          groupFutures_ptr ↦ gfm)
        at next with [groupReady Hgfm lastIdxInGroup Hfs commitIndex Hinfls Hinfl Hsrv groupFutures
          commitLog i]
        as ⟨%k, %M, %lidx, groupReady, Hgfm, lastIdxInGroup, %Hk, HM, Hfs, commitIndex, Hinfls,
          Hinfl, Hsrv, groupFutures⟩
      · ihave HI2 : (∃ (k : Nat) (M : GMap w64 Loc) (lidx : w64) (cl : Loc),
            "i" ∷ i_ptr ↦ W64 k ∗ "groupReady" ∷ groupReady_ptr ↦ W64 k ∗ "Hgfm" ∷ gfm ↦$ M ∗
            "lastIdxInGroup" ∷ lastIdxInGroup_ptr ↦ lidx ∗ "commitLog" ∷ commitLog_ptr ↦ cl ∗
            "%Hk" ∷ ⌜k ≤ fs.length ∧ (∀ t x, t < k → fs[t]? = some x → x.k ≤ uint.nat c) ∧
              (k = 0 → lidx = W64 0) ∧ (0 < k → ∃ x, fs[k - 1]? = some x ∧ uint.nat lidx = x.k) ∧
              (∀ key f, M !! key = some f → ∃ t x, t < k ∧ fs[t]? = some x ∧ uint.nat key = x.k)⌝ ∗
            "HM" ∷ ([∗map] key ↦ f ∈ M, ∃ e, futResp γ rc i f (uint.nat key) e ∗
              ⌜ent s1.log (uint.nat key) = some e⌝) ∗
            "Hfs" ∷ ([∗list] x ∈ fs.drop k, futResp γ rc i x.f x.k x.e ∗ llogIdx γ s.term x.k x.e) : IProp GF)
          $$ [i groupReady Hgfm lastIdxInGroup commitLog Hfs]
        · iexists 0, ∅, (W64 0), _; iframe
          isplitr
          · ipureintro
            refine ⟨Nat.zero_le _, fun t x ht => absurd ht (Nat.not_lt_zero _), fun _ => rfl,
              fun h => absurd h (Nat.lt_irrefl _), fun key f h => by simp at h⟩
          iapply BigSepM.bigSepM_empty.2; iempintro
        wp_for HI2
        wp_if_destruct
        · have Hif' : sint.Z (W64 (k : Int)) < sint.Z infl.len := by
            first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
          obtain ⟨Hkle, Hkc, Hk0, Hkpos, HMk⟩ := Hk
          ihave %Hinfllen := ownSlice_len $$ Hinfls
          simp only [List.length_map] at Hinfllen
          have hlen63 : sint.nat infl.len < 2 ^ 63 := by word
          have hk : k < fs.length := by word
          have hk63 : k < 2 ^ 63 := by omega
          list_elem fs k as x
          rw [if_pos (show 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z infl.len from
            ⟨by word, Hif'⟩)]
          wp_apply (wp_load_slice_index infl (sint.Z (W64 k)) (fs.map InflightItem.f) (DFrac.own 1)
            x.f (by word)) $$ [$Hinfls] as Hinfls
          · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by word]; simp [Hx_lookup]
          have hdrop : fs.drop k = x :: fs.drop (k + 1) := by
            rw [List.drop_eq_getElem_cons hk]; congr; exact (List.getElem?_eq_some_iff.mp Hx_lookup).2
          rw [hdrop]
          icases Hfs with ⟨⟨Hxr, #Hxl⟩, Hfs⟩
          unfold futResp
          icases Hxr with ⟨#Hlp, Hresp, Hde⟩
          unfold logPtr logIs
          icases Hlp with ⟨%lv, #Hlv, %Hlvi, #Hd, #Hext⟩
          ihave Hlv2 := Hlv
          iStructNamed Hlv2
          wp_auto
          wp_if_destruct
          · wp_for_post
            isplitr; · ipureintro; rfl
            iexists k, M, lidx
            rw [hdrop]
            iframe
            isplitr
            · ipureintro
              refine ⟨Hkle, Hkc, Hk0, Hkpos, fun y hy => ?_⟩
              rw [Hx_lookup] at hy; cases hy
              have := Hlvi.1; word
            iframe #
            ipureintro; exact Hlvi
          · imod llogIdx_leader γ ⊤ (by solve_ndisj) i s1 x.k x.e $$ [Hsrv] with ⟨Hsrv, %Hent⟩
            · iframe; iframe #; rw [hs1t, Hterm]; iframe #
            wp_apply (wp_mapInsert go.uint64 gfm M lv.Index' x.f) $$ [$Hgfm] as Hgfm
            wp_for_post
            have hxk : uint.nat lv.Index' = x.k := Hlvi.1
            have hxc : x.k ≤ uint.nat c := by word
            have hfresh : M !! lv.Index' = none := by
              cases hM : M !! lv.Index' with
              | none => rfl
              | some f =>
                obtain ⟨t, y, ht, hy, hyk⟩ := HMk _ _ hM
                have := sorted_lt fs Hfs t k y x hy Hx_lookup ht
                omega
            iframe
            iexists (k + 1), <[lv.Index' := x.f]> M, lv.Index', x.f
            rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
            iframe
            isplitr
            · ipureintro
              refine ⟨by omega, fun t y ht hy => ?_, fun h => absurd h (Nat.succ_ne_zero _),
                fun _ => ⟨x, by simpa using Hx_lookup, hxk⟩, fun key f hkf => ?_⟩
              · rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
                · exact Hkc t y ht hy
                · subst ht; rw [Hx_lookup] at hy; cases hy; exact hxc
              · by_cases hkey : key = lv.Index'
                · subst hkey; exact ⟨k, x, Nat.lt_succ_self _, Hx_lookup, hxk⟩
                · rw [GMap.lookup_insert_ne _ _ (Ne.symm hkey)] at hkf
                  obtain ⟨t, y, ht, hy, hyk⟩ := HMk _ _ hkf
                  exact ⟨t, y, by omega, hy, hyk⟩
            iapply (BigSepM.bigSepM_insert hfresh).2
            iframe
            iexists x.e
            isplitl [Hde]
            · isplitr
              · iexists lv; iframe #; ipureintro; exact ⟨rfl, Hlvi.2⟩
              rw [hxk]; iexact Hde
            ipureintro; rw [hxk]; exact Hent
        · obtain ⟨Hkle, Hkc, Hk0, Hkpos, -⟩ := Hk
          have hnP : ¬ (sint.Z (W64 (k : Int)) < sint.Z infl.len) := by
            intro h; apply Hif; first | exact h | rw [decide_eq_true h]
          have hc : decide ((#(decide (sint.Z (W64 (k : Int)) < sint.Z infl.len)) : val) = #false) = true := by
            rw [decide_eq_false hnP]; exact decide_eq_true rfl
          try rw [if_pos hc]
          try simp only [decide_eq_false hnP, _root_.decide_true, ↓reduceIte]
          ihave %Hinfllen := ownSlice_len $$ Hinfls
          simp only [List.length_map] at Hinfllen
          isplitr; · ipureintro; trivial
          iexists k, M, lidx; iframe
          ipureintro
          refine ⟨Hkle, Hkc, Hk0, Hkpos, fun y hy => ?_⟩
          exfalso
          have := (List.getElem?_eq_some_iff.mp hy).1
          apply Hif; word
      obtain ⟨Hkle, Hkc, Hk0, Hkpos, Hkbrk⟩ := Hk
      have hcdur : uint.nat c ≤ s1.dur.1 := hcd
      wp_join iprop(∃ (a' : Nat) (infl' : GoSlice) (fs' : List InflightItem),
          monoNatAuthOwn rc.dur.applied (1 : Qp).half a' ∗ fsmProd γ rc a' ∗ ⌜a' ≤ s1.dur.1⌝ ∗
          monoNatAuthOwn rc.dur.comp 1 cp ∗
          r.[Raft, go!"leaderState"].[leaderState, go!"inflight"] ↦ infl' ∗
          infl' ↦* fs'.map InflightItem.f ∗ ownSliceCap Loc infl' (DFrac.own 1) ∗
          ⌜(fs'.map InflightItem.k).Pairwise (· < ·)⌝ ∗
          ([∗list] x ∈ fs', futResp γ rc i x.f x.k x.e ∗ llogIdx γ s.term x.k x.e) ∗
          srvOwn γ i s1 ∗ rtok tid ∗ ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) ∗
          ⌜a ≤ a' ∧ uint.nat lidx ≤ a' ∧ fs' = fs.drop k ∧ a' ≤ Max.max a (uint.nat c)⌝)
        with [Happ Hprod Hinfl Hinfls Hinflc Hfs HM Hgfm Hsrv Htok HlogPend groupReady lastIdxInGroup
          groupFutures Hcomp]
        as ⟨%a', %infl', %fs', Happ, Hprod, %Ha', Hcomp, Hinfl, Hinfls, Hinflc, %Hfs', Hfs, Hsrv, Htok,
          HlogPend, %Haa⟩
      · ihave %Hil := ownSlice_len $$ Hinfls
        simp only [List.length_map] at Hil
        have hk0 : k = 0 := by word
        subst hk0
        rw [List.drop_zero]
        iexists a, infl, fs; iframe
        ipureintro; refine ⟨by omega, Hfs, Nat.le_refl _, ?_, rfl, Nat.le_max_left _ _⟩
        rw [Hk0 rfl]; simp
      · have hk0 : k ≠ 0 := by intro h; subst h; simp at Hif
        obtain ⟨y, hy, hlidx⟩ := Hkpos (Nat.pos_of_ne_zero hk0)
        have hyc : y.k ≤ uint.nat c := Hkc (k - 1) y (by omega) hy
        wp_apply (wp_processLogs r γ rc i lidx gfm M s1 a cp tid)
          $$ [$Hr $Hsrv $Hprod $Happ $Htok $HlogPend $Hcomp HM Hgfm]
          as ⟨Hsrv, Hprod, Happ, Hcomp, Htok, HlogPend, -⟩
        · isplitr; · ipureintro; omega
          isplitr; · ipureintro; exact Hcp
          iframe
        ihave %Hil := ownSlice_len $$ Hinfls
        ihave %Hcw := ownSliceCap_wf $$ Hinflc
        simp only [List.length_map] at Hil
        have hk63 : k < 2 ^ 63 := by have : sint.nat infl.len < 2 ^ 63 := by word
                                     omega
        rw [if_pos (show 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) ≤ sint.Z infl.len ∧
          sint.Z infl.len ≤ sint.Z infl.cap from ⟨by word, by word, Hcw.2⟩)]
        wp_auto
        ihave ⟨-, Hinfls⟩ := (ownSlice_split_all (W64 k) infl (DFrac.own 1) _ ⟨by word, by word⟩).1
          $$ Hinfls
        ihave Hinflc := (ownSliceCap_slice infl (W64 k) (DFrac.own 1) ⟨by word, by word, Hcw.2⟩).1
          $$ Hinflc
        rw [show sint.nat (W64 (k : Int)) = k by word, ← List.map_drop]
        isplitr; · ipureintro; rfl
        iexists (Max.max a (uint.nat lidx)), _, fs.drop k
        iframe
        isplitr; · ipureintro; have := hs1d; omega
        ipureintro
        refine ⟨?_, by omega, by omega, rfl, by omega⟩
        rw [List.map_drop]; exact Hfs.sublist (List.drop_sublist _ _)
      obtain ⟨haa, hlidxa, hfs', ha'c⟩ := Haa
      subst hfs'
      obtain ⟨-, Hdurlen1, -⟩ := Hfacts1
      -- the publications' bound stays within what was handed to the FSM
      have hcL : uint.nat c ≤ s'.log.length := by rw [← hs1l]; omega
      have hma' : Max.max m (uint.nat c) ≤ a' := by
        rcases Hcn0 with hc0 | hcn
        · rw [hc0]; omega
        · by_cases hcp : uint.nat c ≤ pb
          · omega
          · have hin : uint.nat c ∈ fs.map InflightItem.k := Hpbc.2 _ (by omega) hcL
            obtain ⟨hk0, hy⟩ := commit_in_group fs Hfs k (uint.nat c) Hkc Hkbrk hin
            obtain ⟨y, hy1, hy2⟩ := Hkpos hk0
            have := hy y hy1
            omega
      ihave Hpbn : (⌜Max.max pb (uint.nat c) = 0⌝ ∨ pubIs γ s.term (Max.max pb (uint.nat c)) : IProp GF)
        $$ [Hpb Hpubc]
      · by_cases hcp : uint.nat c ≤ pb
        · rw [Nat.max_eq_left hcp]; iexact Hpb
        · rw [Nat.max_eq_right (by omega)]; iexact Hpubc
      ihave Hcix1 : (⌜s1.cidx ≤ n0m⌝ ∨ ∃ k p : Nat, commitIs γ s1.term k p ∗ ⌜s1.cidx ≤ k⌝ : IProp GF) $$ []
      · rw [hs1c, hs1t, Hterm]
        icases Hc with (%Hc0 | ⟨%n0', %k, %pk, #Hn0', %Hk, #Hck⟩)
        · ileft; ipureintro; rw [Hc0]; exact Nat.zero_le _
        · iright; iexists k, pk; iframe #; ipureintro; exact Hk.2
      ihave Hldr0 : (⌜stLeader ≠ stLeader⌝ ∨ leaderIs γ s1.term i ∗
          (∃ m', pubOwn γ i s1.term m' ∗ ⌜m' ≤ a'⌝) ∗ ccfgOwn γ i s1.term (lastCfgIdx s1.log) ∗
          ∃ n0 : Nat, len0Is γ s1.term n0 ∗
            (⌜s1.cidx ≤ n0⌝ ∨ ∃ k p : Nat, commitIs γ s1.term k p ∗ ⌜s1.cidx ≤ k⌝) ∗
            (⌜cidx' ≠ li ∨ uint.nat li ≤ n0⌝ ∨
              ∃ k p : Nat, commitIs γ s1.term k p ∗ ⌜uint.nat li ≤ k⌝) : IProp GF) $$ [Hpo Hccm Hcix1]
      · iright; rw [hs1l]; rw [hs1t]; iframe #
        isplitl [Hpo]; · rw [Hterm]; iexists (Max.max m (uint.nat c)); iframe; ipureintro; exact hma'
        iframe Hccm
        rw [← hs1t]; iframe
      have hcov' : inflCover (fs.drop k) (Max.max pb (uint.nat c)) n0m s1.log.length := by
        rw [hs1l]
        refine ⟨Hpbc.1, fun x hx1 hx2 => ?_⟩
        exact commit_drop_cover fs k (uint.nat c) Hkc x (by omega) (Hpbc.2 x (by omega) hx2)
      ihave Hm : mainOwnAt r γ rc i s1 stLeader $$ [HownS HlastLog Hstv Hlown Hdur Hconf Happ Hprod Hsrv Hldr0
          HlogPend Hreg Hpdn Hcomp]
      · unfold mainOwnAt
        iexists a', sst, cfg, ccfg', cidx', li, lch, γl, bs, cp
        rw [hs1l]
        iframe; iframe #
        rw [← hs1l]
        ihave #Hcfg1 : cfgAtIs γ s1.log (uint.nat li) cfg $$ []
        · rw [hs1l]; iexact Hcfg
        ihave #Hccfg1 : cfgAtIs γ s1.log (uint.nat cidx') ccfg' $$ []
        · rw [hs1l]; iexact Hccfg'
        ihave #Hcmt1 : cmtIdx γ s1.term s1.log (uint.nat cidx') $$ []
        · rw [hs1l, hs1t]; iexact Hcmt'
        iframe #
        ipureintro
        refine ⟨?_, ⟨Ha', by rw [hs1c]; omega⟩, by omega, ⟨by rw [hs1l]; exact Hli.1, ?_⟩, Hlcap⟩
        · unfold voteMatches at Hvm ⊢; rw [hs1vt, hs1vc]; exact Hvm
        · rcases Hcfg' with h | ⟨h1, h2, h3⟩
          · left; exact h
          · right; refine ⟨by rw [hs1l]; exact h1, by omega⟩
      ihave Hl : leaderOwnC r γ rc i s.term s1.log $$ [Hcc Hcm Hinfl Hinfls Hinflc Hfs Hrs Hrsm Hrmap Hnt HNMp Hsd Hpbn]
      · unfold leaderOwnC leaderOwnM
        iexists cc', cm', infl', fs.drop k, rs, rmap, nt, sd', n0m
        iframe; iframe #
        ipureintro; exact ⟨Hfs', by rw [hs1l]; exact Hcov, hcov'⟩
      wp_if_destruct
      rotate_left
      · -- removed or demoted: step down (`ShutdownOnRemove` is off)
        wp_apply (wp_config r γ rc i) $$ [$Hr] as %c4 %Hc4
        rw [Hc4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
        wp_auto
        ihave ⟨Hstv, Hmclose⟩ := ml_mainOwnAt_state' r γ rc i s1 stLeader $$ Hm
        rw [show (Follower : val) = #stFollower from rfl]
        wp_apply (wp_setState r γ rc i stLeader stFollower s1 tid) $$ [$Hr $Hstv $Htok] as ⟨Hstv, -, Htok⟩
        · isplitr; · ipureintro; left; rfl
          iapply ml_obsArg_follower γ i s1
        ihave Hm := Hmclose $$ %stFollower Hstv %(by decide)
        wp_for_post
        iframe
        iexists s1, stFollower, lc, γlc, true
        iframe; iframe #
        isplitr; · ipureintro; exact ⟨Or.inl (by decide), fun _ => by decide⟩
        iexists s1.log; iframe; ipureintro; intro h; exact absurd h (by decide)
      · wp_for_post
        iframe
        iexists s1, stLeader, lc, γlc, false
        iframe; iframe #
        isplitr; · ipureintro; exact ⟨Or.inr (hs1t.trans Hterm), by simp⟩
        iexists s1.log; iframe; ipureintro; intro _; exact ⟨rfl, by rw [hs1l]; exact Hlen⟩
    -- verifyCh
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      iapply bag_recv_clause vch γv (verifyP γ rc i vch)
      iframe; iframe #
      inext
      iintro %v Hv
      ihave Hm := cch_mainOwnAt r γ rc i s' cch _ _ $$ Hcch
      unfold verifyP
      icases Hv with (Hnew | Hvoted)
      · -- a fresh future: register it (verifyLeader)
        iunfold verifyNew at Hnew
        icases Hnew with ⟨%sc, #Hsc, Hnc, Hqs, Hvotes, Hvl, Hresp⟩
        wp_auto
        wp_apply (wp_verifyLeader r γ rc i s' v) $$ [$Hr $Hm Hl Hnc Hqs Hvotes Hvl Hresp] as ⟨Hm, Hl⟩
        · rw [Hterm]; iframe
          isplitl [Hnc Hqs Hvotes Hvl Hresp]
          · unfold verifyNew; iexists sc; iframe; iframe #
          iexists n0v; iframe #; ipureintro; exact Hlen
        wp_for_post
        iframe
        iexists s', stLeader, lc, γlc, false; iframe; iframe #
        isplitr; · ipureintro; exact ⟨Or.inr (Hterm), by simp⟩
        iexists s'.log; rw [Hterm]; iframe; ipureintro; intro _; exact ⟨rfl, Hlen⟩
      · -- a voted future
        iunfold verifyVoted at Hvoted
        icases Hvoted with ⟨%T', %sv, %Lr, %n, %q, #HvR, Hback, #Hqs, Hvotes, Hq⟩
        iunfold verifyReg at HvR
        icases HvR with ⟨%q', #Hvreg, #Hqs', #HLpre, #Hrw, ⟨%n0r, #Hn0r, %Hn0rL⟩, %Hq', #Hlock⟩
        icombine Hqs Hqs' gives %Hqq
        subst Hqq
        wp_auto
        wp_if_destruct
        · exfalso; obtain ⟨-, h2, -⟩ := Hq'; simp at h2
        wp_if_destruct
        · -- a voter answered `false`: step down, answer `ErrNotLeader`
          ihave ⟨Hstv, Hmclose⟩ := ml_mainOwnAt_state' r γ rc i s' stLeader $$ Hm
          rw [show (Follower : val) = #stFollower from rfl]
          wp_apply (wp_setState r γ rc i stLeader stFollower s' tid) $$ [$Hr $Hstv $Htok]
            as ⟨Hstv, -, Htok⟩
          · isplitr; · ipureintro; left; rfl
            iapply ml_obsArg_follower γ i s'
          ihave Hm := Hmclose $$ %stFollower Hstv %(by decide)
          imod leader_retire r γ rc i s' stFollower s.term s'.log v T' sv
            $$ [Hm Hl Hback Hvreg] with ⟨%nt, %NM, Hnt, Hntm, Hclose, Hst⟩
          · iframe; iframe #
          wp_auto
          wp_apply (wp_mapDelete nt NM v) $$ [$Hntm] as Hntm
          ihave ⟨Hm, Hl⟩ := Hclose $$ Hntm Hnt
          ipersist v
          icases leaderOwnM_repl r γ rc i s.term _ _ $$ Hl with ⟨%rs, %rmap, Hrs, Hrsm, #Hshared, %Hcov,
            Hlclose⟩
          wp_auto
          wp_func_lits
          wp_bind (App (App (Val (map.forRange _ _)) _) _)
          iapply (wp_map_for_range (fun _ _ => iprop(∃ rp : Loc, repl_ptr ↦ rp))) $$ Hrsm
          iintro %keys %hkeys
          isplitl [repl]
          · iexists _; iframe
          isplitl []
          · imodintro
            iintro %_j %key %u ⟨%hk1, %hk2⟩ ⟨%rp, Hrp⟩
            ihave #Hsh := BigSepM.bigSepM_lookup hk2 $$ Hshared
            wp_auto
            wp_apply (wp_cleanNotify r γ rc i s.term key u v) $$ [$Hsh]
            unfold forMapPostcondition
            iright; ileft
            isplit
            · ipureintro; rfl
            · iexists _; iframe
          iintro ⟨%rp, Hrp⟩ Hrsm
          ihave Hl := Hlclose $$ Hrs Hrsm
          wp_auto
          ihave ⟨%Q, HQ⟩ : (∃ Q : GoInterface → IProp GF,
              (deferResp (v.[verifyFuture, go!"deferError"]) Q ∗ Q eNL) ∨
                deferDone (v.[verifyFuture, go!"deferError"])) $$ [Hst]
          · icases Hst with (⟨%sc, -, -, -, Hresp⟩ | Hd)
            · iexists (verifyQ γ rc i sc); ileft; iframe; unfold verifyQ; ileft; ipureintro
              exact HeNLne
            · iexists (fun _ => iprop(True)); iright; iexact Hd
          wp_apply (wp_verifyFuture_respond v Q eNL) $$ [$HQ] as -
          wp_for_post
          iframe
          iexists s', stFollower, lc, γlc, false; iframe; iframe #
          isplitr; · ipureintro; exact ⟨Or.inl (by decide), by simp⟩
          iexists s'.log; iframe; ipureintro; intro h; exact absurd h (by decide)
        · -- a quorum: hand the future to the FSM goroutine
          icases Hq with (%Hlt | ⟨%Q, %HQ, #HQs⟩)
          · exfalso
            obtain ⟨-, -, -, hq63⟩ := Hq'
            apply Hif
            word
          imod leader_retire r γ rc i s' stLeader s.term s'.log v T' sv
            $$ [Hm Hl Hback Hvreg] with ⟨%nt, %NM, Hnt, Hntm, Hclose, Hst⟩
          · iframe; iframe #
          wp_auto
          wp_apply (wp_mapDelete nt NM v) $$ [$Hntm] as Hntm
          ihave ⟨Hm, Hl⟩ := Hclose $$ Hntm Hnt
          ipersist v
          icases leaderOwnM_repl r γ rc i s.term _ _ $$ Hl with ⟨%rs, %rmap, Hrs, Hrsm, #Hshared, %Hcov,
            Hlclose⟩
          wp_auto
          wp_func_lits
          wp_bind (App (App (Val (map.forRange _ _)) _) _)
          iapply (wp_map_for_range (fun _ _ => iprop(∃ rp : Loc, repl_ptr ↦ rp))) $$ Hrsm
          iintro %keys %hkeys
          isplitl [repl]
          · iexists _; iframe
          isplitl []
          · imodintro
            iintro %_j %key %u ⟨%hk1, %hk2⟩ ⟨%rp, Hrp⟩
            ihave #Hsh := BigSepM.bigSepM_lookup hk2 $$ Hshared
            wp_auto
            wp_apply (wp_cleanNotify r γ rc i s.term key u v) $$ [$Hsh]
            unfold forMapPostcondition
            iright; ileft
            isplit
            · ipureintro; rfl
            · iexists _; iframe
          iintro ⟨%rp, Hrp⟩ Hrsm
          ihave Hl := Hlclose $$ Hrs Hrsm
          ihave ⟨Hl, #Hldr, %n0, #Hlen0, %Hn0⟩ := leaderOwnM_facts r γ rc i s.term _ _ $$ Hl
          obtain ⟨hqQ, hnd, hQv⟩ := HQ
          imod leader_verify_send r γ rc i s' v $$ [Hm Hst] with ⟨%sent, Hp, HP, Hk⟩
          · iframe #; iframe Hm
            icases Hst with (⟨%sc, #Hsc, #Hsv, %Hscv, Hresp⟩ | Hd)
            · ileft
              obtain ⟨h1, h2⟩ := Hscv
              subst h2
              iexists sc, sv, Lr, Q, n0r
              rw [Hterm]
              iframe; iframe #
              ipureintro
              exact ⟨h1, Hq'.1, Hn0rL, ⟨hnd, hQv, by have := Hq'.2.2.1; omega⟩⟩
            · iright; iexact Hd
          wp_auto_lc 3
          wp_apply_core chan.wp_select_blocking
          iapply BigAndL.bigAndL_cons.2
          isplit
          · dsimp only [chan.blockingClausePre]
            iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, fsmCh,
              rc.names.fsmCh.chanName, (interface.mkOk (go.GoType.PointerType verifyFuture.ty) #v)
            isplitr
            · ipureintro
              exact ⟨rfl, rfl⟩
            ihave #Hch : isChan fsmCh rc.names.fsmCh.chanName GoInterface $$ [HfsmSpsc]
            · unfold isSpsc; icases HfsmSpsc with ⟨$, -⟩
            iframe Hch
            iapply spsc_send_au $$ HfsmSpsc [$Hlc1 $Hlc2 $Hlc3] [$Hp $HP]
            inext
            iintro Hp
            ihave Hm := Hk $$ Hp
            wp_auto
            wp_for_post
            iframe
            iexists s', stLeader, lc, γlc, false; iframe; iframe #
            isplitr; · ipureintro; exact ⟨Or.inr (Hterm), by simp⟩
            iexists s'.log; iframe; ipureintro; intro _; exact ⟨rfl, Hlen⟩
          iapply BigAndL.bigAndL_cons.2
          isplit
          · iapply dead_recv_clause shCh γsh
            iframe; iframe #
          iapply BigAndL.bigAndL_nil.2
          itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      iapply dead_recv_clause urCh γur
      iframe; iframe #
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      iapply bag_recv_clause csCh γcs (cfgReqP γ rc i)
      iframe; iframe #
      inext
      iintro %f Hf
      ihave Hm := cch_mainOwnAt r γ rc i s' cch _ _ $$ Hcch
      unfold cfgReqP
      icases Hf with ⟨%x, %mx, %hx, #Hbx, ⟨%cf0, Hcf⟩, Hde⟩
      wp_auto
      wp_apply (wp_getLeadershipTransferInProgress r γ rc i) $$ [$Hr] as %b -
      wp_if_destruct
      · imod mainOwnAt_cfgReq r γ rc i s' stLeader mx x hx $$ [$HInv $Hbx $Hm]
          with ⟨%ccfg, %cfg, %cidx, %li, %ss, Hcfgs, #Hccv, #Hlat, #Hsnap, #Hdx, #Hax, #Hcx, Hm⟩
        ihave #Hccv' := Hccv
        iunfold cfgVal at Hccv'
        icases Hccv' with ⟨#Hss, %Hssok⟩
        iunfold cfgOpt at Hlat
        icases Hlat with ⟨%ss2, #Hss2, -⟩
        wp_apply (configurations.wp_Clone wp_Clone _ ccfg cfg cidx li ss ss2 DFrac.discard
          DFrac.discard) $$ [$Hcfgs $Hss $Hss2] as %cf ⟨Hcfgs, -, -, Hcs, %Hci⟩
        ihave Hm := Hm $$ Hcfgs
        imod ownSlice_persist $$ Hcs with #Hcs
        wp_apply (deferError.respond_cfgFuture wp_respond f (cfgReqQ γ rc i f x) interface.nil)
          $$ [Hde Hcf] as -
        · ileft; iframe
          unfold cfgReqQ
          ileft
          isplitr; · ipureintro; rfl
          iexists cf
          iframe
          iframe Hdx Hax Hcx
          iexists ss
          unfold cfgVal
          iframe Hcs
          isplitr; · ipureintro; exact Hssok
          rw [Hci]; iexact Hsnap
        wp_for_post
        iframe
        iexists s', stLeader, lc, γlc, false; iframe; iframe #
        isplitr; · ipureintro; exact ⟨Or.inr (Hterm), by simp⟩
        iexists s'.log; iframe; ipureintro; intro _; exact ⟨rfl, Hlen⟩
      · -- a transfer is in progress
        wp_apply (deferError.respond_cfgFuture wp_respond f (cfgReqQ γ rc i f x) eTP) $$ [Hde Hcf] as -
        · ileft; iframe
          unfold cfgReqQ
          iright
          iframe HeTP
          iexists cf0; iframe
        wp_for_post
        iframe
        iexists s', stLeader, lc, γlc, false; iframe; iframe #
        isplitr; · ipureintro; exact ⟨Or.inr (Hterm), by simp⟩
        iexists s'.log; iframe; ipureintro; intro _; exact ⟨rfl, Hlen⟩
    iapply BigAndL.bigAndL_cons.2
    isplit
    · icases Hcch with (⟨%Hnil, -⟩ | ⟨HmSt, ⟨%γcch, #HcchBag⟩, Hstab⟩)
      · iright; iapply chan.nilClausePre_recv Loc _ _ Hnil
      · ileft
        iapply bag_recv_clause cch γcch (ccfP γ)
        iframe; iframe #
        inext
        iintro %f Hf
        wp_auto
        wp_apply (wp_getLeadershipTransferInProgress r γ rc i) $$ [$Hr] as %b -
        wp_if_destruct
        · -- a configuration change: appendConfigurationEntry
          wp_apply (wp_appendConfigurationEntry r γ rc i s' f tid) $$ [$Hr $HmSt Hl $Hf $Hstab $Htok]
            as ⟨%s2, Hm, %Hs2, Hl, Htok⟩
          · rw [Hterm]; iexact Hl
          wp_for_post
          iframe
          iexists s2, stLeader, lc, γlc, false
          iframe; iframe #
          isplitr; · ipureintro; exact ⟨Or.inr (Hs2.1.trans Hterm), by simp⟩
          iexists s2.log; rw [← Hterm]; iframe; ipureintro; intro _; exact ⟨rfl, by omega⟩
        · -- a transfer is in progress
          ihave Hm := mainOwnAtSt_mainOwnAt r γ rc i s' $$ HmSt
          unfold ccfP
          icases Hf with ⟨%rq, %lv, %t, %v', Hreq, %Hrq, Hlog, Hresp, Hdisp, Hde⟩
          wp_apply (deferError.respond_ccf wp_respond f cfgChangeQ eTP) $$ [Hde] as -
          · ileft; iframe; unfold cfgChangeQ; iright; ileft; iexists _; iexact HeTP
          wp_for_post
          iframe
          iexists s', stLeader, lc, γlc, false; iframe; iframe #
          isplitr; · ipureintro; exact ⟨Or.inr (Hterm), by simp⟩
          iexists s'.log; iframe; ipureintro; intro _; exact ⟨rfl, Hlen⟩
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      iapply dead_recv_clause bsCh γbs
      iframe; iframe #
    -- applyCh
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      iapply bag_recv_clause applyCh γap (applyP γ rc i)
      iframe; iframe #
      inext
      iintro %v Hv
      ihave Hm := cch_mainOwnAt r γ rc i s' cch _ _ $$ Hcch
      wp_auto
      wp_apply (wp_getLeadershipTransferInProgress r γ rc i) $$ [$Hr] as %b -
      wp_if_destruct
      · wp_bind (App (Val (GoInstruction (CompositeLiteral
          (go.GoType.SliceType (go.GoType.PointerType logFuture.ty))))) (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := Loc) (t := go.GoType.PointerType logFuture.ty) [v]
        wp_auto
        isplitl []; · ipureintro; rfl
        iintro %rsl ⟨Hrsl, Hrcap⟩
        wp_auto
        wp_join iprop(∃ (sl : GoSlice) (fs1 : List Loc),
            ready_ptr ↦ sl ∗ sl ↦* fs1 ∗ ownSliceCap Loc sl (DFrac.own 1) ∗ ⌜fs1 ≠ []⌝ ∗
            ([∗list] f ∈ fs1, applyP γ rc i f))
          at next with [ready Hrsl Hrcap Hv i]
          as ⟨%sl, %fs1, ready, Hsl, Hslc, %Hfs1, Hfs1⟩
        · ihave HI3 : (∃ (j : Nat) (sl : GoSlice) (fs1 : List Loc),
              "i" ∷ i_ptr ↦ W64 j ∗ "ready" ∷ ready_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* fs1 ∗
              "Hslc" ∷ ownSliceCap Loc sl (DFrac.own 1) ∗ "%Hfs1" ∷ ⌜fs1 ≠ [] ∧ j ≤ 64⌝ ∗
              "Hfs1" ∷ ([∗list] f ∈ fs1, applyP γ rc i f) : IProp GF) $$ [i ready Hrsl Hrcap Hv]
          · iexists 0, _, [v]; iframe
            isplitr; · ipureintro; exact ⟨by simp, by omega⟩
            iapply BigSepL.bigSepL_nil.2; iempintro
          wp_for HI3
          wp_apply (wp_config r γ rc i) $$ [$Hr] as %c2 %Hc2
          wp_if_destruct
          · obtain ⟨Hfs1ne, Hj⟩ := Hfs1
            have hP := of_decide_eq_true (go.intoVal_inj Hif)
            have hmax : uint.nat c2.MaxAppendEntries' ≤ 64 := Hc2.2.2.2.2.2.2.2.2.2.2.1
            wp_apply_core chan.wp_select_nonblocking
            isplit
            · iapply BigAndL.bigAndL_cons.2
              isplit
              · simp only [chan.nonblockingClausePre]
                iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, applyCh, γap
                isplitr; · ipureintro; rfl
                isplitr; · iapply is_bag_is_chan γap applyCh _ $$ HapplyBag
                iapply bag_nb_recv_au γap applyCh (applyP γ rc i) _ $$ HapplyBag
                iintro %f Hf
                wp_auto
                wp_bind (App (Val (GoInstruction (CompositeLiteral
                  (go.GoType.SliceType (go.GoType.PointerType logFuture.ty))))) (Val (LiteralValueV _)))
                iapply wp_slice_literal (V := Loc) (t := go.GoType.PointerType logFuture.ty) [f]
                wp_auto
                isplitl []; · ipureintro; rfl
                iintro %fsl ⟨Hfsl, -⟩
                wp_auto
                wp_apply (wp_slice_append (V := Loc)) $$ [$Hsl $Hslc $Hfsl] as %sl2 ⟨Hsl, Hslc, -⟩
                wp_for_post
                iframe
                iexists (j + 1), sl2, fs1 ++ [f]
                rw [show W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) by word]
                iframe
                isplitr
                · ipureintro; refine ⟨by simp, ?_⟩; word
                iapply BigSepL.bigSepL_nil.2; iempintro
              · iapply BigAndL.bigAndL_nil.2; itrivial
            · wp_auto
              wp_for_post
              isplitr; · ipureintro; rfl
              iexists sl, fs1; iframe; ipureintro; exact Hfs1ne
          · have hnP : ¬ (sint.Z (W64 (j : Int)) < sint.Z c2.MaxAppendEntries') := by
              intro h; apply Hif; rw [decide_eq_true h]
            simp only [decide_eq_false hnP, _root_.decide_true, Bool.false_eq_true, ↓reduceIte]
            isplitr; · ipureintro; trivial
            iexists sl, fs1; iframe; ipureintro; exact Hfs1.1
        wp_apply (wp_dispatchLogs r γ rc i s' sl (DFrac.own 1) fs1)
          $$ [$Hr $Hm $Hsl Hl Hfs1] as ⟨%s2, Hm, %Hs2, Hl, -⟩
        · rw [Hterm]; iframe
          isplitr; · ipureintro; exact Hfs1
          iapply (BigSepL.bigSepL_mono (fun {k x} _ => ?_)) $$ Hfs1
          unfold dispP; iintro H; ileft; iexact H
        wp_for_post
        iframe
        iexists s2, stLeader, lc, γlc, false
        iframe; iframe #
        isplitr; · ipureintro; exact ⟨Or.inr (Hs2.1.trans Hterm), by simp⟩
        iexists s2.log; rw [← Hterm]; iframe; ipureintro; intro _; exact ⟨rfl, by omega⟩
      · -- a transfer is in progress
        ihave ⟨%Q, HQ⟩ : (∃ Q : GoInterface → IProp GF,
            (deferResp (v.[logFuture, go!"deferError"]) Q ∗ Q eTP) ∨
              deferDone (v.[logFuture, go!"deferError"])) $$ [Hv]
        · unfold applyP
          icases Hv with (⟨%d, %n, %lv, %t, -, -, -, -, -, -, Hde, Htok⟩ |
            ⟨%lv, %t, %sc, -, -, -, -, -, -, -, Hde⟩)
          · iexists (futQ γ rc v d n); ileft; iframe; unfold futQ; ileft; iframe; iright; iexact HeTP
          · iexists (barrierQ γ rc i sc); ileft; iframe; unfold barrierQ; ileft; ipureintro
            exact HeTPne
        wp_apply (deferError.respond_logFuture wp_respond v Q eTP) $$ [$HQ] as -
        wp_for_post
        iframe
        iexists s', stLeader, lc, γlc, false; iframe; iframe #
        isplitr; · ipureintro; exact ⟨Or.inr (Hterm), by simp⟩
        iexists s'.log; iframe; ipureintro; intro _; exact ⟨rfl, Hlen⟩
    -- lease
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      iapply bag_recv_clause lc γlc (fun _ => iprop(True))
      iframe; iframe #
      inext
      iintro %v Hv
      ihave Hm := cch_mainOwnAt r γ rc i s' cch _ _ $$ Hcch
      wp_auto
      wp_apply (wp_checkLeaderLease r γ rc i s' tid) $$ [$Hr $Hm $Htok Hl]
        as %md ⟨%st2, Hm, %Hst2, Hl, Htok⟩
      · rw [Hterm]; iexact Hl
      wp_apply (wp_config r γ rc i) $$ [$Hr] as %c3 %Hc3
      wp_if_destruct
      · try simp only [minCheckInterval]
        try wp_auto
        ihave #HtimeI : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
        · iPkgInit
        wp_apply (time.After.spec_pkgInit wp_After _) $$ [$HtimeI] as %lc2 %γlc2 #Hlease2
        wp_for_post
        iframe
        iexists s', st2, lc2, γlc2, false
        iframe; iframe #
        isplitr; · ipureintro; exact ⟨Or.inr (Hterm), by simp⟩
        iexists s'.log; rw [← Hterm]; iframe; ipureintro; intro _; exact ⟨rfl, Hlen⟩
      · ihave #HtimeI : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
        · iPkgInit
        wp_apply (time.After.spec_pkgInit wp_After _) $$ [$HtimeI] as %lc2 %γlc2 #Hlease2
        wp_for_post
        iframe
        iexists s', st2, lc2, γlc2, false
        iframe; iframe #
        isplitr; · ipureintro; exact ⟨Or.inr (Hterm), by simp⟩
        iexists s'.log; rw [← Hterm]; iframe; ipureintro; intro _; exact ⟨rfl, Hlen⟩
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      iapply dead_recv_clause lnCh γln
      iframe; iframe #
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      iapply dead_recv_clause fnCh γfn
      iframe; iframe #
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      iapply dead_recv_clause shCh γsh
      iframe; iframe #
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · have hne : st ≠ W32 2 := by intro h; apply Hif; simp [h]
    rw [decide_eq_false hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold deferOk
    icases Hdefer with ⟨%f, Hdf, Hwpf⟩
    wp_auto
    wp_bind (App (Val #f) (Val #()))
    iapply wp_wand $$ Hwpf
    iintro %v %hv
    subst hv
    wp_auto
    iapply HΦ
    icases Hl with ⟨%L, Hl, -⟩
    iframe
    unfold mainOwn; iexists s', st
    isplitl [Hm]; · iexact Hm
    ileft; ipureintro; exact hne

end proof

end Perennial
