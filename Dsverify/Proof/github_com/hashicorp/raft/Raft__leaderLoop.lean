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
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

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
    github_com.hashicorp.raft.Raft.leaderLoop.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
