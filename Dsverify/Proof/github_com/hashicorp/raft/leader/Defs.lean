/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/leader/Defs.lean (241f27e).
-/
/-
The leader part of the main goroutine (agent MAIN-L): shared predicates of the internal specs of
`runLeader`'s callees (`setupLeaderState`, `startStopReplication`, `dispatchLogs`, `leaderLoop`,
`checkLeaderLease`, `configurationChangeChIfStable`).

* `noopP f`: the leader's no-op future as `runLeader` allocates it.
* `dispP γ rc f`: a future handed to `dispatchLogs` (a client's, `applyP`, or the no-op).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft

open proto gprot

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- The leader's no-op future (`&logFuture{log: Log{Type: LogNoop}}`): its fields, a no-op
`Log` with nil data and extensions, and a `deferError` whose `errCh` is nil. -/
def noopP (f : Loc) : IProp GF :=
  iprop(∃ (lv : Log) (t : time.Time) (v : GoInterface),
    (f.[logFuture, go!"log"]) ↦ lv ∗ ⌜lv.Type' = W8 1⌝ ∗ lv.Data' ↦*□ ([] : List w8) ∗
    lv.Extensions' ↦*□ ([] : List w8) ∗
    f.[logFuture, go!"response"] ↦ v ∗ f.[logFuture, go!"dispatch"] ↦ t ∗
    deferResp (f.[logFuture, go!"deferError"]) (fun _ => iprop(True)))

/-- A future handed to `dispatchLogs`: a client's (from `applyCh`) or the leader's no-op. -/
def dispP (γ : GNames) (rc : RCtx GF) (i : SID) (f : Loc) : IProp GF :=
  iprop(applyP γ rc i f ∨ noopP f)

/-- The replication map's keys are the servers but `i` of the latest configuration of the leader's log
`L` (configurations over the servers `S`; stage 4; stage 3: it had an entry for every other voter):
what `startStopReplication`
establishes (starting the new servers' goroutines, stopping the removed ones') and `checkLeaderLease`
needs (it calls `replState[j].LastContact()` for every voter `j ≠ i` of the latest configuration). -/
def replCover (S : List SID) (i : SID) (L : RLog) (m : GMap SID Loc) : Prop :=
  ∀ j, (m !! j).isSome ↔ (j ∈ cfgIdsOf S L ∧ j ≠ i)

/-- (stage 2) The inflight futures cover the leader's own entries past its last publication `pb`:
every index of `(max pb n0, L]` (`n0 ≤ L` the election-time log length, `L` the leader's log
length) is in `fs`. So when the commitment's index `c` passes `pb`, `c` is inflight, and the commit step's
`processLogs(lastIdxInGroup)` applies up to `c` (the publication of `c` stays `≤ lastApplied`). -/
def inflCover (fs : List InflightItem) (pb n0 L : Nat) : Prop :=
  n0 ≤ L ∧ ∀ k, Max.max pb n0 < k → k ≤ L → k ∈ fs.map InflightItem.k

/-- `leaderOwn` (core/Defs.lean) with a condition `P` on its replication map and (stage 2) the
inflight futures covering the entries of `(max pb n0, L]`, `pb` the leader's last publication
(`0` or `pubIs`) and `L` its log length (`inflCover`). -/
def leaderOwnM (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat)
    (P : GMap SID Loc → Prop) (L : Nat) : IProp GF :=
  iprop(∃ (cc : GoChan) (cm : Loc) (infl : GoSlice) (fs : List InflightItem) (rs : GoMap)
      (rmap : GMap SID Loc) (nt : GoMap) (sd : GoChan) (n0 : Nat),
    leaderIs γ T i ∗ len0Is γ T n0 ∗
    r.[Raft, go!"leaderState"].[leaderState, go!"commitCh"] ↦ cc ∗ notifyChan cc ∗
    r.[Raft, go!"leaderState"].[leaderState, go!"commitment"] ↦ cm ∗ isCommitment γ i T cm ∗
    r.[Raft, go!"leaderState"].[leaderState, go!"inflight"] ↦ infl ∗
    infl ↦* fs.map InflightItem.f ∗ ownSliceCap Loc infl (DFrac.own 1) ∗
    ⌜(fs.map InflightItem.k).Pairwise (· < ·)⌝ ∗
    ([∗list] x ∈ fs, futResp γ rc i x.f x.k x.e ∗ llogIdx γ T x.k x.e) ∗
    r.[Raft, go!"leaderState"].[leaderState, go!"replState"] ↦ rs ∗ rs ↦$ rmap ∗
    ([∗map] j ↦ s ∈ rmap, replMain r γ rc i T j s) ∗
    r.[Raft, go!"leaderState"].[leaderState, go!"notify"] ↦ nt ∗
    (∃ (NM : GMap Loc Unit) (vch : Loc), nt ↦$ NM ∗ ghostMapAuth rc.names.vnm (1 : Qp).half NM ∗
      r.[Raft, go!"verifyCh"] ↦□ vch ∗
      [∗map] v ↦ _u ∈ NM, leaderNotifyEntry γ rc i T vch v) ∗
    r.[Raft, go!"leaderState"].[leaderState, go!"stepDown"] ↦ sd ∗ notifyChan sd ∗ ⌜P rmap⌝ ∗
    ∃ pb : Nat, (⌜pb = 0⌝ ∨ pubIs γ T pb) ∗ ⌜inflCover fs pb n0 L⌝)

/-- The leader state with a replication goroutine for every other server of the latest configuration
of the leader's log `L` (stage 4: the log, not only its length `|L|`). -/
abbrev leaderOwnC (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (L : RLog) : IProp GF :=
  leaderOwnM r γ rc i T (replCover γ.srvs i L) L.length

theorem leaderOwnM_weaken (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat)
    (P : GMap SID Loc → Prop) (L : Nat) : leaderOwnM r γ rc i T P L ⊢ leaderOwn r γ rc i T := by
  unfold leaderOwnM leaderOwn
  iintro ⟨%cc, %cm, %infl, %fs, %rs, %rmap, %nt, %sd, %n0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10,
    H11, H12, H13, H14, H15, H16, H17, H18, -, -⟩
  iexists cc, cm, infl, fs, rs, rmap, nt, sd, n0
  iframe

/-- The leader state's channel and commitment fields, out of `leaderOwnM` and back. -/
theorem leaderOwnM_fields (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat)
    (P : GMap SID Loc → Prop) (L : Nat) :
    leaderOwnM r γ rc i T P L ⊢ ∃ (cc sd : GoChan) (cm : Loc),
      r.[Raft, go!"leaderState"].[leaderState, go!"commitCh"] ↦ cc ∗ notifyChan cc ∗
      r.[Raft, go!"leaderState"].[leaderState, go!"stepDown"] ↦ sd ∗ notifyChan sd ∗
      r.[Raft, go!"leaderState"].[leaderState, go!"commitment"] ↦ cm ∗ isCommitment γ i T cm ∗
      (r.[Raft, go!"leaderState"].[leaderState, go!"commitCh"] ↦ cc -∗
       r.[Raft, go!"leaderState"].[leaderState, go!"stepDown"] ↦ sd -∗
       r.[Raft, go!"leaderState"].[leaderState, go!"commitment"] ↦ cm -∗ leaderOwnM r γ rc i T P L) := by
  unfold leaderOwnM
  iintro ⟨%cc, %cm, %infl, %fs, %rs, %rmap, %nt, %sd, %n0, #H1, #H2, Hcc, #Hccn, Hcm, #Hcmi, H7, H8,
    H9, %H10, H11, H12, H13, H14, H15, H16, Hsd, #Hsdn, %H19, H20⟩
  iexists cc, sd, cm
  iframe; iframe #
  iintro Hcc Hsd Hcm
  iexists cc, cm, infl, fs, rs, rmap, nt, sd, n0
  iframe; iframe #
  ipureintro; exact ⟨H10, H19⟩

variable [hRB : ReceiptBoundLe GF (2 ^ 62)] in
/-- The leader's last publication `pb` (`0` or a publication of `T`) is within its bound. -/
theorem pb_le (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (T pb m : Nat) :
    Inv (GF := GF) γ ∗ leaderIs γ T i ∗ (⌜pb = 0⌝ ∨ pubIs γ T pb) ∗ pubOwn γ i T m ⊢ |={E}=>
      pubOwn γ i T m ∗ ⌜pb ≤ m⌝ := by
  iintro ⟨#HI, #Hl, Hpb, Hpo⟩
  icases Hpb with (%Hpb | #Hpb)
  · iframe; ipureintro; omega
  iapply pubIs_le γ E hE i T pb m
  iframe; iframe #

variable [hRB : ReceiptBoundLe GF (2 ^ 62)] in
/-- The commitment's index is `0` or past `T`'s election-time log. -/
theorem commit_gt_len0 (E : CoPset) (hE : ↑gprotN ⊆ E) (T c n0 : Nat) :
    Inv (GF := GF) γ ∗ (⌜c = 0⌝ ∨ ∃ p, commitIs γ T c p) ∗ len0Is γ T n0 ⊢ |={E}=> ⌜c = 0 ∨ n0 < c⌝ := by
  iintro ⟨#HI, Hc, #Hn⟩
  icases Hc with (%Hc | ⟨%p, #Hc⟩)
  · imodintro; ipureintro; left; exact Hc
  imod commitIs_len0 γ E hE T c p n0 $$ [] with %h
  · iframe #
  imodintro; ipureintro; right; exact h

include sem in
theorem ml_obs_ne_leader (st : w32) (h : st ≠ stLeader) :
    interface.mkOk RaftState.ty #st ≠ leaderObs := by
  unfold leaderObs
  rw [Ne, interface_mkOk_inj]
  rintro ⟨-, hv⟩
  exact h (go.IntoValInj.intoVal_inj hv)

include sem package_sem in
theorem ml_obsArg_follower (γ : GNames) (i : SID) (s : SState) :
    ⊢ obsArg (GF := GF) γ i s (interface.mkOk RaftState.ty #stFollower) := by
  have h := ml_obs_ne_leader (GF := GF) stFollower (by decide)
  exact obsArg_other γ i s _ h (fun v hv => ⟨_, ((interface_mkOk_inj _ _ _ _).1 hv).2.symm⟩)

/-- `setState(Follower)` on `mainOwnAt`: the state half of `mainOwnAt` for any `st`. -/
theorem ml_mainOwnAt_state' (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (st : w32) :
    mainOwnAt r γ rc i s st ⊢ ghostVar rc.names.state (1 : Qp).half st ∗
      (∀ st', ghostVar rc.names.state (1 : Qp).half st' -∗ ⌜st' ≠ stLeader⌝ -∗
        mainOwnAt r γ rc i s st') := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 2000000 in
instance replShared_persistent' (r : Loc) (γ : GNames) (i : SID) (T : Nat) (j : SID) (s : Loc) :
    Persistent (replShared (GF := GF) r γ rc i T j s) := by
  unfold replShared stopChan; infer_instance

theorem replMain_split (r : Loc) (γ : GNames) (i : SID) (T : Nat) (m : GMap SID Loc) :
    ([∗map] j ↦ s ∈ m, replMain (GF := GF) r γ rc i T j s) ⊣⊢
      ([∗map] j ↦ s ∈ m, replShared r γ rc i T j s) ∗
      ([∗map] j ↦ s ∈ m, ∃ γs : StopNames, replStopCh s γs ∗ stopCloser γs) := by
  unfold replMain; rw [BigSepM.bigSepM_sep_eq]; exact .rfl

/-- The replication map out of `leaderOwnM` (read-only) and back; its goroutines' shared facts. -/
theorem leaderOwnM_repl (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat)
    (P : GMap SID Loc → Prop) (L : Nat) :
    leaderOwnM r γ rc i T P L ⊢ ∃ (rs : GoMap) (rmap : GMap SID Loc),
      r.[Raft, go!"leaderState"].[leaderState, go!"replState"] ↦ rs ∗ rs ↦$ rmap ∗
      ([∗map] j ↦ s ∈ rmap, replShared r γ rc i T j s) ∗ ⌜P rmap⌝ ∗
      (r.[Raft, go!"leaderState"].[leaderState, go!"replState"] ↦ rs -∗ rs ↦$ rmap -∗
        leaderOwnM r γ rc i T P L) := by
  unfold leaderOwnM
  iintro ⟨%cc, %cm, %infl, %fs, %rs, %rmap, %nt, %sd, %n0, #H1, #H2, Hcc, #Hccn, Hcm, #Hcmi, H7, H8,
    H9, %H10, H11, Hrs, Hrsm, Hrmap, H15, H16, Hsd, #Hsdn, %H19, H20⟩
  ihave ⟨#Hsh, Hstops⟩ := (replMain_split (rc := rc) r γ i T rmap).1 $$ Hrmap
  iexists rs, rmap
  iframe; iframe #
  isplitr; · ipureintro; exact H19
  iintro Hrs Hrsm
  ihave Hrmap := (replMain_split (rc := rc) r γ i T rmap).2 $$ [Hstops]
  · iframe; iframe #
  iexists cc, cm, infl, fs, rs, rmap, nt, sd, n0
  iframe; iframe #
  ipureintro; exact ⟨H10, H19⟩

/-- `leaderOwnM`'s persistent facts: `leaderIs`, the election-time log length (at most `L`). -/
theorem leaderOwnM_facts (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat)
    (P : GMap SID Loc → Prop) (L : Nat) :
    leaderOwnM r γ rc i T P L ⊢ leaderOwnM r γ rc i T P L ∗ leaderIs γ T i ∗
      ∃ n0, len0Is γ T n0 ∗ ⌜n0 ≤ L⌝ := by
  unfold leaderOwnM
  iintro ⟨%cc, %cm, %infl, %fs, %rs, %rmap, %nt, %sd, %n0, #H1, #H2, Hcc, #Hccn, Hcm, #Hcmi, H7, H8,
    H9, %H10, H11, Hrs, Hrsm, Hrmap, H15, H16, Hsd, #Hsdn, %H19, %pb, #Hpb, %Hpbc⟩
  isplitl
  · iexists cc, cm, infl, fs, rs, rmap, nt, sd, n0
    iframe; iframe #
    ipureintro; exact ⟨H10, H19, Hpbc⟩
  iframe #
  ipureintro; exact Hpbc.1

/-- The `configurations` field out of `mainOwnAt` and back (stage 4: with its facts, `cfgAtIs`). -/
theorem mainOwnAt_conf (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (st : w32) :
    mainOwnAt r γ rc i s st ⊢ ∃ (ccfg cfg : Configuration) (cidx li : w64),
      r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li ∗
      cfgAtIs γ s.log (uint.nat li) cfg ∗ cfgAtIs γ s.log (uint.nat cidx) ccfg ∗
      ⌜uint.nat li = lastCfgIdx s.log⌝ ∗
      (r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li -∗
        mainOwnAt r γ rc i s st) := by
  unfold mainOwnAt
  iintro ⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %c, H1, H2, H3, %H4, H5, H6, H7, H8, H9, H10,
    %H11, H12, Hpd, Hcm, %Hc, Hconf, #Hcfg, #Hccfg, %Hli, #Hcmt, #Hlch, #Hlchan, Hlown, %Hlcap⟩
  iexists ccfg, cfg, cidx, li
  iframe Hconf; iframe #
  isplitr; · ipureintro; exact Hli.1
  iintro Hconf
  iexists a, sst, cfg, ccfg, cidx, li, lch, γl, bs, c
  iframe; iframe #
  ipureintro; exact ⟨H4, H11, Hc, Hli, Hlcap⟩

end defs

end github_com.hashicorp.raft

end Perennial
