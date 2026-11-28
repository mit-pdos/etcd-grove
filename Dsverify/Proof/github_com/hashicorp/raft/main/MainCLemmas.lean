/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/main/MainCLemmas.lean (241f27e).
-/
/-
Helper lemmas of the MAIN-C proofs (run, runFollower, runCandidate, electSelf, preElectSelf,
quorumSize).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.main.MainOwnAt
public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Laws
public import Perennial.Spec.sync.atomic.Bool__Load
public import Perennial.Spec.sync.atomic.Bool__Store

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

open proto gprot

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- Access to `r.configurations.latest.Servers` in the `configurations` field. -/
theorem cfgsServers_acc (r : Loc) (ccfg cfg : Configuration) (cidx : w64) (dq : DFrac) :
    (r.[Raft, go!"configurations"] ↦{dq} configurations.mk ccfg cidx cfg (W64 1) : IProp GF) ⊢
      r.[Raft, go!"configurations"].[configurations, go!"latest"].[Configuration, go!"Servers"] ↦{dq}
        cfg.Servers' ∗
      (r.[Raft, go!"configurations"].[configurations, go!"latest"].[Configuration, go!"Servers"] ↦{dq}
        cfg.Servers' -∗
        r.[Raft, go!"configurations"] ↦{dq} configurations.mk ccfg cidx cfg (W64 1)) := by
  iintro H
  icases (configurations.configurations_access_load_latest (GF := GF) _
    (configurations.mk ccfg cidx cfg (W64 1)) dq).access_strict $$ H with ⟨H1, Hc1⟩
  icases (Configuration.Configuration_access_load_Servers (GF := GF) _ cfg dq).access_strict $$ H1
    with ⟨H2, Hc2⟩
  iframe H2
  iintro H2
  iapply Hc1
  iapply Hc2 $$ H2

/-- Every voter of the protocol is `isSrv` (from the invariant; an unfold of gprot's internals,
the converse of `gprot.isSrv_mem`). -/
theorem isSrv_of_mem [hRB : ReceiptBoundLe GF (2 ^ 62)] (γ : GNames) (E : CoPset)
    (hE : ↑gprotN ⊆ E) (j : SID) (hj : j ∈ γ.srvs) :
    Inv (GF := GF) γ ⊢ |={E}=> isSrv γ j := by
  have h := Inv_read (GF := GF) γ E hE iprop(True) (isSrv γ j) (fun σ => by
    unfold InvBody
    iintro ⟨⟨%hg, Hh, Hs, Hr, Hc⟩, -⟩
    have hj' : j ∈ σ.srvs := by rw [hg.2.1]; exact hj
    ihave ⟨Hh, #Hv⟩ := H_voter_get γ σ j hj' $$ Hh
    isplitl [Hh Hs Hr Hc]
    · iframe; ipureintro; exact hg
    iexact Hv)
  iintro #HI
  iapply h
  isplitl
  · iexact HI
  itrivial

theorem upToDate_refl (L : RLog) : upToDate L.length (lastTerm L) L := Or.inr ⟨rfl, Nat.le_refl _⟩

include sem in
/-- The `RaftState` observations other than `Leader` (for `obsArg_other`). -/
theorem obs_ne_leader (st : w32) (h : st ≠ stLeader) :
    interface.mkOk RaftState.ty #st ≠ leaderObs := by
  unfold leaderObs
  rw [Ne, interface_mkOk_inj]
  rintro ⟨-, hv⟩
  exact h (go.IntoValInj.intoVal_inj hv)

include sem package_sem in
theorem obsArg_follower (γ : GNames) (i : SID) (s : SState) :
    ⊢ obsArg (GF := GF) γ i s (interface.mkOk RaftState.ty #stFollower) := by
  have h := obs_ne_leader (GF := GF) stFollower (by decide)
  exact obsArg_other γ i s _ h (fun v hv => ⟨_, ((interface_mkOk_inj _ _ _ _).1 hv).2.symm⟩)

include sem package_sem in
theorem obsArg_candidate (γ : GNames) (i : SID) (s : SState) :
    ⊢ obsArg (GF := GF) γ i s (interface.mkOk RaftState.ty #stCandidate) := by
  have h := obs_ne_leader (GF := GF) stCandidate (by decide)
  exact obsArg_other γ i s _ h (fun v hv => ⟨_, ((interface_mkOk_inj _ _ _ _).1 hv).2.symm⟩)

instance hdrOk_persistent' (h : RPCHeader) (snd : SID) : Persistent (hdrOk (GF := GF) h snd) := by
  unfold hdrOk; infer_instance

instance rvReq_persistent' (γ : GNames) (rq : RequestVoteRequest) (c : SID) (T li lt : Nat) :
    Persistent (rvReq (GF := GF) γ rq c T li lt) := by
  unfold rvReq; infer_instance

instance pvReq_persistent' (rq : RequestPreVoteRequest) (c : SID) (T : Nat) :
    Persistent (pvReq (GF := GF) rq c T) := by
  unfold pvReq; infer_instance

/-! ## `candidateFromLeadershipTransfer` (holds any bool, stage 2) -/

theorem isRaft_cftCell (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) :
    isRaft r γ rc i ⊢ cftCell r := by
  iintro #Hr
  ihave #Hc := isRaft_cells r γ rc i $$ Hr
  unfold raftCells
  icases Hc with ⟨-, -, -, -, -, #Hcft, -⟩
  iexact Hcft

theorem wp_cft_Load (wp_BoolLoad : sync.atomic.Bool.Load.spec (GF := GF) (hG := hG)) (r : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ cftCell r }}
      (App (Val ((r.[Raft, go!"candidateFromLeadershipTransfer"]) @!!
        go.GoType.PointerType sync.atomic.Bool'.ty @!! go!"Load")) (Val #()))
    {{ (b : Bool), RET #b; True }} := by
  wp_start_folded as #Hcft
  wp_apply (wp_BoolLoad (r.[Raft, go!"candidateFromLeadershipTransfer"]) (DFrac.own 1))
  unfold cftCell
  iinv Hcft with ⟨%b, Hi⟩ Hclose
  iapply fupd_mask_intro (by solve_ndisj)
  iintro Hmask
  inext
  iexists b
  iframe Hi
  iintro Hi
  imod Hmask with -
  imod Hclose $$ [Hi] with -
  · inext; iexists b; iexact Hi
  imodintro
  iapply HΦ
  itrivial

theorem wp_cft_Store (wp_BoolStore : sync.atomic.Bool.Store.spec (GF := GF) (hG := hG)) (r : Loc)
    (b : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ cftCell r }}
      (App (Val ((r.[Raft, go!"candidateFromLeadershipTransfer"]) @!!
        go.GoType.PointerType sync.atomic.Bool'.ty @!! go!"Store")) (Val #b))
    {{ RET #(); True }} := by
  wp_start_folded as #Hcft
  wp_apply (wp_BoolStore (r.[Raft, go!"candidateFromLeadershipTransfer"]) b)
  unfold cftCell
  iinv Hcft with ⟨%b0, Hi⟩ Hclose
  iapply fupd_mask_intro (by solve_ndisj)
  iintro Hmask
  inext
  iexists b0
  iframe Hi
  iintro Hi
  imod Hmask with -
  imod Hclose $$ [Hi] with -
  · inext; iexists b; iexact Hi
  imodintro
  iapply HΦ
  itrivial

/-! ## Select clauses -/

section clauses
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

/-- A receive clause on a bag channel. -/
theorem bag_clause (γc : ChanNames) (ch : Loc) (P : V → IProp GF) (body : Expr)
    (Φ : val → IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ isChanBag γc ch P -∗
      (▷ ∀ v : V, P v -∗ WP (App body (Val (PairV #v #true))) {{ Φ }}) -∗
      chan.blockingClausePre (.CommClause (.RecvCase t (Val #ch)) body) Φ := by
  iintro Hlc #Hb Hbody
  simp only [chan.blockingClausePre]
  iexists V, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply is_bag_is_chan γc ch P $$ Hb
  iapply bag_recv_au γc ch P (fun v ok => WP (App body (Val (PairV #v #ok))) {{ Φ }}) $$ Hlc Hb Hbody

/-- A receive clause on a channel that is never sent on (a bag with predicate `False`). -/
theorem dead_clause (γc : ChanNames) (ch : Loc) (body : Expr) (Φ : val → IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ isChanBag (V := V) γc ch (fun _ => iprop(False)) -∗
      chan.blockingClausePre (.CommClause (.RecvCase t (Val #ch)) body) Φ := by
  iintro Hlc #Hb
  iapply bag_clause γc ch _ body Φ $$ Hlc Hb
  inext
  iintro %v H
  iexfalso
  iexact H

/-- `deadChan` gives the clause. -/
theorem deadChan_clause (ch : Loc) (body : Expr) (Φ : val → IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ deadChan V ch -∗
      chan.blockingClausePre (.CommClause (.RecvCase t (Val #ch)) body) Φ := by
  iintro Hlc #Hd
  unfold deadChan
  icases Hd with ⟨%γc, #Hb⟩
  iapply dead_clause γc ch body Φ $$ Hlc Hb

/-- A receive clause of a nonblocking select on a dead channel: never ready. -/
theorem dead_nb_clause (γc : ChanNames) (ch : Loc) (body : Expr) (Φ : val → IProp GF) :
    ⊢ £ 1 -∗ isChanBag (V := V) γc ch (fun _ => iprop(False)) -∗
      chan.nonblockingClausePre (.CommClause (.RecvCase t (Val #ch)) body) Φ := by
  iintro Hlc #Hb
  simp only [chan.nonblockingClausePre]
  iexists V, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply is_bag_is_chan γc ch _ $$ Hb
  unfold nonblockingRecvAu
  isplit
  · rw [isChanBag_unseal]; unfold isChanBagDef nonblockingRecvAuInner
    icases Hb with ⟨#Hch, #Hinv⟩
    iapply ncfupd_of_fupd  -- (port) channel AUs are `|NC=…` now
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
    unfold chanBagInv
    icases Hi with ⟨%s, Hoc0, Hi⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hoc0
    rcases s with (_ | ⟨v0, buff'⟩) | _ | v | _ | _ | _ | _
    all_goals dsimp only
    all_goals first | itrivial | (iexfalso; iexact Hi) | skip
    all_goals first | (icases BigSepL.bigSepL_cons.1 $$ Hi with ⟨HP, -⟩; iexfalso; iexact HP) | skip
  · itrivial

end clauses

/-! ## Credit-free select clauses and `mainOwnAt` access (from the runFollower proof) -/

section clauses
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

/-- `bag_recv_au` without later credits (the invariant's contents are only used under the
update's `▷`). -/
theorem bag_recv_au' (γ : ChanNames) (ch : Loc) (P : V → IProp GF) (Φ : V → Bool → IProp GF) :
    ⊢ isChanBag γ ch P -∗ (▷ ∀ v, P v -∗ Φ v true) -∗ recvAu γ V Φ := by
  rw [isChanBag_unseal]; unfold isChanBagDef recvAu
  iintro ⟨#Hch, #Hinv⟩ HΦ
  iapply ncfupd_of_fupd  -- (port) channel AUs are `|NC=…` now
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold chanBagInv
  icases Hi with ⟨%s, Hoc0, Hi⟩
  iexists s
  iframe Hoc0
  rcases s with (_ | ⟨v0, buff'⟩) | _ | v | _ | _ | _ | _
  all_goals dsimp only
  case Buffered.cons =>
    iintro Hoc
    icases BigSepL.bigSepL_cons.1 $$ Hi with ⟨HP, Hi⟩
    imod Hmask with -
    imod Hclose $$ [Hoc Hi] with -
    · inext; iexists .Buffered buff'; iframe
    imodintro
    iapply HΦ $$ HP
  case Idle =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc] with -
    · inext; iexists .RcvPending; iframe
    imodintro
    unfold recvNestedAu
    iapply ncfupd_of_fupd  -- (port) channel AUs are `|NC=…` now
    iinv Hinv with Hi Hclose
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    icases Hi with ⟨%s, Hoc1, Hi⟩
    iexists s
    iframe Hoc1
    rcases s with _ | _ | _ | _ | v | _ | (_ | ⟨_, _⟩)
    all_goals dsimp only
    case SndCommit =>
      iintro Hoc
      imod Hmask with -
      imod Hclose $$ [Hoc] with -
      · inext; iexists .Idle; iframe
      imodintro
      iapply HΦ $$ Hi
    all_goals first | itrivial | (iexfalso; iexact Hi)
  case SndPending =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc] with -
    · inext; iexists .RcvCommit; iframe
    imodintro
    iapply HΦ $$ Hi
  all_goals first | itrivial | (iexfalso; iexact Hi)

/-- A receive clause on a bag channel (no credits). -/
theorem bag_clause' (γc : ChanNames) (ch : Loc) (P : V → IProp GF) (body : Expr)
    (Φ : val → IProp GF) :
    ⊢ isChanBag γc ch P -∗
      (▷ ∀ v : V, P v -∗ WP (App body (Val (PairV #v #true))) {{ Φ }}) -∗
      chan.blockingClausePre (.CommClause (.RecvCase t (Val #ch)) body) Φ := by
  iintro #Hb Hbody
  simp only [chan.blockingClausePre]
  iexists V, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply is_bag_is_chan γc ch P $$ Hb
  iapply bag_recv_au' γc ch P (fun v ok => WP (App body (Val (PairV #v #ok))) {{ Φ }}) $$ Hb Hbody

/-- A receive clause on a dead channel (no credits). -/
theorem dead_clause' (γc : ChanNames) (ch : Loc) (body : Expr) (Φ : val → IProp GF) :
    ⊢ isChanBag (V := V) γc ch (fun _ => iprop(False)) -∗
      chan.blockingClausePre (.CommClause (.RecvCase t (Val #ch)) body) Φ := by
  iintro #Hb
  iapply bag_clause' γc ch _ body Φ $$ Hb
  inext
  iintro %v H
  iexfalso
  iexact H

/-- A receive clause on a dead field of `r` (no credits). -/
theorem deadField_clause' (r : Loc) (fld : GoString) (ch : Loc) (body : Expr) (Φ : val → IProp GF) :
    ⊢ r.[Raft, fld] ↦□ ch -∗ deadField V r fld -∗
      chan.blockingClausePre (.CommClause (.RecvCase t (Val #ch)) body) Φ := by
  iintro #Hf #Hd
  unfold deadField deadChan
  icases Hd with ⟨%ch', #Hf', %γc, #Hb⟩
  icombine Hf Hf' gives %Heq
  subst Heq
  iapply bag_clause' γc ch _ body Φ $$ Hb
  inext
  iintro %v H
  iexfalso
  iexact H

end clauses

/-- The main goroutine's half of the `state` ghost variable, out of `mainOwnAt`. -/
theorem mainOwnAt_state' (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (st : w32) :
    mainOwnAt r γ rc i s st ⊢ ghostVar rc.names.state (1 : Qp).half st ∗
      (ghostVar rc.names.state (1 : Qp).half st -∗ mainOwnAt r γ rc i s st) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

/-- `mainOwnAt` split: the `configurations` field and (stage 4) the latest configuration's facts
(`cfgAtIs`, at the log's last configuration entry; stage 3: the bootstrap configuration), the `state`
ghost half, and the rest (which takes back a new state other than `Leader`, or the same). -/
theorem mainOwnAt_split (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (st : w32) :
    mainOwnAt r γ rc i s st ⊢ ∃ (cfg ccfg : Configuration) (cidx li : w64),
      r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li ∗
      cfgAtIs γ s.log (uint.nat li) cfg ∗ ⌜uint.nat li = lastCfgIdx s.log⌝ ∗
      ghostVar rc.names.state (1 : Qp).half st ∗
      (∀ st' : w32, ⌜st' ≠ stLeader ∨ st' = st⌝ -∗
        r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li -∗
        ghostVar rc.names.state (1 : Qp).half st' -∗ mainOwnAt r γ rc i s st') := by
  unfold mainOwnAt
  iintro ⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %c, H1, H2, H3, H4, H5, Hst, Hl, Hp, Hv, H8, H9,
    H10, Hpd, Hcm, Hcc, Hc, #Hcfg, #Hccfg, %Hcf, #Hci, H13⟩
  iexists cfg, ccfg, cidx, li
  iframe Hc Hst
  iframe #
  isplitr; · ipureintro; exact Hcf.1
  iintro %st' %hst' Hc Hst
  iexists a, sst, cfg, ccfg, cidx, li, lch, γl, bs, c
  iframe
  iframe #
  isplitl [Hl]
  · rcases hst' with h | h
    · ileft; ipureintro; exact h
    · subst h; iexact Hl
  ipureintro; exact Hcf

theorem obsArg_candidate' (γ : GNames) (i : SID) (s : SState) :
    ⊢ obsArg (GF := GF) γ i s (interface.mkOk RaftState.ty #(W32 1)) :=
  obsArg_candidate γ i s


end lemmas

/-! ## Elections: the response channels -/

section election
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- A `*voteResult` on the vote channel of candidate `i`'s election of term `T` (tokens `γv`):
its response (owned), the voter's exclusive token of this election, (stage 4) the voter one of the
candidate's configuration's voters `V` (`electSelf` asks only those; stage 3: one of the fixed
voters), its term an existing one, and the vote if granted. -/
def voteP (γ : GNames) (i : SID) (T : Nat) (V : List SID) (γv : GName) (p : Loc) : IProp GF :=
  iprop(∃ (rp : RequestVoteResponse) (j : SID),
    p.[voteResult, go!"RequestVoteResponse"] ↦ rp ∗ (j ↪[γv] () : IProp GF) ∗ ⌜j ∈ V⌝ ∗
    termOk γ (uint.nat rp.Term') ∗ (⌜rp.Granted' = false⌝ ∨ voteIs γ j T i))

/-- A `*preVoteResult` on the pre-vote channel of a pre-election of term `T`: its response
(owned), whose term is `T` or an existing one. -/
def pvP (γ : GNames) (T : Nat) (p : Loc) : IProp GF :=
  iprop(∃ rp : RequestPreVoteResponse,
    p.[preVoteResult, go!"RequestPreVoteResponse"] ↦ rp ∗
    (⌜uint.nat rp.Term' = T⌝ ∨ termOk γ (uint.nat rp.Term')))

/-- The granted votes counted so far by candidate `i` in term `T`: distinct voters (their
tokens), each with its vote. -/
def voteTally (γ : GNames) (i : SID) (T : Nat) (γv : GName) (G : List SID) : IProp GF :=
  iprop(([∗list] j ∈ G, (j ↪[γv] () : IProp GF) ∗ voteIs γ j T i) ∗
    ⌜G.Nodup ∧ ∀ j ∈ G, j ∈ γ.srvs⌝)

theorem voteTally_nil (γ : GNames) (i : SID) (T : Nat) (γv : GName) :
    ⊢ voteTally (GF := GF) γ i T γv [] := by
  unfold voteTally
  isplitl
  · iapply BigSepL.bigSepL_nil.2; iempintro
  ipureintro; exact ⟨List.nodup_nil, by simp⟩

theorem voteTally_add (γ : GNames) (i : SID) (T : Nat) (γv : GName) (G : List SID) (j : SID)
    (hj : j ∈ γ.srvs) :
    voteTally (GF := GF) γ i T γv G ∗ (j ↪[γv] () : IProp GF) ∗ voteIs γ j T i ⊢
      voteTally γ i T γv (j :: G) := by
  unfold voteTally
  iintro ⟨⟨HG, %hG⟩, Hj, #Hv⟩
  ihave %hnot : ⌜j ∉ G⌝ $$ [HG Hj]
  · iintro %hmem
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hmem
    icases BigSepL.bigSepL_lookup_acc hk $$ HG with ⟨⟨Hk, -⟩, -⟩
    ihave %hne := ghostMapElem_ne γv j j (DFrac.own 1) () () $$ Hj Hk
    exact absurd rfl hne
  isplitl
  · iapply BigSepL.bigSepL_cons.2
    iframe
    iframe #
  ipureintro
  refine ⟨List.nodup_cons.2 ⟨hnot, hG.1⟩, ?_⟩
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact hj
  · exact hG.2 x hx

theorem voteTally_votes (γ : GNames) (i : SID) (T : Nat) (γv : GName) (G : List SID) :
    voteTally (GF := GF) γ i T γv G ⊢
      ([∗list] j ∈ G, voteIs γ j T i) ∗ ⌜G.Nodup ∧ ∀ j ∈ G, j ∈ γ.srvs⌝ := by
  unfold voteTally
  iintro ⟨HG, %hG⟩
  isplitl
  · iapply BigSepL.bigSepL_mono (fun _ => sep_elim_right) $$ HG
  ipureintro; exact hG

end election

end github_com.hashicorp.raft

end Perennial
