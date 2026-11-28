/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/leader/VerifyCase.lean (241f27e).
-/
/-
The leader part of the main goroutine (agent MAIN-L), stage 2: the ghost steps of the leader loop's
`verifyCh` case for a voted future.

* `leader_retire`: the future leaves the registry and the leader's notify set (with the Go map
  delete); its responder state comes out;
* `verify_item`: at a quorum of the leader's term, the read bound (`gprot.read_bound_upd`) gives
  `verifyItem` for what the leader handed to its FSM (`pubOwn`'s bound `≤ lastApplied`);
* `leader_verify_send`: the item sent to the FSM goroutine on `fsmMutateCh` (`fsmVerifyP`, an
  empty batch after the last one), from `mainOwnAt`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.leader.Verify
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Snap

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

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
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

instance respWit_persistent' (γ : GNames) (j : SID) (T : Nat) (ss : Snap) :
    Persistent (respWit (GF := GF) γ j T ss) := by
  unfold respWit; infer_instance

instance verifyItem_persistent' (γ : GNames) (i : SID) (sc : Snap) (a : Nat) :
    Persistent (verifyItem (GF := GF) γ i sc a) := by
  unfold verifyItem; infer_instance

instance batchStart_persistent' (rc : RCtx GF) (n k0 : Nat) : Persistent (batchStart rc n k0) := by
  unfold batchStart; infer_instance

/-- **A voted future comes back** (main goroutine side): it leaves the registry (`mainOwnAt`) and
the leader's notify set (`leaderOwnC`: the Go map `notify` loses it with `delete`); its responder
state comes out (pending only if registered in the leader's term `T`). -/
theorem leader_retire (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (st : w32)
    (T : Nat) (L : RLog) (v : Loc) (T' : Nat) (sv : Snap) :
    mainOwnAt r γ rc i s st ∗ leaderOwnC r γ rc i T L ∗ backTok rc v ∗ vregIs rc v T' sv ⊢ |==>
    ∃ (nt : GoMap) (NM : GMap Loc Unit),
      r.[Raft, go!"leaderState"].[leaderState, go!"notify"] ↦ nt ∗ nt ↦$ NM ∗
      (nt ↦$ GMap.delete v NM -∗ r.[Raft, go!"leaderState"].[leaderState, go!"notify"] ↦ nt -∗
        mainOwnAt r γ rc i s st ∗ leaderOwnC r γ rc i T L) ∗
      ((∃ sc : Snap, histLb γ sc ∗ histLb γ sv ∗ ⌜snapLe sc sv ∧ T' = T⌝ ∗
          deferResp (v.[verifyFuture, go!"deferError"]) (verifyQ γ rc i sc)) ∨
        deferDone (v.[verifyFuture, go!"deferError"])) := by
  unfold mainOwnAt leaderOwnC leaderOwnM
  iintro ⟨⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %c, Hsrv, Hdur, HownS, %Hvm, HlastLog,
    Hstv, Hldr0, HlogPend, Hreg, Happ, %Ha, Hprod, Hpdn, Hcomp, %Hc, Hconf, #Hcfg, #Hccfg, %Hli,
    #Hcmt, #Hlch, #Hlchan, Hlown, %Hlcap⟩,
    ⟨%cc, %cm, %infl, %fs, %rs, %rmap, %nt, %sd, %n0, #Hldr, #Hlen0, Hcc, #Hccn, Hcm,
      #Hcmi, Hinfl, Hinfls, Hinflc, %Hfs, Hfs, Hrs, Hrsm, Hrmap, Hnt,
      ⟨%NM, %vch, Hntm, HNMa, #Hvch, HNMs⟩, Hsd, #Hsdn, %Hcov, %pb, #Hpb, %Hpbc⟩, Hback, #Hvreg⟩
  imod vreg_retire γ rc i T vch v T' sv NM $$ [Hreg HNMa HNMs Hback] with ⟨Hreg, HNMa, HNMs, Hst⟩
  · iframe; iframe #
  imodintro
  iexists nt, NM
  iframe Hnt Hntm Hst
  iintro Hntm Hnt
  isplitl [Hsrv Hdur HownS HlastLog Hstv Hldr0 HlogPend Hreg Happ Hprod Hpdn Hcomp Hconf Hlown]
  · iexists a, sst, cfg, ccfg, cidx, li, lch, γl, bs, c
    iframe; iframe #
    ipureintro; exact ⟨Hvm, Ha, Hc, Hli, Hlcap⟩
  ihave HNMp : (∃ (NM' : GMap Loc Unit) (vch' : Loc), nt ↦$ NM' ∗
      ghostMapAuth rc.names.vnm (1 : Qp).half NM' ∗ r.[Raft, go!"verifyCh"] ↦□ vch' ∗
      [∗map] w ↦ _u ∈ NM', leaderNotifyEntry γ rc i T vch' w : IProp GF) $$ [Hntm HNMa HNMs]
  · iexists GMap.delete v NM, vch
    iframe; iframe #
  iexists cc, cm, infl, fs, rs, rmap, nt, sd, n0
  iframe; iframe #
  ipureintro; exact ⟨Hfs, Hcov, Hpbc⟩

/-- **The read bound of a verify** (the leader `i` of `T`, registered at the snapshot `sv` with
its log prefix `L` then (`llogPre`, of the length `sv` counted, past `T`'s election part `n0`), at a
quorum `Q` of `L`'s latest configuration of witnesses of `T` after `sv`, and its own witness;
`sc ≤ sv` the client's snapshot): `verifyItem` for every `a` at least the publications' bound
`m`. -/
theorem verify_item (E : CoPset) (hE : ↑gprotN ⊆ E) (γ : GNames) (i : SID) (T n0 m a : Nat)
    (sc sv : Snap) (L : RLog) (Q : List SID) (hsc : snapLe sc sv) (hma : m ≤ a)
    (hL : L.length = sv.llen T) (hn0 : n0 < L.length) (hQ : isQuorumOf (cfgOfC γ.cv L) Q) :
    Inv (GF := GF) γ ∗ histLb γ sc ∗ histLb γ sv ∗ leaderIs γ T i ∗ len0Is γ T n0 ∗
      llogPre γ T L ∗ pubOwn γ i T m ∗ respWit γ i T sv ∗
      ([∗list] j ∈ Q, respWit γ j T sv) ⊢ |={E}=>
      pubOwn γ i T m ∗ verifyItem γ i sc a := by
  iintro ⟨#HI, #Hsc, #Hsv, #Hldr, #Hlen0, #Hpre, Hpo, #Hiw, #HQ⟩
  ihave #HQ' : ([∗list] j ∈ Q, ∃ sq, histLb γ sq ∗ ⌜snapLe sv sq ∧ sq.term j ≤ T⌝ : IProp GF) $$ []
  · iapply (BigSepL.bigSepL_mono (fun {k j} _ => ?_)) $$ HQ
    unfold respWit
    iintro ⟨%sq, #Hsq, %Hsq⟩
    iexists sq; iframe #; ipureintro; exact ⟨Hsq.1, Nat.le_of_eq Hsq.2⟩
  imod read_bound_upd γ E hE sv T n0 m i L Q hL hn0 hQ $$ [Hpo] with ⟨Hpo, %Hb⟩
  · iframe; iframe #
  unfold respWit
  icases Hiw with ⟨%st, #Hst, %Hst⟩
  imodintro
  iframe Hpo
  unfold verifyItem
  iexists T, n0, st
  iframe #
  ipureintro
  refine ⟨snapLe_trans hsc Hst.1, Hst.2, fun i' hi' => ?_⟩
  have hd := hsc.2.2.1 i'
  rcases Hb i' hi' with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- `verify_item` on a responder state (pending at a quorum, or already answered). -/
theorem verify_item_or (γ : GNames) (rc : RCtx GF) (i : SID) (T m a : Nat) (vf : Loc)
    (hma : m ≤ a) :
    Inv γ ∗ leaderIs γ T i ∗ pubOwn γ i T m ∗
      ((∃ (sc sv : Snap) (L : RLog) (Q : List SID) (n0 : Nat), histLb γ sc ∗ histLb γ sv ∗
          llogPre γ T L ∗ len0Is γ T n0 ∗
          ⌜snapLe sc sv ∧ L.length = sv.llen T ∧ n0 < L.length ∧ isQuorumOf (cfgOfC γ.cv L) Q⌝ ∗
          respWit γ i T sv ∗ ([∗list] j ∈ Q, respWit γ j T sv) ∗
          deferResp (vf.[verifyFuture, go!"deferError"]) (verifyQ γ rc i sc)) ∨
        deferDone (vf.[verifyFuture, go!"deferError"])) ⊢ |={⊤}=>
      pubOwn γ i T m ∗
      ((∃ sc : Snap, verifyItem γ i sc a ∗
          deferResp (vf.[verifyFuture, go!"deferError"]) (verifyQ γ rc i sc)) ∨
        deferDone (vf.[verifyFuture, go!"deferError"])) := by
  iintro ⟨#HI, #Hldr, Hpo, Hst⟩
  icases Hst with (⟨%sc, %sv, %L, %Q, %n0, #Hsc, #Hsv, #Hpre, #Hlen0, %HQ, #Hiw, #HQs, Hresp⟩ | Hd)
  · obtain ⟨hsc, hL, hn0, hQ⟩ := HQ
    imod verify_item ⊤ (by solve_ndisj) γ i T n0 m a sc sv L Q hsc hma hL hn0 hQ
      $$ [Hpo] with ⟨Hpo, #Hit⟩
    · iframe; iframe #
    imodintro
    iframe Hpo
    ileft; iexists sc; iframe; iframe #
  · imodintro; iframe Hpo; iright; iexact Hd

/-- **The verify item sent to the FSM goroutine** (`fsmMutateCh <- v`, the quorum case): from
`mainOwnAt` (the FSM producer's state, `lastApplied`, the publications' bound), the leader's
facts and the future's responder state at a quorum (or already answered): the `fsmP` element (an
empty batch after the last one, `fsmVerifyP`) and the producer's state back after the send. -/
theorem leader_verify_send (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState)
    (vf : Loc) :
    Inv γ ∗ mainOwnAt r γ rc i s stLeader ∗
      ((∃ (sc sv : Snap) (L : RLog) (Q : List SID) (n0 : Nat), histLb γ sc ∗ histLb γ sv ∗
          llogPre γ s.term L ∗ len0Is γ s.term n0 ∗
          ⌜snapLe sc sv ∧ L.length = sv.llen s.term ∧ n0 < L.length ∧
            isQuorumOf (cfgOfC γ.cv L) Q⌝ ∗
          respWit γ i s.term sv ∗ ([∗list] j ∈ Q, respWit γ j s.term sv) ∗
          deferResp (vf.[verifyFuture, go!"deferError"]) (verifyQ γ rc i sc)) ∨
        deferDone (vf.[verifyFuture, go!"deferError"])) ⊢ |={⊤}=>
    ∃ sent : List GoInterface, spscProducer rc.names.fsmCh sent ∗
      fsmP γ rc i sent.length (interface.mkOk (go.GoType.PointerType verifyFuture.ty) #vf) ∗
      (spscProducer rc.names.fsmCh
          (sent ++ [interface.mkOk (go.GoType.PointerType verifyFuture.ty) #vf]) -∗
        mainOwnAt r γ rc i s stLeader) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end defs

end github_com.hashicorp.raft

end Perennial
