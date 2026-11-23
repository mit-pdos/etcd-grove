/-
`deliver`: the run loop handles message `(fr, i, n)`. Split by message kind (`inv_step_deliver'`):
the beacons and the TryPreAccept messages leave the replica's state as it is and send nothing
(`inv_deliver_nop`: only `delivered` grows); each protocol handler has its own law
(`inv_deliver_*`; open ones are marked).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Frame
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Safe
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Decide
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.AuxSteps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HAccept
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HPrepare
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HCommit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HPreAccept
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HPrepReply
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HDecide
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.ExecCommit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HAcceptReply
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HPreAcceptReply

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace DeliverProof

/-- A delivery whose handler changes nothing and outputs nothing: only `delivered` grows (by a
sent position). -/
theorem inv0_deliver_nop (S : Sys) (fr i n : Nat) (m : Msg) (hS : Inv0 S)
    (hm : (S.sent fr i)[n]? = some m) (hnop : hMsg (S.rep i) m = (S.rep i, [])) :
    Inv0 (S.deliver fr i n m) := by
  have hS' : S.deliver fr i n m = { S with delivered := S.delivered ++ [(fr, i, n)] } := by
    simp only [Sys.deliver, hnop, Sys.applyStep, List.foldl_nil, upd_eta]
  rw [hS']
  generalize hT : ({ S with delivered := S.delivered ++ [(fr, i, n)] } : Sys) = T
  have hdm : ∀ a r m', S.deliveredMsg a r m' → T.deliveredMsg a r m' := by
    rintro a r m' ⟨k, hk, hd⟩
    exact ⟨k, by rw [← hT]; exact hk, by rw [← hT]; exact List.mem_append_left _ hd⟩
  have hrep : T.rep = S.rep := by rw [← hT]
  have hmsgs : T.msgs = S.msgs := by rw [← hT]; rfl
  have hhist : T.hist = S.hist := by rw [← hT]
  have hpend : T.pending = S.pending := by rw [← hT]
  have hsent : T.sent = S.sent := by rw [← hT]
  have hcur : T.execCur = S.execCur := by rw [← hT]
  have howner : T.owner = S.owner := by rw [← hT]
  have hops : T.ops = S.ops := by rw [← hT]
  have hlog : T.execLog = S.execLog := by rw [← hT]
  have hidx : T.execIdx = S.execIdx := by rw [← hT]
  have hgexec : T.gexec = S.gexec := by rw [← hT]
  have hfired : T.fired = S.fired := by rw [← hT]
  have hdE : T.dEdge = S.dEdge := by
    funext x y; simp only [Sys.dEdge, Sys.committedVal, Sys.ev, hhist, hmsgs]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27⟩ := hS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  case refine_1 =>
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := h1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun fr' to n' hn' => ?_, ?_⟩ <;>
      (try simp only [hrep, hmsgs, hpend, hcur, howner]) <;> try assumption
    rw [hsent]
    rw [← hT] at hn'
    rcases List.mem_append.mp hn' with h | h
    · exact w7 fr' to n' h
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact (List.getElem?_eq_some_iff.mp hm).1
  case refine_11 =>
    intro r hr x w lb hw hlb
    rw [hrep] at hw
    obtain ⟨a1, a2, a3, a4, a5, ⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩, a8, a9⟩ :=
      h11 r hr x w lb hw hlb
    have hev : T.ev = S.ev := by funext r e; simp only [Sys.ev, hhist]
    rw [hev]
    refine ⟨a1, a2, a3, a4, a5, ⟨Q, q1, q2, fun a m' h => ?_⟩, ⟨Q', q1', q2', fun a h => ?_⟩, a8,
      fun hp => ?_⟩
    · obtain ⟨c1, c2, c3, c4⟩ := q3 a m' h; exact ⟨c1, c2, hdm _ _ _ c3, c4⟩
    · obtain ⟨c1, c2, m', c3, c4⟩ := q3' a h; exact ⟨c1, c2, m', hdm _ _ _ c3, c4⟩
    · obtain ⟨c1, c2⟩ := a9 hp
      refine ⟨c1, fun e he => ?_⟩
      obtain ⟨d1, d2, d3⟩ := c2 e he
      refine ⟨d1, d2, ?_⟩
      rcases d3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl ⟨e1, hdm _ _ _ e2⟩
      · exact Or.inr ⟨e1, e2⟩
  all_goals
    simp only [Inv.wf, Inv.msgWf, Inv.replyTargets, Inv.noTPA, Inv.ballots, Inv.ballotOwner,
      Inv.oneProposal, Inv.votesFollowProposals, Inv.repliesReportVotes, Inv.prepReplyHighest,
      Inv.agreement, Inv.decidedChosen, Inv.chosenSafe, Inv.depsCover, Inv.witnesses,
      Inv.attrsCover, Inv.execClosed, Inv.execCursor, Inv.execOrder, Inv.execPrefix, Inv.slots,
      Inv.clientOps, Inv.commitMsgs, Inv.pendingKind, Inv.safe, Inv.reports, Sys.safeAcc, Sys.safePh,
      Sys.blocked, Sys.fastBlocked, Sys.noPA, Sys.fastLive, Sys.fastReplies, Sys.slowChosen,
      Sys.committedVal, Sys.ev, Sys.evBefore, Sys.prepReport, Sys.dEdge, Sys.sccOrd, Sys.lexec,
      Sys.curSlots, Sys.slotOp, Sys.kv, hdE, hrep, hhist, hmsgs, hpend, hops, howner, hlog, hcur,
      hidx, hgexec, hfired] at * <;>
    assumption

theorem inv_deliver_nop (S : Sys) (fr i n : Nat) (m : Msg) (hS : Inv S)
    (hm : (S.sent fr i)[n]? = some m) (hnop : hMsg (S.rep i) m = (S.rep i, [])) :
    Inv (S.deliver fr i n m) := by
  have hS' : S.deliver fr i n m = { S with delivered := S.delivered ++ [(fr, i, n)] } := by
    simp only [Sys.deliver, hnop, Sys.applyStep, List.foldl_nil, upd_eta]
  refine ⟨inv0_deliver_nop S fr i n m hS.1 hm hnop, ?_⟩
  rw [hS']
  exact AuxProof.aux_congr S _ hS.2 hS.1.1.2.2.2.2.2.2.1
    (AuxProof.frame_same S _ (fun r => rfl) (fun r => rfl) (fun r => rfl) rfl rfl
      (fun d h => List.mem_append_left _ h) (fun r => rfl) rfl hS.2 (fun r => ⟨rfl, rfl⟩))
    (PMProof.pm_same hS.2.pm (fun r => rfl) rfl rfl (fun _ _ _ h => h) rfl (fun _ _ _ h => h))
    (ExecOrd.invExec_same hS.1 hS.2.exec (fun r => rfl) (fun r e h => h)
      hS.1.2.2.2.2.2.2.2.2.2.2.2.1 rfl rfl rfl rfl rfl rfl rfl)
    (AuxProof.execLo_of_eq hS.2.execLo (fun r _ => rfl))

/-! ## The handlers' laws -/

section
variable (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i)
  (hn : (fr, i, n) ∉ S.delivered)
include hS hi hfr hidle hn

/-- `handlePrepare`: proved (`Proof/HPrepare.lean`). -/
theorem inv_deliver_prepare (p : Prepare) (hm : (S.sent fr i)[n]? = some (.prepare p)) :
    Inv (S.deliver fr i n (.prepare p)) :=
  PrepareProof.inv_deliver_prepare' S fr i n hS hi hfr hidle hn p hm

/-- `handlePrepareReply`: proved. The branches that change at most the bookkeeping:
`PrepReplyProof.inv_deliver_prepareReply_nodec`; the decision (`Proof/HDecide.lean`): sub-case 1
(`inv_deliver_dec1`, commit of the reported committed value), 2/3 (`inv_deliver_dec23`, Accept),
5/6 (`inv_deliver_dec56`, Phase 1), safe by `DecideProof.decide_safe`. -/
theorem inv_deliver_prepareReply (p : PrepareReply)
    (hm : (S.sent fr i)[n]? = some (.prepareReply p)) :
    Inv (S.deliver fr i n (.prepareReply p)) := by
  by_cases hd : PrepReplyProof.Decides (S.rep i) p
  · obtain ⟨w, lb, hw, hlb, hp, h2, h3, h4, h5, h6⟩ := hd
    by_cases h1 : (DecideStepProof.dD lb p).1 = 1
    · exact DecideStepProof.inv_deliver_dec1 S fr i n hS hi hfr hidle p hm w lb hw hlb hp h2 h3 h4
        h5 h6 h1
    by_cases h23 : (DecideStepProof.dD lb p).1 = 2 ∨ (DecideStepProof.dD lb p).1 = 3
    · exact DecideStepProof.inv_deliver_dec23 S fr i n hS hi hfr hidle p hm w lb hw hlb hp h2 h3
        h4 h5 h6 h1 h23
    · exact DecideStepProof.inv_deliver_dec56 S fr i n hS hi hfr hidle p hm w lb hw hlb hp h2 h3
        h4 h5 h6 h1 h23
  · exact PrepReplyProof.inv_deliver_prepareReply_nodec S fr i n hS hi hfr hidle hn p hm hd

/-- `handlePreAccept`: proved (`Proof/HPreAccept.lean`). -/
theorem inv_deliver_preAccept (p : PreAccept) (hm : (S.sent fr i)[n]? = some (.preAccept p)) :
    Inv (S.deliver fr i n (.preAccept p)) :=
  PreAcceptProof.inv_deliver_preAccept' S fr i n hS hi hfr hidle hn p hm

/-- `handlePreAcceptReply`: proved (`Proof/HPreAcceptReply.lean`: the no-op and dead branches,
the counting branch `par_count`, the slow path `par_slow`, the fast path `par_fast`; the slow
path's ACCEPTED no-op reply, SLOW-WIT, by `InvPM.accSup`/`cmdSafe`). -/
theorem inv_deliver_preAcceptReply (p : PreAcceptReply)
    (hm : (S.sent fr i)[n]? = some (.preAcceptReply p)) :
    Inv (S.deliver fr i n (.preAcceptReply p)) :=
  PARProof.inv_deliver_preAcceptReply' S fr i n hS hi hfr hidle hn p hm

/-- `handleAccept`: proved (`Proof/HAccept.lean`). -/
theorem inv_deliver_accept (p : Accept) (hm : (S.sent fr i)[n]? = some (.accept p)) :
    Inv (S.deliver fr i n (.accept p)) :=
  AcceptProof.inv_deliver_accept' S fr i n hS hi hfr hidle hn p hm

/-- `handleAcceptReply`: proved (`Proof/HAcceptReply.lean`; G3 by `InvPM.arOk`). -/
theorem inv_deliver_acceptReply (p : AcceptReply)
    (hm : (S.sent fr i)[n]? = some (.acceptReply p)) :
    Inv (S.deliver fr i n (.acceptReply p)) :=
  AcceptReplyProof.inv_deliver_acceptReply' S fr i n hS hi hfr hidle hn p hm

/-- `handleCommit`: proved (`Proof/HCommit.lean`). -/
theorem inv_deliver_commit (p : Commit) (hm : (S.sent fr i)[n]? = some (.commit p)) :
    Inv (S.deliver fr i n (.commit p)) :=
  CommitProof.inv_deliver_commit' S fr i n hS hi hfr hidle hn p hm
    (ExecOrd.invExec_commit S fr i n hS hi hidle p hm)

end

end DeliverProof

open DeliverProof in
theorem inv_step_deliver' (S : Sys) (fr i n : Nat) (m : Msg) (hS : Inv S)
    (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hm : (S.sent fr i)[n]? = some m)
    (hn : (fr, i, n) ∉ S.delivered) : Inv (S.deliver fr i n m) := by
  cases m with
  | prepare p => exact inv_deliver_prepare S fr i n hS hi hfr hidle hn p hm
  | prepareReply p => exact inv_deliver_prepareReply S fr i n hS hi hfr hidle hn p hm
  | preAccept p => exact inv_deliver_preAccept S fr i n hS hi hfr hidle hn p hm
  | preAcceptReply p => exact inv_deliver_preAcceptReply S fr i n hS hi hfr hidle hn p hm
  | accept p => exact inv_deliver_accept S fr i n hS hi hfr hidle hn p hm
  | acceptReply p => exact inv_deliver_acceptReply S fr i n hS hi hfr hidle hn p hm
  | commit p => exact inv_deliver_commit S fr i n hS hi hfr hidle hn p hm
  | tryPreAccept p => exact inv_deliver_nop S fr i n _ hS hm rfl
  | tryPreAcceptReply p => exact inv_deliver_nop S fr i n _ hS hm rfl
  | beacon t => exact inv_deliver_nop S fr i n _ hS hm rfl
  | beaconReply t => exact inv_deliver_nop S fr i n _ hS hm rfl

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
