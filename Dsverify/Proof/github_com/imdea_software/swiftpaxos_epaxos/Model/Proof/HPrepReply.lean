/-
`handlePrepareReply` (`hPrepareReply`): the law `inv_deliver_prepareReply`, without the recovery's
decision. The branches that send nothing: the state is unchanged, or only `maxRecvBallot` moves
(`inv_deliver_same`), or only the bookkeeping of the instance changes (`preparing := false`,
`nacks + 1`, one more reply below the quorum: `inv_deliver_lb`). The decision (sub-cases
1/2/3/5/6) is open (see notes/prove-model.md, fourth agent).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Frame
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HLocal
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.AuxSteps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Conf

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace PrepReplyProof

open HStepProof HLocal SafeProof AuxProof

/-- A delivery extends `delivered` by a sent position: `Inv0` is kept (the body of
`DeliverProof.inv0_deliver_nop`). -/
theorem inv0_delivered_ext (S : Sys) (fr i n : Nat) (m : Msg) (hS : Inv0 S)
    (hm : (S.sent fr i)[n]? = some m) :
    Inv0 { S with delivered := S.delivered ++ [(fr, i, n)] } := by
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

/-- A delivery whose handler outputs nothing. -/
theorem deliver_eq (S : Sys) (fr i n : Nat) (m : Msg) (σ' : RState)
    (h : hMsg (S.rep i) m = (σ', [])) :
    S.deliver fr i n m =
      { S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } := by
  simp only [Sys.deliver, h, Sys.applyStep, List.foldl_nil]

/-- A delivery whose handler outputs nothing and changes nothing `Inv` reads. -/
theorem inv_deliver_same (S : Sys) (fr i n : Nat) (m : Msg) (σ' : RState) (hS : Inv S)
    (hm : (S.sent fr i)[n]? = some m) (h : hMsg (S.rep i) m = (σ', []))
    (hc : FrameProof.SameCore (S.rep i) σ') (hpo : σ'.peerOrder = (S.rep i).peerOrder)
    (hcls : σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut) :
    Inv (S.deliver fr i n m) := by
  rw [deliver_eq S fr i n m σ' h]
  have hT := inv0_delivered_ext S fr i n m hS.1 hm
  have hcore : ∀ r, FrameProof.SameCore
      (({ S with delivered := S.delivered ++ [(fr, i, n)] } : Sys).rep r) (upd S.rep i σ' r) := by
    intro r
    by_cases hr : r = i
    · subst hr; simp only [upd_same]; exact hc
    · simp only [upd_other _ _ _ _ hr]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨FrameProof.inv_rep_congr _ _ hcore hT, aux_congr S _ hS.2 hS.1.1.2.2.2.2.2.2.1
    (frame_same S _ (fun r => (hcore r).inst) (fun r => (hcore r).crt) (fun r => ?_) rfl rfl
      (fun d h => List.mem_append_left _ h) (fun r => (hcore r).conflicts) rfl hS.2 (fun r => ?_))
    (PMProof.pm_same hS.2.pm (fun r => (hcore r).inst) rfl rfl (fun _ _ _ h => h) rfl
      (fun _ _ _ h => h))
    (ExecOrd.invExec_same hS.1 hS.2.exec (fun r => (hcore r).inst) (fun r e h => h)
      (ExecOrd.I0.agr (FrameProof.inv_rep_congr _ _ hcore hT)) rfl rfl rfl rfl rfl rfl rfl)
    (execLo_of_eq hS.2.execLo (fun r _ => (hcore r).exe))⟩
  · by_cases hr : r = i
    · subst hr; simp only [upd_same]; exact hpo
    · simp only [upd_other _ _ _ _ hr]
  · by_cases hr : r = i
    · subst hr; simp only [upd_same]; exact hcls
    · simp only [upd_other _ _ _ _ hr]; exact ⟨trivial, trivial⟩

/-- The bookkeeping fields the lb-only branches keep (`preparing` may only go false,
`prepareReplies` only grow, `nacks` is free). -/
def LbKeep (lb lb' : LbRec) : Prop :=
  lb'.lastTriedBallot = lb.lastTriedBallot ∧ lb'.ballot = lb.ballot ∧ lb'.status = lb.status ∧
  lb'.cmds = lb.cmds ∧ lb'.seq = lb.seq ∧ lb'.deps = lb.deps ∧
  lb'.preAcceptOKs = lb.preAcceptOKs ∧ lb'.acceptOKs = lb.acceptOKs ∧
  lb'.allEqual = lb.allEqual ∧ lb'.tryingToPreAccept = lb.tryingToPreAccept ∧
  lb'.clientProposals = lb.clientProposals ∧ lb'.leaderResponded = lb.leaderResponded ∧
  (lb'.preparing = true → lb.preparing = true) ∧ (∀ e ∈ lb.prepareReplies, e ∈ lb'.prepareReplies) ∧
  lb'.preAcceptsSent = lb.preAcceptsSent

/-- A new entry of `prepareReplies`: the delivered reply. -/
def NewEntry (S : Sys) (fr i n : Nat) (x : InstId) (lb : LbRec) (e : PReply) : Prop :=
  e.cmdsNil = false ∧ e.m.ballot = lb.lastTriedBallot ∧ (Msg.prepareReply e.m).instOf = some x ∧
  toN e.m.acceptorId = fr ∧ fr ≠ i ∧ (S.sent fr i)[n]? = some (.prepareReply e.m)

/-- **A delivery that changes only one bookkeeping, outputs nothing.** -/
theorem inv_deliver_lb (S : Sys) (fr i n : Nat) (m : Msg) (σ' : RState) (x : InstId) (w : InstRec)
    (lb lb' : LbRec) (hS : Inv S) (hi : i < nR) (hidle : S.idle i)
    (hm : (S.sent fr i)[n]? = some m) (h : hMsg (S.rep i) m = (σ', []))
    (hσ : σ'.inst = upd (S.rep i).inst x (some { w with lb := some lb' }))
    (hc : σ'.id = (S.rep i).id ∧ σ'.peerOrder = (S.rep i).peerOrder ∧
      σ'.crtInstance = (S.rep i).crtInstance ∧ σ'.conflicts = (S.rep i).conflicts ∧
      σ'.execedUpTo = (S.rep i).execedUpTo ∧ σ'.store = (S.rep i).store)
    (hcls : σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut)
    (hw : (S.rep i).inst x = some w) (hlb : w.lb = some lb) (hk : LbKeep lb lb')
    (hacc : lb'.preparing = false → lb.preparing = true → lb.status = stACCEPTED →
      w.status = stACCEPTED → w.bal ≠ lb.lastTriedBallot)
    (hprep : lb'.preparing = true → (lb'.prepareReplies.map (·.m.acceptorId)).Nodup ∧
      ∀ e ∈ lb'.prepareReplies, e ∈ lb.prepareReplies ∨ NewEntry S fr i n x lb e) :
    Inv (S.deliver fr i n m) := by
  rw [deliver_eq S fr i n m σ' h]
  have hT := inv0_delivered_ext S fr i n m hS.1 hm
  have NR : Inv.msgWf ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) ∧ Inv.noTPA ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) ∧ Inv.ballotOwner ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) ∧ Inv.oneProposal ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) ∧
      Inv.votesFollowProposals ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) ∧ Inv.repliesReportVotes ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) ∧ Inv.prepReplyHighest ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) ∧
      Inv.decidedChosen ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) ∧ Inv.depsCover ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) ∧ Inv.witnesses ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) ∧ Inv.attrsCover ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) ∧
      Inv.execOrder ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) ∧ Inv.slots ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) ∧ Inv.clientOps ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) ∧ Inv.commitMsgs ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) ∧
      Inv.pendingKind ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) ∧
      (∀ a b, Sys.msgs ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) a b ≠ [] → a < nR ∧ b < nR ∧ a ≠ b) ∧
      (∀ a b c, (a, b, c) ∈ Sys.delivered ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) → c < (Sys.sent ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) a b).length) :=
    ⟨hT.2.1, hT.2.2.2.1, hT.2.2.2.2.2.1, hT.2.2.2.2.2.2.1, hT.2.2.2.2.2.2.2.1,
      hT.2.2.2.2.2.2.2.2.1, hT.2.2.2.2.2.2.2.2.2.1, hT.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hT.1.2.2.2.2.2.1, hT.1.2.2.2.2.2.2.1⟩
  generalize hS' : ({ S with delivered := S.delivered ++ [(fr, i, n)], rep := upd S.rep i σ' } : Sys) = S' at NR
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hc
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15⟩ := hk
  -- the system's other fields
  have ehist : S'.hist = S.hist := by rw [← hS']
  have emsgs : S'.msgs = S.msgs := by rw [← hS']; rfl
  have esent : S'.sent = S.sent := by rw [← hS']
  have edel : S'.delivered = S.delivered ++ [(fr, i, n)] := by rw [← hS']
  have epend : S'.pending = S.pending := by rw [← hS']
  have ecur : S'.execCur = S.execCur := by rw [← hS']
  have eidx : S'.execIdx = S.execIdx := by rw [← hS']
  have elog : S'.execLog = S.execLog := by rw [← hS']
  have eown : S'.owner = S.owner := by rw [← hS']
  have eops : S'.ops = S.ops := by rw [← hS']
  have egex : S'.gexec = S.gexec := by rw [← hS']
  have efir : S'.fired = S.fired := by rw [← hS']
  have erep : S'.rep = upd S.rep i σ' := by rw [← hS']
  have hev : ∀ r e, S'.ev r e ↔ S.ev r e := by intro r e; simp only [Sys.ev, ehist]
  have hevB : ∀ r e r' e', S'.evBefore r e r' e' ↔ S.evBefore r e r' e' := by
    intro r e r' e'; simp only [Sys.evBefore, ehist]
  have hdm : ∀ a r m', S.deliveredMsg a r m' → S'.deliveredMsg a r m' := by
    rintro a r m' ⟨k, hk1, hk2⟩
    exact ⟨k, by rw [esent]; exact hk1, by rw [edel]; exact List.mem_append_left _ hk2⟩
  have hcv : ∀ y v, S'.committedVal y v ↔ S.committedVal y v := by
    intro y v; simp only [Sys.committedVal, hev, emsgs]
  have hprepR : ∀ r m' e, S'.prepReport r m' e ↔ S.prepReport r m' e := by
    intro r m' e; simp only [Sys.prepReport, hev, emsgs]
  have hcnt : ∀ fr' to p, S'.cnt fr' to p = S.cnt fr' to p := by
    intro fr' to p; simp only [Sys.cnt, emsgs]
  have hall : ∀ fr' to p, S.allDeliv fr' to p → S'.allDeliv fr' to p := by
    intro fr' to p ha k m' hk hp
    rw [emsgs] at hk; rw [edel]; exact List.mem_append_left _ (ha k m' hk hp)
  -- the records
  have hrep : ∀ r y, (S'.rep r).inst y =
      if r = i ∧ y = x then some { w with lb := some lb' } else (S.rep r).inst y := by
    intro r y
    rw [erep]
    by_cases hr : r = i
    · subst hr; simp only [upd_same, hσ, upd_apply, true_and]
    · simp [upd_other _ _ _ _ hr, hr]
  have hv : ∀ r y w2, (S'.rep r).inst y = some w2 → ∃ w1, (S.rep r).inst y = some w1 ∧
      w2 = { w1 with lb := w2.lb } ∧ (w2.lb = w1.lb ∨ (r = i ∧ y = x ∧ w1 = w ∧ w2.lb = some lb')) := by
    intro r y w2 h2
    rw [hrep] at h2
    split at h2
    · rename_i hc; obtain ⟨rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at h2; subst h2
      exact ⟨w, hw, rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
    · exact ⟨w2, h2, rfl, Or.inl rfl⟩
  have hv' : ∀ r y w1, (S.rep r).inst y = some w1 → ∃ w2, (S'.rep r).inst y = some w2 ∧
      w2 = { w1 with lb := w2.lb } ∧ (w2.lb = w1.lb ∨ (r = i ∧ y = x ∧ w1 = w ∧ w2.lb = some lb')) := by
    intro r y w1 h1
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc
      rw [hw] at h1; cases h1
      refine ⟨_, by rw [hrep, if_pos ⟨rfl, rfl⟩], rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
    · exact ⟨w1, by rw [hrep, if_neg hc]; exact h1, rfl, Or.inl rfl⟩
  -- field transfer
  have fld : ∀ w1 w2 : InstRec, w2 = { w1 with lb := w2.lb } →
      w2.cmds = w1.cmds ∧ w2.bal = w1.bal ∧ w2.vbal = w1.vbal ∧ w2.status = w1.status ∧
      w2.seq = w1.seq ∧ w2.deps = w1.deps ∧ w2.id = w1.id ∧ instVal w2 = instVal w1 := by
    intro w1 w2 he
    rw [he]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hex : ∀ r y, (S'.rep r).executed y ↔ (S.rep r).executed y := by
    intro r y
    constructor
    · rintro ⟨w2, h2, hs⟩
      obtain ⟨w1, h1, he, -⟩ := hv r y w2 h2
      exact ⟨w1, h1, by rw [← (fld w1 w2 he).2.2.2.1]; exact hs⟩
    · rintro ⟨w1, h1, hs⟩
      obtain ⟨w2, h2, he, -⟩ := hv' r y w1 h1
      exact ⟨w2, h2, by rw [(fld w1 w2 he).2.2.2.1]; exact hs⟩
  have hdep : ∀ r y z, (S'.rep r).depEdge y z ↔ (S.rep r).depEdge y z := by
    intro r y z
    constructor
    · rintro ⟨w2, h2, hq, hz⟩
      obtain ⟨w1, h1, he, -⟩ := hv r y w2 h2
      exact ⟨w1, h1, hq, by rw [← (fld w1 w2 he).2.2.2.2.2.1]; exact hz⟩
    · rintro ⟨w1, h1, hq, hz⟩
      obtain ⟨w2, h2, he, -⟩ := hv' r y w1 h1
      exact ⟨w2, h2, hq, by rw [(fld w1 w2 he).2.2.2.2.2.1]; exact hz⟩
  have hcmds : ∀ r y, ((S'.rep r).inst y).bind (·.cmds) = ((S.rep r).inst y).bind (·.cmds) := by
    intro r y
    cases h2 : (S'.rep r).inst y with
    | none =>
      cases h1 : (S.rep r).inst y with
      | none => rfl
      | some w1 => obtain ⟨w2, h2', -⟩ := hv' r y w1 h1; rw [h2] at h2'; cases h2'
    | some w2 =>
      obtain ⟨w1, h1, he, -⟩ := hv r y w2 h2
      rw [h1]; simp only [Option.bind_some]; exact (fld w1 w2 he).1
  have hsafeM : SafeMono S S' := by
    refine safeMono_same S S' (fun r y w1 h1 => ?_) (fun r e h => (hev r e).mpr h)
      (fun r e _ h => (hev r e).mp h) (fun fr' to m' h => by rw [emsgs] at h; exact h)
    obtain ⟨w2, h2, he, -⟩ := hv' r y w1 h1
    obtain ⟨-, e2, -, e4, -⟩ := fld w1 w2 he
    exact ⟨w2, h2, e2, fun hs => by rw [e4]; exact hs⟩
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19,
    t20, t21, t22, t23, t24, t25, t26, t27⟩ := hT
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, s21, s22, s23, s24, s25, s26, s27⟩ := hS.1
  have hwf : Inv.wf S' := by
    obtain ⟨w1', w2', w3', w4', w5', w6', w7', w8'⟩ := s1
    refine ⟨fun r hr => ?_, fun r hr y w2 h2 => ?_, fun r hr q hq => ?_, fun r hr q k p hk => ?_,
      fun r hr q hq n' hn' => ?_, fun fr' to hne => ?_, fun fr' to n' hn' => ?_, fun r b hb => ?_⟩
    · rw [erep]; by_cases h : r = i
      · subst h; simp only [upd_same, c1]; exact w1' r hr
      · simp only [upd_other _ _ _ _ h]; exact w1' r hr
    · obtain ⟨w1, h1, he, hl⟩ := hv r y w2 h2
      obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := w2' r hr y w1 h1
      obtain ⟨f1, -, -, f4, -, f6, f7, -⟩ := fld w1 w2 he
      refine ⟨by rw [f7]; exact g1, g2, g3, fun hs => by rw [f6]; rw [f4] at hs; exact g4 hs,
        fun lb2 hlb2 hs => ?_, fun hq => ?_, fun lb2 ps hlb2 hps => ?_⟩
      · rcases hl with hl | ⟨rfl, rfl, rfl, hl⟩
        · rw [hl] at hlb2; exact g5 lb2 hlb2 hs
        · rw [hl] at hlb2; cases hlb2; rw [k6]; rw [k3] at hs; exact g5 lb hlb hs
      · rcases hl with hl | ⟨rfl, rfl, rfl, hl⟩
        · rw [hl]; exact g6 hq
        · rw [hl]; simp
      · rw [eown]
        rcases hl with hl | ⟨rfl, rfl, rfl, hl⟩
        · rw [hl] at hlb2; exact g7 lb2 ps hlb2 hps
        · rw [hl] at hlb2; cases hlb2; rw [k11] at hps; exact g7 lb ps hlb hps
    · rw [erep]; by_cases h : r = i
      · subst h; simp only [upd_same, c3]; exact w3' r hr q hq
      · simp only [upd_other _ _ _ _ h]; exact w3' r hr q hq
    · have hk' : (S.rep r).conflicts q k = some p := by
        rw [erep] at hk; by_cases h : r = i
        · subst h; simp only [upd_same, c4] at hk; exact hk
        · simp only [upd_other _ _ _ _ h] at hk; exact hk
      obtain ⟨k1', k2', k3'⟩ := w4' r hr q k p hk'
      have grow : ∀ y, (S.rep r).inst y ≠ none → (S'.rep r).inst y ≠ none := by
        intro y hy hy'
        obtain ⟨w1, h1⟩ := Option.ne_none_iff_exists'.mp hy
        obtain ⟨w2, h2, -⟩ := hv' r y w1 h1
        rw [hy'] at h2; cases h2
      exact ⟨k1', fun h0 => grow _ (k2' h0), fun h0 => grow _ (k3' h0)⟩
    · have : zz ((S'.rep r).execedUpTo q) = zz ((S.rep r).execedUpTo q) := by
        rw [erep]; by_cases h : r = i
        · subst h; simp only [upd_same, c5]
        · simp only [upd_other _ _ _ _ h]
      rw [this] at hn'
      exact (hex r _).mpr (w5' r hr q hq n' hn')
    · exact NR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 fr' to hne
    · exact NR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 fr' to n' hn'
    · obtain ⟨d1, d2, d3, d4, d5, d6, w1, lb1, h1, hl1⟩ := w8' r b (by rw [epend] at hb; exact hb)
      obtain ⟨w2, h2, -, hl⟩ := hv' r _ w1 h1
      refine ⟨d1, by rw [ecur]; exact d2, d3, d4, d5, d6, w2, ?_⟩
      rcases hl with hl | ⟨-, -, -, hl⟩
      · exact ⟨_, h2, by rw [hl]; exact hl1⟩
      · exact ⟨lb', h2, hl⟩
  have hbal : Inv.ballots S' := by
    refine ⟨fun r hr y w2 h2 => ?_, fun r hr y b st v he => ?_⟩
    · obtain ⟨w1, h1, he, -⟩ := hv r y w2 h2
      obtain ⟨-, e2, e3, -⟩ := fld w1 w2 he
      rw [e2, e3]; exact s5.1 r hr y w1 h1
    · obtain ⟨w1, h1, hle⟩ := s5.2 r hr y b st v ((hev _ _).mp he)
      obtain ⟨w2, h2, he, -⟩ := hv' r y w1 h1
      exact ⟨w2, h2, by rw [(fld w1 w2 he).2.1]; exact hle⟩
  have hsafe : Inv.safe S' := safe_frame hsafeM s26 (fun r y b v h => (hev _ _).mp h)
    (fun r y b v h => (hev _ _).mp h)
  have hrt : Inv.replyTargets S' := by
    intro fr' to m' y hm' hy hk'
    obtain ⟨w1, lb1, h1, hl1⟩ := s3 fr' to m' y (by rw [emsgs] at hm'; exact hm') hy hk'
    obtain ⟨w2, h2, -, hl⟩ := hv' to y w1 h1
    rcases hl with hl | ⟨-, -, -, hl⟩
    · exact ⟨w2, lb1, h2, by rw [hl]; exact hl1⟩
    · exact ⟨w2, lb', h2, hl⟩
  have hpf : lb.preparing = false → lb'.preparing = false := by
    intro h0; cases h' : lb'.preparing
    · rfl
    · rw [k13 h'] at h0; cases h0
  have hlbI : Inv.lbInv S' := by
    intro r hr y w2 lb2 h2 hl2
    obtain ⟨w1, h1, he, hl⟩ := hv r y w2 h2
    obtain ⟨-, f2, -, f4, -⟩ := fld w1 w2 he
    rcases hl with hl | ⟨hr', hy', hw1, hl⟩
    · rw [hl] at hl2
      obtain ⟨a1, a2, a3, a4, a5, ⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩, a8, a9⟩ :=
        s11 r hr y w1 lb2 h1 hl2
      refine ⟨(hev _ _).mpr a1, a2, a3, fun b v hv0 => a4 b v (hv0.imp (hev _ _).mp (hev _ _).mp),
        fun c1 c2 => ?_, ⟨Q, q1, q2, fun a m' hq => ?_⟩, ⟨Q', q1', q2', fun a hq => ?_⟩,
        fun c1 c2 c3 c4 => ?_, fun hp => ?_⟩
      · obtain ⟨d1, d2, v, d3, d4⟩ := a5 c1 c2; exact ⟨d1, d2, v, (hev _ _).mpr d3, d4⟩
      · obtain ⟨b1, b2, b3, b4⟩ := q3 a m' hq; exact ⟨b1, b2, hdm _ _ _ b3, b4⟩
      · obtain ⟨b1, b2, m', b3, b4⟩ := q3' a hq; exact ⟨b1, b2, m', hdm _ _ _ b3, b4⟩
      · rw [f4] at c2; rw [f2] at c3
        obtain ⟨d1, d2⟩ := a8 c1 c2 c3 c4; exact ⟨(hev _ _).mpr d1, (hev _ _).mpr d2⟩
      · obtain ⟨c1, c2⟩ := a9 hp
        refine ⟨c1, fun e he' => ?_⟩
        obtain ⟨d1, d2, d3⟩ := c2 e he'
        refine ⟨d1, d2, ?_⟩
        rcases d3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact Or.inl ⟨e1, hdm _ _ _ e2⟩
        · exact Or.inr ⟨e1, (hev _ _).mpr e2⟩
    · subst hr' hy' hw1
      rw [hl] at hl2; cases hl2
      obtain ⟨a1, a2, a3, a4, a5, ⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩, a8, a9⟩ :=
        s11 r hr y w1 lb h1 hlb
      refine ⟨by rw [k1]; exact (hev _ _).mpr a1, by rw [k1, k2]; exact a2, by rw [k10]; exact a3,
        fun b v hv0 => by rw [k1]; exact a4 b v (hv0.imp (hev _ _).mp (hev _ _).mp),
        fun c1 c2 => ?_, ⟨Q, q1, by rw [k7]; exact q2, fun a m' hq => ?_⟩,
        ⟨Q', q1', by rw [k8]; exact q2', fun a hq => ?_⟩, fun c1 c2 c3 c4 => ?_, fun hp => ?_⟩
      · rw [k3] at c1; rw [k7] at c2
        obtain ⟨d1, d2, v, d3, d4⟩ := a5 c1 c2
        exact ⟨by rw [k2, k1]; exact d1, hpf d2, v, by rw [k1]; exact (hev _ _).mpr d3,
          by rw [k4]; exact d4⟩
      · obtain ⟨b1, b2, b3, b4, b5, b6⟩ := q3 a m' hq
        exact ⟨b1, b2, hdm _ _ _ b3, b4, by rw [k1]; exact b5, by rw [k3, k6, k5, k9]; exact b6⟩
      · obtain ⟨b1, b2, m', b3, b4, b5⟩ := q3' a hq
        exact ⟨b1, b2, m', hdm _ _ _ b3, b4, by rw [k1]; exact b5⟩
      · rw [k3] at c1; rw [k1] at c3 ⊢; rw [f4] at c2; rw [f2] at c3
        cases hpp : lb.preparing
        · obtain ⟨d1, d2⟩ := a8 c1 c2 c3 hpp
          rw [k4, k5, k6]; exact ⟨(hev _ _).mpr d1, (hev _ _).mpr d2⟩
        · exact absurd c3 (hacc c4 hpp c1 c2)
      · obtain ⟨c1, c2⟩ := hprep hp
        obtain ⟨-, a9b⟩ := a9 (k13 hp)
        refine ⟨c1, fun e he' => ?_⟩
        rcases c2 e he' with hold | ⟨n1, n2, n3, n4, n5, n6⟩
        · obtain ⟨d1, d2, d3⟩ := a9b e hold
          refine ⟨by rw [k1]; exact d1, d2, ?_⟩
          rcases d3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · exact Or.inl ⟨e1, hdm _ _ _ e2⟩
          · exact Or.inr ⟨e1, (hev _ _).mpr e2⟩
        · refine ⟨by rw [k1]; exact n2, n3, Or.inl ⟨by rw [n4]; exact n5, ?_⟩⟩
          rw [n4]
          exact ⟨n, by rw [esent]; exact n6, by rw [edel]; simp⟩
  have hagr : Inv.agreement S' := by
    refine ⟨fun y v v' h1 h2 => s12.1 y v v' ((hcv _ _).mp h1) ((hcv _ _).mp h2),
      fun r hr y w2 h2 hc' => ?_⟩
    obtain ⟨w1, h1, he, -⟩ := hv r y w2 h2
    obtain ⟨f1, -, -, f4, -, -, -, f8⟩ := fld w1 w2 he
    rw [f4] at hc'
    obtain ⟨d1, d2⟩ := s12.2 r hr y w1 h1 hc'
    exact ⟨by rw [f1]; exact d1, (hcv _ _).mpr (by rw [f8]; exact d2)⟩
  have hrepo : Inv.reports S' := reports_frame hsafeM (fun r m' e h => (hprepR r m' e).mp h)
    (fun r m' e y b st u _ h => (hevB _ _ _ _).mp h) (fun r e _ h => (hev r e).mp h) s27
  have hso : ∀ r, Sys.slotsOn (S'.rep r) = Sys.slotsOn (S.rep r) := by
    intro r; funext xs k; simp only [Sys.slotsOn, hcmds]
  have hexec : Inv.execClosed S' ∧ Inv.execCursor S' ∧ Inv.execPrefix S' := by
    refine ⟨fun r hr => ?_, fun r hr => ?_, ?_⟩
    · obtain ⟨e1, e2, e3⟩ := s18 r hr
      refine ⟨by rw [elog]; exact e1, fun y => by rw [elog, hex]; exact e2 y,
        fun y w2 h2 hs => ?_⟩
      obtain ⟨w1, h1, he, -⟩ := hv r y w2 h2
      obtain ⟨-, -, -, f4, -, -, -, f8⟩ := fld w1 w2 he
      rw [f4] at hs
      obtain ⟨d1, d2⟩ := e3 y w1 h1 hs
      refine ⟨(hcv _ _).mpr (by rw [f8]; exact d1), fun z hz => ?_⟩
      rw [hex, ecur]; exact d2 z ((hdep r y z).mp hz)
    · by_cases hri : r = i
      · subst r
        have hc0 : S.execCur i = [] := hidle.2
        have hi0 := (s19 i hr).1 hc0
        rw [ecur, eidx]
        exact ⟨fun _ => hi0, fun h => absurd hc0 h⟩
      · have := s19 r hr
        rw [erep, upd_other _ _ _ _ hri, ecur, eidx]; exact this
    · have hlx : ∀ r k, S'.lexec r k = S.lexec r k := by
        intro r k
        simp only [Sys.lexec, Sys.curSlots, hso, ecur, elog, eidx]
      obtain ⟨p1, p2, p3⟩ := s21
      refine ⟨fun r hr k => ?_, fun r hr k => ?_, fun r hr k pre e post h => ?_⟩
      · rw [hlx, egex]; exact p1 r hr k
      · rw [hlx]
        have : (S'.rep r).store = (S.rep r).store := by
          rw [erep]; by_cases h : r = i
          · subst h; simp only [upd_same, c6]
          · simp only [upd_other _ _ _ _ h]
        rw [this]; exact p2 r hr k
      · rw [hlx] at h; rw [egex]; exact p3 r hr k pre e post h
  obtain ⟨n2, n4, n6, n7, n8, n9, n10, n13, n15, n16, n17, n20, n22, n23, n24, n25, -, -⟩ := NR
  refine ⟨⟨hwf, n2, hrt, n4, hbal, n6, n7, n8, n9, n10, hlbI, hagr, n13,
    chosenSafe_of_safe _ hwf hbal n6 n8 hsafe, n15, n16, n17, hexec.1, hexec.2.1, n20,
    hexec.2.2, n22, n23, n24, n25, hsafe, hrepo⟩, ?_⟩
  have hA := hS.2
  have hcrt : ∀ r, (S'.rep r).crtInstance = (S.rep r).crtInstance := by
    intro r; rw [erep]; by_cases h : r = i
    · subst h; simp only [upd_same, c3]
    · simp only [upd_other _ _ _ _ h]
  have hcf : ∀ r, (S'.rep r).conflicts = (S.rep r).conflicts := by
    intro r; rw [erep]; by_cases h : r = i
    · subst h; simp only [upd_same, c4]
    · simp only [upd_other _ _ _ _ h]
  have hpo : ∀ r, (S'.rep r).peerOrder = (S.rep r).peerOrder := by
    intro r; rw [erep]; by_cases h : r = i
    · subst h; simp only [upd_same, c2]
    · simp only [upd_other _ _ _ _ h]
  have hcls' : ∀ r, (S'.rep r).lastScan = (S.rep r).lastScan ∧
      (S'.rep r).lastPut = (S.rep r).lastPut := by
    intro r; rw [erep]; by_cases h : r = i
    · subst h; simp only [upd_same]; exact hcls
    · simp only [upd_other _ _ _ _ h]; exact ⟨trivial, trivial⟩
  -- a bookkeeping after the step: the old one, or `lb'` (for `lb`)
  have hlbv : ∀ r y w2 lb2, (S'.rep r).inst y = some w2 → w2.lb = some lb2 →
      ∃ w1, (S.rep r).inst y = some w1 ∧ w2 = { w1 with lb := w2.lb } ∧
        (w1.lb = some lb2 ∨ (r = i ∧ y = x ∧ w1 = w ∧ lb2 = lb')) := by
    intro r y w2 lb2 h2 hl2
    obtain ⟨w1, h1, he, hl⟩ := hv r y w2 h2
    rcases hl with hl | ⟨h3, h4, h5, hl⟩
    · exact ⟨w1, h1, he, Or.inl (by rw [← hl]; exact hl2)⟩
    · rw [hl] at hl2; cases hl2; exact ⟨w1, h1, he, Or.inr ⟨h3, h4, h5, rfl⟩⟩
  have hlbv' : ∀ r y w1 lb1, (S.rep r).inst y = some w1 → w1.lb = some lb1 →
      ∃ w2 lb2, (S'.rep r).inst y = some w2 ∧ w2.lb = some lb2 ∧
        (lb2 = lb1 ∨ (r = i ∧ y = x ∧ lb1 = lb ∧ lb2 = lb')) := by
    intro r y w1 lb1 h1 hl1
    obtain ⟨w2, h2, -, hl⟩ := hv' r y w1 h1
    rcases hl with hl | ⟨h3, h4, h5, hl⟩
    · exact ⟨w2, lb1, h2, by rw [hl]; exact hl1, Or.inl rfl⟩
    · subst h5; rw [hlb] at hl1; cases hl1; exact ⟨w2, lb', h2, hl, Or.inr ⟨h3, h4, rfl, rfl⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr y w2 h2
    obtain ⟨w1, h1, he, -⟩ := hv r y w2 h2
    rw [(fld w1 w2 he).2.2.2.1]; exact hA.stRange r hr y w1 h1
  · intro r hr y w2 h2 hs
    obtain ⟨w1, h1, he, -⟩ := hv r y w2 h2
    obtain ⟨f1, -, -, f4, -⟩ := fld w1 w2 he
    rw [f4] at hs; rw [f1]; exact hA.cmdsSome r hr y w1 h1 hs
  · intro r hr y w2 h2 hs
    obtain ⟨w1, h1, he, -⟩ := hv r y w2 h2
    obtain ⟨-, -, f3, f4, -⟩ := fld w1 w2 he
    rw [f4] at hs
    obtain ⟨d1, d2⟩ := hA.noneRec r hr y w1 h1 hs
    exact ⟨by rw [f3]; exact d1, fun b st v hv0 => d2 b st v ((hev _ _).mp hv0)⟩
  · intro r hr y w2 h2 hs
    obtain ⟨w1, h1, he, -⟩ := hv r y w2 h2
    obtain ⟨-, -, f3, f4, -⟩ := fld w1 w2 he
    rw [f4] at hs; rw [f3]; exact hA.vbalNonneg r hr y w1 h1 hs
  · intro r hr y w2 h2 b st v hv0
    obtain ⟨w1, h1, he, -⟩ := hv r y w2 h2
    rw [(fld w1 w2 he).2.2.1]; exact hA.votesLe r hr y w1 h1 b st v ((hev _ _).mp hv0)
  · intro r hr y w2 h2 hs
    obtain ⟨w1, h1, he, -⟩ := hv r y w2 h2
    obtain ⟨-, -, f3, f4, -, -, -, f8⟩ := fld w1 w2 he
    rw [f4] at hs ⊢; rw [f3, f8]; exact (hev _ _).mpr (hA.recVote r hr y w1 h1 hs)
  · intro r hr y w2 h2 b u hv0 hle
    obtain ⟨w1, h1, he, -⟩ := hv r y w2 h2
    obtain ⟨-, -, f3, f4, -⟩ := fld w1 w2 he
    rw [f3] at hle; rw [f4]; exact hA.accKeep r hr y w1 h1 b u ((hev _ _).mp hv0) hle
  · intro r hr y w2 h2 hs
    obtain ⟨w1, h1, he, -⟩ := hv r y w2 h2
    obtain ⟨-, f2, -, f4, -⟩ := fld w1 w2 he
    rw [f4] at hs; rw [f2]
    obtain ⟨b, v, d1, d2⟩ := hA.recCommit r hr y w1 h1 hs
    exact ⟨b, v, (hev _ _).mpr d1, d2⟩
  · intro r y b v hr he
    obtain ⟨w1, h1, hs⟩ := hA.commitRec r y b v hr ((hev _ _).mp he)
    obtain ⟨w2, h2, he', -⟩ := hv' r y w1 h1
    exact ⟨w2, h2, by rw [(fld w1 w2 he').2.2.2.1]; exact hs⟩
  · intro r y v he
    obtain ⟨d1, b, d2⟩ := hA.fastCommitEv r y v ((hev _ _).mp he)
    exact ⟨d1, b, (hev _ _).mpr d2⟩
  · intro r y b hr he
    obtain ⟨w1, lb1, h1, hl1, hle⟩ := hA.makerLb r y b hr ((hev _ _).mp he)
    obtain ⟨w2, lb2, h2, hl2, hl⟩ := hlbv' r y w1 lb1 h1 hl1
    rcases hl with rfl | ⟨-, -, rfl, rfl⟩
    · exact ⟨w2, lb2, h2, hl2, hle⟩
    · exact ⟨w2, lb2, h2, hl2, by rw [k1]; exact hle⟩
  · intro r hr y w2 lb2 h2 hl2
    obtain ⟨w1, h1, he, hl⟩ := hlbv r y w2 lb2 h2 hl2
    rw [(fld w1 w2 he).2.1]
    rcases hl with hl | ⟨-, -, rfl, rfl⟩
    · exact hA.lastLeBal r hr y w1 lb2 h1 hl
    · rw [k1]; exact hA.lastLeBal r hr y w1 lb h1 hlb
  · intro r hr; rw [hpo]; exact hA.peerOk r hr
  · intro r hr q hq; rw [hcrt, hcrt]; exact hA.crtOwn r hr q hq
  · intro r hr y w2 h2
    obtain ⟨w1, h1, -, -⟩ := hv r y w2 h2
    rw [hcrt]; exact hA.crtRec r hr y w1 h1
  · intro fr' to m' y hm' hy; rw [hcrt]; exact hA.crtMsg fr' to m' y (by rw [emsgs] at hm'; exact hm') hy
  · intro r e y he hy; rw [hcrt]; exact hA.crtEv r e y ((hev _ _).mp he) hy
  · intro q hq j hj
    rw [hcrt] at hj
    obtain ⟨w1, lb1, h1, hl1⟩ := hA.ownRow q hq j hj
    obtain ⟨w2, lb2, h2, hl2, -⟩ := hlbv' q _ w1 lb1 h1 hl1
    exact ⟨w2, lb2, h2, hl2⟩
  · intro r hr y w2 lb2 h2 hl2 hs v hv0
    obtain ⟨w1, h1, -, hl⟩ := hlbv r y w2 lb2 h2 hl2
    rcases hl with hl | ⟨-, -, rfl, rfl⟩
    · exact hA.paNoAcc r hr y w1 lb2 h1 hl hs v ((hev _ _).mp hv0)
    · rw [k3] at hs; rw [k1] at hv0
      exact hA.paNoAcc r hr y w1 lb h1 hlb hs v ((hev _ _).mp hv0)
  · intro r hr y w2 lb2 h2 hl2 hs hp hc' hb
    obtain ⟨w1, h1, he, hl⟩ := hlbv r y w2 lb2 h2 hl2
    obtain ⟨-, f2, f3, f4, -⟩ := fld w1 w2 he
    obtain ⟨v, hv0⟩ := hp
    rw [f4] at hc' ⊢; rw [f2] at hb; rw [f3]
    rcases hl with hl | ⟨-, -, rfl, rfl⟩
    · exact hA.paLeader r hr y w1 lb2 h1 hl hs ⟨v, (hev _ _).mp hv0⟩ hc' hb
    · rw [k3] at hs; rw [k1] at hv0 hb ⊢
      exact hA.paLeader r hr y w1 lb h1 hlb hs ⟨v, (hev _ _).mp hv0⟩ hc' hb
  · intro r hr y w2 lb2 h2 hl2 hp
    obtain ⟨w1, h1, -, hl⟩ := hlbv r y w2 lb2 h2 hl2
    rcases hl with hl | ⟨-, hy, rfl, rfl⟩
    · obtain ⟨d1, d2, d3, d4, d5⟩ := hA.prepNoProp r hr y w1 lb2 h1 hl hp
      exact ⟨d1, fun v h' => d2 v ((hev _ _).mp h'), fun v h' => d3 v ((hev _ _).mp h'), d4, d5⟩
    · obtain ⟨d1, d2, d3, d4, d5⟩ := hA.prepNoProp r hr y w1 lb h1 hlb (k13 hp)
      refine ⟨by rw [k1]; exact d1, fun v h' => d2 v (by rw [k1] at h'; exact (hev _ _).mp h'),
        fun v h' => d3 v (by rw [k1] at h'; exact (hev _ _).mp h'), fun e he' hn' => ?_,
        fun hl' => ?_⟩
      · rcases (hprep hp).2 e he' with h0 | h0
        · exact d4 e h0 hn'
        · rw [h0.1] at hn'; cases hn'
      · rw [k12] at hl'
        obtain ⟨e, he', h0⟩ := d5 hl'
        exact ⟨e, k14 e he', h0⟩
  · intro fr' to y b; rw [hcnt]; exact hA.paMsgOnce fr' to y b
  · intro fr' to y b; rw [hcnt]; exact hA.accMsgOnce fr' to y b
  · intro r y b st v hst hv0
    rcases hA.paVoteDeliv r y b st v hst ((hev _ _).mp hv0) with ⟨v0, h0⟩ | h0
    · exact Or.inl ⟨v0, (hev _ _).mpr h0⟩
    · exact Or.inr (fun fr' => hall _ _ _ (h0 fr'))
  · intro a r y b h1
    rw [hcnt] at h1 ⊢
    obtain ⟨d1, d2⟩ := hA.parOnce a r y b h1
    exact ⟨d1, hall _ _ _ d2⟩
  · intro a r m' hm'
    obtain ⟨b', v, d1, d2⟩ := hA.arFrom a r m' (by rw [emsgs] at hm'; exact hm')
    exact ⟨b', v, d1, (hev _ _).mpr d2⟩
  · intro a r y b h1
    rw [hcnt] at h1 ⊢
    rcases hA.arOnce a r y b h1 with ⟨w1, lb1, h1', hl1, hlt⟩ | ⟨d1, d2⟩
    · obtain ⟨w2, lb2, h2, hl2, hl⟩ := hlbv' r y w1 lb1 h1' hl1
      refine Or.inl ⟨w2, lb2, h2, hl2, ?_⟩
      rcases hl with rfl | ⟨-, -, rfl, rfl⟩
      · exact hlt
      · rw [k1]; exact hlt
    · exact Or.inr ⟨d1, hall _ _ _ d2⟩
  · intro fr' to m' hm'; exact hA.commitBal fr' to m' (by rw [emsgs] at hm'; exact hm')
  · intro r to m' he
    obtain ⟨d1, d2, d3⟩ := hA.sentPR r to m' ((hev _ _).mp he)
    refine ⟨fun hr => ?_, fun b st v hb => d2 b st v ((hevB _ _ _ _).mp hb),
      fun to' m2 hb hy => d3 to' m2 ((hevB _ _ _ _).mp hb) hy⟩
    obtain ⟨w1, h1, hle⟩ := d1 hr
    obtain ⟨w2, h2, he', -⟩ := hv' r _ w1 h1
    exact ⟨w2, h2, by rw [(fld w1 w2 he').2.1]; exact hle⟩
  · intro r hr e y cy he hrec c hc'
    rw [hcf]; exact hA.confCover r hr e y cy ((hev _ _).mp he) hrec c hc'
  · intro r hr q hq
    refine AuxProof.clsWf_keep (hA.classWf r hr) (hcls' r).1 (hcls' r).2 (fun y h => ?_) q hq
    obtain ⟨w1, h1⟩ := Option.ne_none_iff_exists'.mp h
    obtain ⟨w2, h2, -⟩ := hv' r y w1 h1
    rw [h2]; simp
  · intro r hr e y cy he hrec
    rw [(hcls' r).1, (hcls' r).2]; exact hA.classCover r hr e y cy ((hev _ _).mp he) hrec
  · intro r y b st v hst hv0
    exact (hev _ _).mpr (hA.paAttrs r y b st v hst ((hev _ _).mp hv0))
  · intro r y b v hv0
    rw [eown]; exact hA.valOk r y b v (hv0.imp (hev _ _).mp (hev _ _).mp)
  · obtain ⟨m1, m2, m3, m4, m5, m6⟩ := hA.cmdsNe
    refine ⟨fun fr' to m' hm' => m1 fr' to m' (by rw [emsgs] at hm'; exact hm'),
      fun r hr y w2 cs h2 hc' => ?_, fun r hr y w2 lb2 cs h2 hl2 hc' => ?_,
      fun fr' to m' hm' => m4 fr' to m' (by rw [emsgs] at hm'; exact hm'),
      fun r m' he => m5 r m' ((hev _ _).mp he),
      fun r y b v hv0 => m6 r y b v (hv0.imp (hev _ _).mp (hev _ _).mp)⟩
    · obtain ⟨w1, h1, he, -⟩ := hv r y w2 h2
      rw [(fld w1 w2 he).1] at hc'; exact m2 r hr y w1 cs h1 hc'
    · obtain ⟨w1, h1, -, hl⟩ := hlbv r y w2 lb2 h2 hl2
      rcases hl with hl | ⟨-, -, rfl, rfl⟩
      · exact m3 r hr y w1 lb2 cs h1 hl hc'
      · rw [k4] at hc'; exact m3 r hr y w1 lb cs h1 hlb hc'
  · intro fr' to m' hm'
    exact (hev _ _).mpr (hA.prSent fr' to m' (by rw [emsgs] at hm'; exact hm'))
  · intro r m' he hs; exact hA.selfOk r m' ((hev _ _).mp he) hs
  · intro r m' he; exact hA.selfRaw r m' ((hev _ _).mp he)
  · -- pm (sixth agent): the bookkeeping keeps what `InvPM` reads
    have hlbP : ∀ r y w2 lb2, (S'.rep r).inst y = some w2 → w2.lb = some lb2 →
        ∃ w1 lb1, (S.rep r).inst y = some w1 ∧ w1.lb = some lb1 ∧ PMProof.LbPM lb1 lb2 ∧
          lb2.preAcceptsSent = lb1.preAcceptsSent := by
      intro r y w2 lb2 h2 hl2
      obtain ⟨w1, h1, -, hl⟩ := hlbv r y w2 lb2 h2 hl2
      rcases hl with hl | ⟨-, -, rfl, rfl⟩
      · exact ⟨w1, lb2, h1, hl, PMProof.LbPM.refl _, rfl⟩
      · exact ⟨_, lb, h1, hlb, ⟨k1, k3, k2, k4, k7, k9⟩, k15⟩
    refine PMProof.pm_frame hA.pm (fun r e h => (hev r e).mpr h) (fun r e h => Or.inl ((hev r e).mp h))
      (fun fr' to m' h => by rw [emsgs] at h; exact h) (fun fr' to m' h => by rw [esent]; exact h)
      (fun y u h => (hcv y u).mpr h) (fun r y w1 h1 => ?_)
      (fun r y w2 lb2 h2 hl2 => by
        obtain ⟨w1, lb1, h1, hl1, e, -⟩ := hlbP r y w2 lb2 h2 hl2; exact ⟨w1, lb1, h1, hl1, e⟩) ?_
      (fun r b h => Or.inl (by rw [epend] at h; exact h))
    · by_cases hc : r = i ∧ y = x
      · obtain ⟨rfl, rfl⟩ := hc
        rw [hw] at h1; cases h1
        refine ⟨{ w with lb := some lb' }, ?_, Int.le_refl _⟩
        rw [hrep]; simp
      · exact ⟨w1, by rw [hrep, if_neg hc]; exact h1, Int.le_refl _⟩
    · refine PMProof.ps_frame hA.pm (fun y w2 lb2 h2 hl2 => ?_)
        (fun r b h _ => by rw [epend] at h; exact h)
        (fun y a h => by rw [esent, show S'.outbox = S.outbox by rw [← hS']] at h; exact h)
      obtain ⟨w1, lb1, h1, hl1, e, e'⟩ := hlbP _ y w2 lb2 h2 hl2
      exact ⟨w1, lb1, h1, hl1, e.1, e'⟩
  · intro y ps h; rw [eown] at h; rw [hcrt]; exact hA.ownerCrt y ps h
  · -- execLo (p-exec)
    refine AuxProof.execLo_of_eq hA.execLo (fun r _ => ?_)
    rw [erep]; by_cases h : r = i
    · subst h; simp only [upd_same, c5]
    · simp only [upd_other _ _ _ _ h]
  · -- execution fields (p-modelexec)
    refine ExecOrd.invExec_step hS.1 hS.2.exec (fun r e h => (hev r e).mpr h) hagr elog ecur eidx
      egex eown (by rw [← hS']) eops (fun r _ y _ => by simp only [ExecOrd.cmdsAt, hcmds])
      (fun r _ _ y => by simp only [ExecOrd.cmdsAt, hcmds]) ?_
    intro y w2 lb2 h2 hl2 hne
    obtain ⟨w1, h1, -, hl⟩ := hv _ y w2 h2
    rcases hl with hl | ⟨-, -, h5, hl⟩
    · exact ⟨w1, lb2, h1, by rw [← hl]; exact hl2, hne⟩
    · rw [hl] at hl2; cases hl2; exact ⟨w1, lb, h1, by rw [h5]; exact hlb, by rw [← k11]; exact hne⟩


/-- The recovery decides on reply `m`: every guard passes and the reply completes the quorum. -/
def Decides (σ : RState) (m : PrepareReply) : Prop :=
  ∃ w lb, σ.inst ⟨toN m.replica, toN m.inst⟩ = some w ∧ w.lb = some lb ∧ lb.preparing = true ∧
    stGe w.status stCOMMITTED = false ∧ lb.lastTriedBallot.slt w.bal = false ∧
    m.ballot = lb.lastTriedBallot ∧
    lb.prepareReplies.any (fun e => e.m.acceptorId == m.acceptorId) = false ∧
    ¬ (lb.prepareReplies ++ [(⟨m, false⟩ : PReply)]).length < (nR + 1) / 2

/-- The cases of `hPrepareReply` that do not decide. -/
theorem prepReply_cases (σ : RState) (m : PrepareReply) :
    hPrepareReply σ m = (σ, []) ∨ hPrepareReply σ m = (bumpRecvBallot σ m.ballot, []) ∨
    (∃ w lb lb', σ.inst ⟨toN m.replica, toN m.inst⟩ = some w ∧ w.lb = some lb ∧
      hPrepareReply σ m = ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩
        { w with lb := some lb' }, []) ∧
      ((lb.preparing = true ∧ (stGe w.status stCOMMITTED = true ∨
          lb.lastTriedBallot.slt w.bal = true) ∧ lb' = { lb with preparing := false }) ∨
       lb' = { lb with nacks := lb.nacks + 1 } ∨
       (lb.preparing = true ∧ m.ballot = lb.lastTriedBallot ∧
        lb.prepareReplies.any (fun e => e.m.acceptorId == m.acceptorId) = false ∧
        lb' = { lb with prepareReplies := lb.prepareReplies ++ [(⟨m, false⟩ : PReply)] }))) ∨
    Decides σ m := by
  unfold hPrepareReply
  dsimp only
  cases hw : σ.inst ⟨toN m.replica, toN m.inst⟩ with
  | none => exact Or.inl rfl
  | some w =>
    dsimp only
    cases hlb : w.lb with
    | none => exact Or.inl rfl
    | some lb =>
      dsimp only
      by_cases c1 : lb.preparing = false
      · rw [if_pos c1]; exact Or.inr (Or.inl rfl)
      have c1' : lb.preparing = true := by simpa using c1
      rw [if_neg c1]
      by_cases c2 : stGe w.status stCOMMITTED = true
      · rw [if_pos c2]
        exact Or.inr (Or.inr (Or.inl ⟨w, lb, _, rfl, hlb, rfl, Or.inl ⟨c1', Or.inl c2, rfl⟩⟩))
      rw [if_neg c2]
      by_cases c3 : lb.lastTriedBallot.slt w.bal = true
      · rw [if_pos c3]
        exact Or.inr (Or.inr (Or.inl ⟨w, lb, _, rfl, hlb, rfl, Or.inl ⟨c1', Or.inr c3, rfl⟩⟩))
      rw [if_neg c3]
      by_cases c4 : m.ballot ≠ lb.lastTriedBallot
      · rw [if_pos c4]
        exact Or.inr (Or.inr (Or.inl ⟨w, lb, _, rfl, hlb, rfl, Or.inr (Or.inl rfl)⟩))
      rw [if_neg c4]
      have c4' : m.ballot = lb.lastTriedBallot := by simpa using c4
      by_cases c5 : lb.prepareReplies.any (fun e => e.m.acceptorId == m.acceptorId) = true
      · rw [if_pos c5]; exact Or.inr (Or.inl rfl)
      rw [if_neg c5]
      have c5' : lb.prepareReplies.any (fun e => e.m.acceptorId == m.acceptorId) = false := by
        simpa using c5
      by_cases c6 : (lb.prepareReplies ++ [(⟨m, false⟩ : PReply)]).length < (nR + 1) / 2
      · rw [if_pos c6]
        exact Or.inr (Or.inr (Or.inl ⟨w, lb, _, rfl, hlb, rfl, Or.inr (Or.inr ⟨c1', c4', c5', rfl⟩)⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨w, lb, hw, hlb, c1', by simpa using c2, by simpa using c3,
          c4', c5', c6⟩))

/-- **`handlePrepareReply` keeps the invariant**, except (open) when the recovery decides. -/
theorem inv_deliver_prepareReply_nodec (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR)
    (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered) (p : PrepareReply)
    (hm : (S.sent fr i)[n]? = some (.prepareReply p)) (hd : ¬ Decides (S.rep i) p) :
    Inv (S.deliver fr i n (.prepareReply p)) := by
  have hpm := mem_msgs_of_sent S hm
  rcases prepReply_cases (S.rep i) p with h | h | ⟨w, lb, lb', hw, hlb, h, hk⟩ | h
  · exact inv_deliver_same S fr i n _ _ hS hm h ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl ⟨rfl, rfl⟩
  · refine inv_deliver_same S fr i n _ _ hS hm h ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩
      (by simp) (AuxProof.bumpRB_cls _ _)
  · have hlbI := hS.1.2.2.2.2.2.2.2.2.2.2.1 i hi _ w lb hw hlb
    obtain ⟨-, -, -, -, -, -, -, -, a9⟩ := hlbI
    refine inv_deliver_lb S fr i n _ _ _ w lb lb' hS hi hidle hm h (by simp [RState.setInst])
      ⟨by simp [RState.setInst], by simp [RState.setInst], by simp [RState.setInst],
        by simp [RState.setInst], by simp [RState.setInst], by simp [RState.setInst]⟩
      (AuxProof.bumpRB_cls _ _) hw hlb ?_ ?_ ?_
    · rcases hk with ⟨-, -, rfl⟩ | rfl | ⟨-, -, -, rfl⟩ <;>
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩ <;>
        first | exact fun e he => Or.inl he | exact fun e he => List.mem_append_left _ he | simp
    · intro h0 h1 _ hs hb
      rcases hk with ⟨-, hc | hc, rfl⟩ | rfl | ⟨-, -, -, rfl⟩
      · rw [hs] at hc; exact absurd hc (by decide)
      · rw [hb] at hc; have := (slt_iff _ _).mp hc; omega
      · simp only at h0; rw [h1] at h0; cases h0
      · simp only at h0; rw [h1] at h0; cases h0
    · intro hp
      rcases hk with ⟨-, -, rfl⟩ | rfl | ⟨c1, c4, c5, rfl⟩
      · simp at hp
      · obtain ⟨d1, d2⟩ := a9 hp
        exact ⟨d1, fun e he => Or.inl he⟩
      · obtain ⟨d1, d2⟩ := a9 c1
        refine ⟨?_, fun e he => ?_⟩
        · simp only [List.map_append, List.map_cons, List.map_nil]
          refine List.nodup_append.mpr ⟨d1, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
          intro a ha b hb' hab
          simp only [List.mem_singleton] at hb'
          obtain ⟨e, he, hea⟩ := List.mem_map.mp ha
          have := List.any_eq_false.mp c5 e he
          rw [hea, hab, hb'] at this; simp at this
        · simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact Or.inl he
          · -- the delivered reply is from `fr`
            have hsent := hS.2.prSent fr i p hpm
            have hrep : S.prepReport fr p (.sent i (.prepareReply p)) :=
              ⟨hsent, Or.inl ⟨i, hpm, rfl⟩⟩
            have hacc := (hS.1.2.2.2.2.2.2.2.2.1.1 fr p _ hrep).1
            have hfi : fr ≠ i := (hS.1.1.2.2.2.2.2.1 fr i (List.ne_nil_of_mem hpm)).2.2
            exact Or.inr ⟨rfl, c4, rfl, by rw [hacc]; exact toN_W32 fr hfr, hfi, hm⟩
  · exact absurd h hd

end PrepReplyProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
