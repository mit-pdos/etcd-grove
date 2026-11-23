/-
The steps that change no protocol state the invariant reads: `peerOrder`, `beTheLeader` (only
`peerOrder`/`isLeader`, which `Inv` does not mention), `flush` (moves an outbox head to `sent`:
`msgs` unchanged, `sent` extended), `clientPropose` (a fresh op appended, `proposeChan`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Basic

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace FrameProof

/-- `Inv` reads a replica's state only through these fields. -/
structure SameCore (σ σ' : RState) : Prop where
  id : σ'.id = σ.id
  inst : σ'.inst = σ.inst
  crt : σ'.crtInstance = σ.crtInstance
  conflicts : σ'.conflicts = σ.conflicts
  exe : σ'.execedUpTo = σ.execedUpTo
  store : σ'.store = σ.store

theorem inv_rep_congr (S : Sys) (R : Nat → RState) (h : ∀ r, SameCore (S.rep r) (R r))
    (hS : Inv0 S) : Inv0 { S with rep := R } := by
  have hid : ∀ r, (R r).id = (S.rep r).id := fun r => (h r).id
  have hinst : ∀ r, (R r).inst = (S.rep r).inst := fun r => (h r).inst
  have hcrt : ∀ r, (R r).crtInstance = (S.rep r).crtInstance := fun r => (h r).crt
  have hcf : ∀ r, (R r).conflicts = (S.rep r).conflicts := fun r => (h r).conflicts
  have hexe : ∀ r, (R r).execedUpTo = (S.rep r).execedUpTo := fun r => (h r).exe
  have hst : ∀ r, (R r).store = (S.rep r).store := fun r => (h r).store
  have hle : ∀ r, sccLe (R r) = sccLe (S.rep r) := by
    intro r; funext a b; simp only [sccLe, hinst]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27⟩ := hS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [Inv.wf, Inv.msgWf, Inv.replyTargets, Inv.noTPA, Inv.ballots, Inv.ballotOwner,
    Inv.oneProposal, Inv.votesFollowProposals, Inv.repliesReportVotes, Inv.prepReplyHighest,
    Inv.lbInv, Inv.agreement, Inv.decidedChosen, Inv.chosenSafe, Inv.depsCover, Inv.witnesses,
    Inv.attrsCover, Inv.execClosed, Inv.execCursor, Inv.execOrder, Inv.execPrefix, Inv.slots,
    Inv.clientOps, Inv.commitMsgs, Inv.pendingKind, Inv.safe, Inv.reports, Sys.safeAcc, Sys.safePh, Sys.blocked, Sys.fastBlocked, Sys.noPA, Sys.fastLive, Sys.lexec, Sys.curSlots, Sys.slotsOn, RState.executed,
    RState.ready, RState.depEdge, sccSort, hle, hid, hinst, hcrt, hcf, hexe, hst] at * <;>
  assumption

theorem deliveredMsg_mono (S S' : Sys) (hdel : S'.delivered = S.delivered)
    (hpre : ∀ fr to, S.sent fr to <+: S'.sent fr to) (a r : Nat) (m : Msg)
    (h : S.deliveredMsg a r m) : S'.deliveredMsg a r m := by
  obtain ⟨n, hn, hd⟩ := h
  obtain ⟨t, ht⟩ := hpre a r
  refine ⟨n, ?_, hdel ▸ hd⟩
  rw [← ht, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hn).1, hn]

/-- A step that changes only `sent`, `outbox` (and `proposeChan`, which `Inv` does not read), with
the same `msgs` and `sent` only extended. -/
theorem inv_sent_congr (S S' : Sys) (hrep : S'.rep = S.rep) (hhist : S'.hist = S.hist)
    (hdel : S'.delivered = S.delivered) (hpend : S'.pending = S.pending) (hops : S'.ops = S.ops)
    (howner : S'.owner = S.owner) (hlog : S'.execLog = S.execLog) (hcur : S'.execCur = S.execCur)
    (hidx : S'.execIdx = S.execIdx) (hgexec : S'.gexec = S.gexec) (hfired : S'.fired = S.fired)
    (hmsgs : ∀ fr to, S'.msgs fr to = S.msgs fr to)
    (hpre : ∀ fr to, S.sent fr to <+: S'.sent fr to) (hS : Inv0 S) : Inv0 S' := by
  have hdm := deliveredMsg_mono S S' hdel hpre
  have hdE : S'.dEdge = S.dEdge := by
    funext x y; simp only [Sys.dEdge, Sys.committedVal, Sys.ev, hhist, hmsgs]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27⟩ := hS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  case refine_1 =>
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := h1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hrep, hmsgs, hdel, hpend, hcur, howner]
    · exact w1
    · exact w2
    · exact w3
    · exact w4
    · exact w5
    · exact w6
    · intro fr to n hn
      exact Nat.lt_of_lt_of_le (w7 fr to n hn) ((hpre fr to).length_le)
    · exact w8
  case refine_11 =>
    intro r hr x w lb hw hlb
    simp only [hrep] at hw
    obtain ⟨a1, a2, a3, a4, a5, ⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩, a8, a9⟩ :=
      h11 r hr x w lb hw hlb
    simp only [Sys.ev, hhist] at *
    refine ⟨a1, a2, a3, a4, a5, ⟨Q, q1, q2, fun a m h => ?_⟩, ⟨Q', q1', q2', fun a h => ?_⟩, a8,
      fun hp => ?_⟩
    · obtain ⟨b1, b2, b3, b4⟩ := q3 a m h; exact ⟨b1, b2, hdm _ _ _ b3, b4⟩
    · obtain ⟨b1, b2, m, b3, b4⟩ := q3' a h; exact ⟨b1, b2, m, hdm _ _ _ b3, b4⟩
    · obtain ⟨c1, c2⟩ := a9 hp
      refine ⟨c1, fun e he => ?_⟩
      obtain ⟨d1, d2, d3⟩ := c2 e he
      refine ⟨d1, d2, ?_⟩
      rcases d3 with ⟨e1, e2⟩ | e3
      · exact Or.inl ⟨e1, hdm _ _ _ e2⟩
      · exact Or.inr e3
  all_goals
    simp only [Inv.wf, Inv.msgWf, Inv.replyTargets, Inv.noTPA, Inv.ballots, Inv.ballotOwner,
      Inv.oneProposal, Inv.votesFollowProposals, Inv.repliesReportVotes, Inv.prepReplyHighest,
      Inv.agreement, Inv.decidedChosen, Inv.chosenSafe, Inv.depsCover, Inv.witnesses,
      Inv.attrsCover, Inv.execClosed, Inv.execCursor, Inv.execOrder, Inv.execPrefix, Inv.slots,
      Inv.clientOps, Inv.commitMsgs, Inv.pendingKind, Inv.safe, Inv.reports, Sys.safeAcc, Sys.safePh, Sys.blocked, Sys.fastBlocked, Sys.noPA, Sys.fastLive, Sys.fastReplies, Sys.slowChosen, Sys.committedVal, Sys.ev,
      Sys.evBefore, Sys.prepReport, Sys.dEdge, Sys.sccOrd, Sys.lexec, Sys.curSlots, Sys.slotOp,
      Sys.kv, hdE, hrep, hhist, hmsgs, hdel, hpend, hops, howner, hlog, hcur, hidx, hgexec,
      hfired] at * <;>
    assumption

end FrameProof

theorem inv0_step_peerOrder' (S : Sys) (i : Nat) (o : List Nat) (hS : Inv0 S) :
    Inv0 { S with rep := upd S.rep i { S.rep i with peerOrder := o } } := by
  refine FrameProof.inv_rep_congr S _ (fun r => ?_) hS
  by_cases h : r = i
  · subst h; simp only [upd_same]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [upd_other _ _ _ _ h]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem inv0_step_beTheLeader' (S : Sys) (i : Nat) (hS : Inv0 S) :
    Inv0 { S with rep := upd S.rep i (hBeTheLeader (S.rep i)) } := by
  refine FrameProof.inv_rep_congr S _ (fun r => ?_) hS
  by_cases h : r = i
  · subst h; simp only [upd_same, hBeTheLeader]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [upd_other _ _ _ _ h]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem inv0_step_flush' (S : Sys) (i to : Nat) (m : Msg) (rest : List Msg) (hS : Inv0 S)
    (h : S.outbox i to = m :: rest) :
    Inv0 { S with sent := upd S.sent i (upd (S.sent i) to (S.sent i to ++ [m])),
                  outbox := upd S.outbox i (upd (S.outbox i) to rest) } := by
  refine FrameProof.inv_sent_congr S _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun fr to' => ?_) (fun fr to' => ?_) hS
  · simp only [Sys.msgs, Sys.intended]
    by_cases h1 : fr = i
    · subst h1; by_cases h2 : to' = to
      · subst h2; simp [h]
      · simp [upd_apply, h2]
    · simp [upd_apply, h1]
  · by_cases h1 : fr = i
    · subst h1; by_cases h2 : to' = to
      · subst h2; simp
      · simp [upd_apply, h2]
    · simp [upd_apply, h1]

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

theorem inv0_step_clientPropose' (S : Sys) (i : Nat) (p : Proposal) (hS : Inv0 S)
    (hp : p.cid ∉ S.ops.map (·.2.cid)) :
    Inv0 { S with ops := S.ops ++ [(i, p)],
                  proposeChan := upd S.proposeChan i (S.proposeChan i ++ [p]) } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27⟩ := hS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  case refine_22 =>
    refine ⟨h22.1, fun x ps hx q hq => ?_⟩
    exact List.mem_append_left _ (h22.2 x ps hx q hq)
  case refine_23 =>
    obtain ⟨c1, c2⟩ := h23
    refine ⟨?_, c2⟩
    simp only [List.map_append, List.map_cons, List.map_nil]
    exact List.nodup_append.mpr ⟨c1, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, by
      intro a ha b hb; simp at hb; subst hb; intro h; exact hp (h ▸ ha)⟩
  all_goals assumption

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
