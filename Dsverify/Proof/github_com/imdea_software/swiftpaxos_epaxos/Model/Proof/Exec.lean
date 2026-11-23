/-
The executor's simple steps: `execBump` (the scan moves `ExecedUpTo[q]` over an executed
instance) and `execSCC` (a component starts; nothing executed yet).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Frame

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace ExecProof

theorem zz_succ (e : w32) : zz (e + 1) = zz e + 1 ∨ zz (e + 1) < 0 := by
  have h1 := BitVec.toInt_lt (x := e)
  have h2 := BitVec.le_toInt (x := e)
  simp only [zz, sint.Z, BitVec.toInt_add, Int.bmod] at *
  simp at *
  split <;> omega

/-- `Inv` reads a replica's state only through these fields; `execedUpTo` only in `wf`. -/
structure SameCoreX (σ σ' : RState) : Prop where
  id : σ'.id = σ.id
  inst : σ'.inst = σ.inst
  crt : σ'.crtInstance = σ.crtInstance
  conflicts : σ'.conflicts = σ.conflicts
  store : σ'.store = σ.store

theorem inv_rep_congr_exe (S : Sys) (R : Nat → RState) (h : ∀ r, SameCoreX (S.rep r) (R r))
    (hexe : ∀ r < nR, ∀ q < nR, ∀ n : Nat, (n : Int) ≤ zz ((R r).execedUpTo q) →
      (R r).executed ⟨q, n⟩)
    (hS : Inv0 S) : Inv0 { S with rep := R } := by
  have hid : ∀ r, (R r).id = (S.rep r).id := fun r => (h r).id
  have hinst : ∀ r, (R r).inst = (S.rep r).inst := fun r => (h r).inst
  have hcrt : ∀ r, (R r).crtInstance = (S.rep r).crtInstance := fun r => (h r).crt
  have hcf : ∀ r, (R r).conflicts = (S.rep r).conflicts := fun r => (h r).conflicts
  have hst : ∀ r, (R r).store = (S.rep r).store := fun r => (h r).store
  have hle : ∀ r, sccLe (R r) = sccLe (S.rep r) := by
    intro r; funext a b; simp only [sccLe, hinst]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27⟩ := hS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  case refine_1 =>
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := h1
    refine ⟨?_, ?_, ?_, ?_, hexe, ?_, ?_, ?_⟩ <;>
    (try simp only [hid, hinst, hcrt, hcf]) <;> assumption
  all_goals
  simp only [Inv.msgWf, Inv.replyTargets, Inv.noTPA, Inv.ballots, Inv.ballotOwner,
    Inv.oneProposal, Inv.votesFollowProposals, Inv.repliesReportVotes, Inv.prepReplyHighest,
    Inv.lbInv, Inv.agreement, Inv.decidedChosen, Inv.chosenSafe, Inv.depsCover, Inv.witnesses,
    Inv.attrsCover, Inv.execClosed, Inv.execCursor, Inv.execOrder, Inv.execPrefix, Inv.slots,
    Inv.clientOps, Inv.commitMsgs, Inv.pendingKind, Inv.safe, Inv.reports, Sys.safeAcc, Sys.safePh, Sys.blocked, Sys.fastBlocked, Sys.noPA, Sys.fastLive, Sys.lexec, Sys.curSlots, Sys.slotsOn,
    RState.executed, RState.ready, RState.depEdge, sccSort, hle, hid, hinst, hcrt, hcf,
    hst] at * <;>
  assumption

end ExecProof

open ExecProof in
theorem inv0_step_execBump' (S : Sys) (i q : Nat) (hS : Inv0 S) (hq : q < nR)
    (he : (S.rep i).executed ⟨q, toN ((S.rep i).execedUpTo q + 1)⟩) :
    Inv0 { S with rep := upd S.rep i (execBump (S.rep i) q) } := by
  refine inv_rep_congr_exe S _ (fun r => ?_) (fun r hr q' hq' n hn => ?_) hS
  · by_cases h : r = i
    · subst h; simp only [upd_same, execBump]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · simp only [upd_other _ _ _ _ h]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · have hold := hS.1.2.2.2.2.1 r hr q' hq'
    by_cases h : r = i
    · subst h
      simp only [upd_same, execBump, RState.executed] at hn ⊢
      by_cases hqq : q' = q
      · subst hqq
        simp only [upd_same] at hn
        rcases zz_succ ((S.rep r).execedUpTo q') with h1 | h1
        · rw [h1] at hn
          rcases Int.lt_or_eq_of_le hn with h2 | h2
          · exact hold n (by omega)
          · have : toN ((S.rep r).execedUpTo q' + 1) = n := by
              have h3 : sint.Z ((S.rep r).execedUpTo q' + 1) = (n : Int) := by
                rw [h2]; exact h1
              simp only [toN, h3]; simp
            rw [← this]; exact he
        · omega
      · simp only [upd_other _ _ _ _ hqq] at hn; exact hold n hn
    · simp only [upd_other _ _ _ _ h] at hn ⊢; exact hold n hn

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

theorem mem_sccSort (σ : RState) (C : List InstId) (x : InstId) : x ∈ sccSort σ C ↔ x ∈ C := by
  simp only [sccSort]; exact List.mem_mergeSort

theorem inv0_step_execSCC' (S : Sys) (i : Nat) (C : List InstId) (hS : Inv0 S) (hi : i < nR)
    (hidle : S.idle i) (hC : sccReady (S.rep i) C) : Inv0 (S.startSCC i C) := by
  obtain ⟨hpi, hci⟩ := hidle
  obtain ⟨c1, c2, c3, c4, c5⟩ := hC
  generalize hS' : S.startSCC i C = S'
  have hrep : S'.rep = S.rep := by subst hS'; rfl
  have hhist : S'.hist = S.hist := by subst hS'; rfl
  have hsent : S'.sent = S.sent := by subst hS'; rfl
  have hob : S'.outbox = S.outbox := by subst hS'; rfl
  have hdel : S'.delivered = S.delivered := by subst hS'; rfl
  have hpend : S'.pending = S.pending := by subst hS'; rfl
  have hops : S'.ops = S.ops := by subst hS'; rfl
  have howner : S'.owner = S.owner := by subst hS'; rfl
  have hlog : S'.execLog = S.execLog := by subst hS'; rfl
  have hgexec : S'.gexec = S.gexec := by subst hS'; rfl
  have hfired : S'.fired = S.fired := by subst hS'; rfl
  have hcur : ∀ r, S'.execCur r = if r = i then sccSort (S.rep i) C else S.execCur r := by
    intro r; subst hS'; simp only [Sys.startSCC, upd_apply]
  have hidx : ∀ r, S'.execIdx r = if r = i then 0 else S.execIdx r := by
    intro r; subst hS'; simp only [Sys.startSCC, upd_apply]
  have hmsgs : S'.msgs = S.msgs := by
    funext fr to; simp only [Sys.msgs, Sys.intended, hsent, hob, hpend]
  have hcs : S'.curSlots = S.curSlots := by
    funext r k
    simp only [Sys.curSlots, hcur, hidx, hrep]
    by_cases h : r = i
    · subst h; simp only [if_true, hci]
      split
      · rfl
      · simp
    · simp only [h, if_false]
  have hlx : S'.lexec = S.lexec := by
    funext r k; simp only [Sys.lexec, hcs, hrep, hlog]
  have hdE : S'.dEdge = S.dEdge := by
    funext x y; simp only [Sys.dEdge, Sys.committedVal, Sys.ev, hhist, hmsgs]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27⟩ := hS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  case refine_1 =>
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := h1
    simp only [Inv.wf, hrep, hmsgs, hdel, hpend, howner, hsent]
    refine ⟨w1, w2, w3, w4, w5, w6, w7, fun r b hb => ?_⟩
    obtain ⟨d1, d2, d3⟩ := w8 r b hb
    refine ⟨d1, ?_, d3⟩
    rw [hcur]; split
    · rename_i h; subst h; rw [hpi] at hb; cases hb
    · exact d2
  case refine_18 =>
    intro r hr
    obtain ⟨e1, e2, e3⟩ := h18 r hr
    simp only [hrep, hlog, Sys.committedVal, Sys.ev, hhist, hmsgs] at *
    refine ⟨e1, e2, fun x w hw hs => ?_⟩
    obtain ⟨f1, f2⟩ := e3 x w hw hs
    refine ⟨f1, fun y hy => ?_⟩
    rcases f2 y hy with g | g
    · exact Or.inl g
    · right; rw [hcur]; split
      · rename_i h; subst h; rw [hci] at g; cases g
      · exact g
  case refine_19 =>
    intro r hr
    simp only [hcur, hidx, hrep]
    by_cases h : r = i
    · subst h
      simp only [if_true]
      have hne : sccSort (S.rep r) C ≠ [] := by
        intro he; apply c1
        obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil C c1
        have := (mem_sccSort (S.rep r) C a).mpr ha; rw [he] at this; cases this
      refine ⟨fun h => absurd h hne, fun _ => ⟨[], C, by simp, c2, by simp,
        fun x hx => c3 x ((mem_sccSort _ _ _).mp hx), c4, c5, fun x w _ _ => Nat.zero_le _⟩⟩
    · simp only [h, if_false]; exact h19 r hr
  all_goals
    simp only [Inv.msgWf, Inv.replyTargets, Inv.noTPA, Inv.ballots, Inv.ballotOwner,
      Inv.oneProposal, Inv.votesFollowProposals, Inv.repliesReportVotes, Inv.prepReplyHighest,
      Inv.lbInv, Inv.agreement, Inv.decidedChosen, Inv.chosenSafe, Inv.depsCover, Inv.witnesses,
      Inv.attrsCover, Inv.execOrder, Inv.execPrefix, Inv.slots, Inv.clientOps, Inv.commitMsgs, Inv.pendingKind, Inv.safe, Inv.reports, Sys.safeAcc, Sys.safePh, Sys.blocked, Sys.fastBlocked, Sys.noPA,
      Sys.fastLive, Sys.fastReplies, Sys.slowChosen, Sys.committedVal, Sys.ev, Sys.evBefore,
      Sys.prepReport, hdE, Sys.sccOrd, Sys.deliveredMsg, Sys.slotOp, Sys.kv, hlx, hrep,
      hhist, hmsgs, hdel, hsent, hpend, hops, howner, hlog, hgexec, hfired] at * <;>
    assumption

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
