/-
`lose`: an outbox message is dropped. `msgs` shrinks; every conjunct reads `msgs` either under a
universal (preserved by shrinking) or through `committedVal`, which `Inv.commitMsgs` makes a
function of the history alone.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Safe

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace LoseProof

/-- Under `commitMsgs`, `committedVal` is witnessed by a commit event. -/
theorem committedVal_ev (S : Sys) (h : Inv.commitMsgs S) (x : InstId) (v : Val) :
    S.committedVal x v ↔ ∃ r b, S.ev r (.commit x b v) := by
  constructor
  · rintro (h1 | ⟨fr, to, m, hm, hx, rfl⟩)
    · exact h1
    · obtain ⟨r, b, he⟩ := h fr to m hm
      simp only [Msg.instOf, Option.some.injEq] at hx
      exact ⟨r, b, hx ▸ he⟩
  · intro h1; exact Or.inl h1

end LoseProof

open LoseProof in
theorem inv0_step_lose' (S : Sys) (i to : Nat) (m : Msg) (rest : List Msg) (hS : Inv0 S)
    (h : S.outbox i to = m :: rest) :
    Inv0 { S with outbox := upd S.outbox i (upd (S.outbox i) to rest) } := by
  generalize hS' : ({ S with outbox := upd S.outbox i (upd (S.outbox i) to rest) } : Sys) = S'
  have hsub : ∀ fr to' m', m' ∈ S'.msgs fr to' → m' ∈ S.msgs fr to' := by
    intro fr to' m' hm
    subst hS'
    simp only [Sys.msgs, Sys.intended, List.mem_append] at hm ⊢
    rcases hm with (h1 | h1) | h1
    · exact Or.inl (Or.inl h1)
    · refine Or.inl (Or.inr ?_)
      by_cases e1 : fr = i
      · subst e1; by_cases e2 : to' = to
        · subst e2; simp only [upd_same] at h1; rw [h]; exact List.mem_cons_of_mem _ h1
        · simp only [upd_same, upd_other _ _ _ _ e2] at h1; exact h1
      · simp only [upd_other _ _ _ _ e1] at h1; exact h1
    · exact Or.inr h1
  have hrep : S'.rep = S.rep := by subst hS'; rfl
  have hhist : S'.hist = S.hist := by subst hS'; rfl
  have hsent : S'.sent = S.sent := by subst hS'; rfl
  have hdel : S'.delivered = S.delivered := by subst hS'; rfl
  have hpend : S'.pending = S.pending := by subst hS'; rfl
  have hops : S'.ops = S.ops := by subst hS'; rfl
  have howner : S'.owner = S.owner := by subst hS'; rfl
  have hlog : S'.execLog = S.execLog := by subst hS'; rfl
  have hcur : S'.execCur = S.execCur := by subst hS'; rfl
  have hidx : S'.execIdx = S.execIdx := by subst hS'; rfl
  have hgexec : S'.gexec = S.gexec := by subst hS'; rfl
  have hfired : S'.fired = S.fired := by subst hS'; rfl
  have hev : S'.ev = S.ev := by funext r e; simp only [Sys.ev, hhist]
  have hevB : S'.evBefore = S.evBefore := by funext r e r' e'; simp only [Sys.evBefore, hhist]
  have hcm : Inv.commitMsgs S' := by
    intro fr to' m' hm; rw [hev]; exact hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 fr to' m' (hsub _ _ _ hm)
  have hcv : S'.committedVal = S.committedVal := by
    funext x v; apply propext
    rw [committedVal_ev S' hcm, committedVal_ev S hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hev]
  have hprep : ∀ r m' e, S'.prepReport r m' e → S.prepReport r m' e := by
    rintro r m' e ⟨he, h1 | h1⟩
    · obtain ⟨to', hm, rfl⟩ := h1
      exact ⟨hev ▸ he, Or.inl ⟨to', hsub _ _ _ hm, rfl⟩⟩
    · exact ⟨hev ▸ he, Or.inr h1⟩
  have hdE : S'.dEdge = S.dEdge := by funext x y; simp only [Sys.dEdge, hcv]
  have hsO : S'.sccOrd = S.sccOrd := by funext x y; simp only [Sys.sccOrd, hcv]
  have hdm : S'.deliveredMsg = S.deliveredMsg := by
    funext a r m'; simp only [Sys.deliveredMsg, hsent, hdel]
  have hsl : S'.slowChosen = S.slowChosen := by funext x b v; simp only [Sys.slowChosen, hev]
  have hfr : S'.fastReplies = S.fastReplies := by funext x v; simp only [Sys.fastReplies, hev]
  have hfl : S'.fastLive = S.fastLive := by funext x v; simp only [Sys.fastLive, hfr, hev, hrep]
  have hlx : S'.lexec = S.lexec := by
    funext r k; simp only [Sys.lexec, Sys.curSlots, hrep, hlog, hcur, hidx]
  have hso : S'.slotOp = S.slotOp := by funext s; simp only [Sys.slotOp, howner]
  have hkv : S'.kv = S.kv := by funext k; simp only [Sys.kv, hgexec]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27⟩ := hS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, hcm, ?_, ?_, ?_⟩
  case refine_1 =>
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := h1
    simp only [Inv.wf, hrep, hdel, hpend, hcur, howner, hsent]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact w1
    · exact w2
    · exact w3
    · exact w4
    · exact w5
    · intro fr to' hne
      apply w6
      intro he
      obtain ⟨m', hm'⟩ := List.exists_mem_of_ne_nil _ hne
      have := hsub _ _ _ hm'; rw [he] at this; simp at this
    · exact w7
    · exact w8
  case refine_2 => intro fr to' m' hm; exact h2 fr to' m' (hsub _ _ _ hm)
  case refine_3 => intro fr to' m' x hm; rw [hrep]; exact h3 fr to' m' x (hsub _ _ _ hm)
  case refine_4 => intro fr to' m' hm; exact h4 fr to' m' (hsub _ _ _ hm)
  case refine_6 =>
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := h6
    simp only [Inv.ballotOwner, hev, hhist, hevB]
    exact ⟨o1, o2, o3, fun r to' m' hm => o4 r to' m' (hsub _ _ _ hm),
      fun r to' m' hm => o5 r to' m' (hsub _ _ _ hm), fun r to' m' hm => o6 r to' m' (hsub _ _ _ hm)⟩
  case refine_9 =>
    obtain ⟨p1, p2, p3⟩ := h9
    simp only [Inv.repliesReportVotes, hevB, hcv, hev]
    refine ⟨fun r m' e hp => p1 r m' e (hprep _ _ _ hp), fun a r m' hm => p2 a r m' (hsub _ _ _ hm),
      fun a r m' hm => ?_⟩
    rcases p3 a r m' (hsub _ _ _ hm) with q | ⟨q1, q2⟩
    · exact Or.inl q
    · exact Or.inr ⟨q1, fun m'' e' hp => q2 m'' e' (hprep _ _ _ hp)⟩
  case refine_25 =>
    exact SafeProof.safe_same S S' (fun r x w h => ⟨w, by rw [hrep]; exact h, rfl, id⟩)
      (fun r e he => by rw [hev]; exact he) (fun r e _ he => by rw [hev] at he; exact he)
      hsub h26
  case refine_26 =>
    exact SafeProof.reports_frame (SafeProof.safeMono_same S S'
      (fun r x w h => ⟨w, by rw [hrep]; exact h, rfl, id⟩)
      (fun r e he => by rw [hev]; exact he) (fun r e _ he => by rw [hev] at he; exact he) hsub)
      hprep (fun r m e x b st u _ h => by rw [hevB] at h; exact h)
      (fun r e _ he => by rw [hev] at he; exact he) h27
  case refine_10 =>
    simp only [Inv.prepReplyHighest, hevB]
    intro r m' e hp; exact h10 r m' e (hprep _ _ _ hp)
  all_goals
    simp only [Inv.ballots, Inv.oneProposal, Inv.votesFollowProposals, Inv.lbInv, Inv.agreement,
      Inv.decidedChosen, Inv.chosenSafe, Inv.depsCover, Inv.witnesses, Inv.attrsCover,
      Inv.execClosed, Inv.execCursor, Inv.execOrder, Inv.execPrefix, Inv.slots, Inv.clientOps,
      Inv.pendingKind, hpend, hrep, hev, hevB, hcv, hdE, hsO, hdm, hsl, hfr, hfl, hlx, hso, hkv, hhist, hops, howner, hlog, hcur,
      hidx, hgexec, hfired] at * <;>
    assumption

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
