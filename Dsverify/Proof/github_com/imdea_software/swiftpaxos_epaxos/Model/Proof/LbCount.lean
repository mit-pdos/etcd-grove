/-
A delivery whose handler only counts a reply in one bookkeeping and outputs nothing
(`inv_deliver_lbc`): the below-quorum branches of `handlePreAcceptReply` (`preAcceptOKs + 1`,
the merged attributes, the reply's ballot/status when it carries a higher vote) and
`handleAcceptReply` (`acceptOKs + 1`). A variant of `PrepReplyProof.inv_deliver_lb` whose
bookkeeping may change the fields `lbInv` counts; the changed obligations are hypotheses.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HPrepReply

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace LbCountProof

open HStepProof HLocal SafeProof AuxProof PrepReplyProof

/-- The bookkeeping fields a counting step keeps: its ballot, commands, proposals, the prepare
phase (over), `preAcceptsSent`; either only `acceptOKs` (and `nacks`) change, or a pre-accepting
bookkeeping counted a PreAcceptReply (`preAcceptOKs ≠ 0` after) and may take the reply's
ballot/attributes/status. -/
def LbCount (lb lb' : LbRec) : Prop :=
  lb'.lastTriedBallot = lb.lastTriedBallot ∧ lb'.cmds = lb.cmds ∧
  lb'.clientProposals = lb.clientProposals ∧ lb'.tryingToPreAccept = lb.tryingToPreAccept ∧
  lb'.preparing = false ∧ lb.preparing = false ∧ lb'.prepareReplies = lb.prepareReplies ∧
  lb'.leaderResponded = lb.leaderResponded ∧ lb'.preAcceptsSent = lb.preAcceptsSent ∧
  zz lb'.ballot ≤ zz lb'.lastTriedBallot ∧
  ((lb'.ballot = lb.ballot ∧ lb'.seq = lb.seq ∧ lb'.deps = lb.deps ∧
      lb'.preAcceptOKs = lb.preAcceptOKs ∧ lb'.allEqual = lb.allEqual ∧ lb'.status = lb.status) ∨
    (isPA lb.status ∧ lb'.preAcceptOKs ≠ W64 0 ∧
      (isPA lb'.status ∨ lb'.status = stACCEPTED ∨ isCommitted lb'.status)))

/-- **A delivery that only counts a reply in one bookkeeping, outputs nothing.** -/
theorem inv_deliver_lbc (S : Sys) (fr i n : Nat) (m : Msg) (σ' : RState) (x : InstId)
    (w : InstRec) (lb lb' : LbRec) (hS : Inv S) (hi : i < nR) (hidle : S.idle i)
    (hm : (S.sent fr i)[n]? = some m) (h : hMsg (S.rep i) m = (σ', []))
    (hσ : σ'.inst = upd (S.rep i).inst x (some { w with lb := some lb' }))
    (hc : σ'.id = (S.rep i).id ∧ σ'.peerOrder = (S.rep i).peerOrder ∧
      σ'.crtInstance = (S.rep i).crtInstance ∧ σ'.conflicts = (S.rep i).conflicts ∧
      σ'.execedUpTo = (S.rep i).execedUpTo ∧ σ'.store = (S.rep i).store)
    (hcls : σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut)
    (hw : (S.rep i).inst x = some w) (hlb : w.lb = some lb) (hk : LbCount lb lb')
    (hdeps : lb'.status ≠ stNONE → depsOk lb'.deps)
    -- `lbInv`'s clauses about the counted replies, in the post-state
    (hpa : isPA lb'.status → lb'.preAcceptOKs ≠ W64 0 →
      lb'.ballot = lb'.lastTriedBallot ∧ ∃ v, S.ev i (.phase1 x lb'.lastTriedBallot v) ∧
        lb'.cmds = some v.cmds)
    (hQ : ∃ Q : List (Nat × PreAcceptReply), (Q.map (·.1)).Nodup ∧
      Q.length = lb'.preAcceptOKs.toNat ∧
      ∀ a m', (a, m') ∈ Q → a < nR ∧ a ≠ i ∧
        (S.deliveredMsg a i (.preAcceptReply m') ∨ a = fr ∧ m = .preAcceptReply m') ∧
        (Msg.preAcceptReply m').instOf = some x ∧ m'.ballot = lb'.lastTriedBallot ∧
        (isPA lb'.status → depsLe m'.deps lb'.deps ∧ zz m'.seq ≤ zz lb'.seq ∧
          (lb'.allEqual = true → m'.seq = lb'.seq ∧ m'.deps = lb'.deps)))
    (hQ' : ∃ Q : List Nat, Q.Nodup ∧ Q.length = lb'.acceptOKs.toNat ∧
      ∀ a ∈ Q, a < nR ∧ a ≠ i ∧ ∃ m' : AcceptReply,
        (S.deliveredMsg a i (.acceptReply m') ∨ a = fr ∧ m = .acceptReply m') ∧
        (Msg.acceptReply m').instOf = some x ∧ m'.ballot = lb'.lastTriedBallot)
    -- a pre-accepting bookkeeping that took an ACCEPTED reply's status holds no accepted record
    (hacc2 : lb'.status = stACCEPTED → isPA lb.status → w.status = stACCEPTED →
      w.bal = lb.lastTriedBallot → False)
    -- `InvPM.aeF` for the new bookkeeping
    (haeF : isPA lb'.status → lb'.allEqual = false → ∃ (a a' : Nat) (m1 m2 : PreAcceptReply),
      Msg.preAcceptReply m1 ∈ S.sent a i ∧ Msg.preAcceptReply m2 ∈ S.sent a' i ∧
      parX m1 = x ∧ parX m2 = x ∧ m1.ballot = lb'.lastTriedBallot ∧
      m2.ballot = lb'.lastTriedBallot ∧ (m1.seq ≠ m2.seq ∨ m1.deps ≠ m2.deps)) :
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
  obtain ⟨kT, kC, kCP, kTPA, kP', kP, -, kLR, kPS, kB, kM⟩ := hk
  have hpaS : isPA lb'.status → isPA lb.status := by
    intro h0; rcases kM with ⟨-, -, -, -, -, e⟩ | ⟨e, -⟩
    · rw [← e]; exact h0
    · exact e
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
        · rw [hl] at hlb2; cases hlb2; exact hdeps hs
      · rcases hl with hl | ⟨rfl, rfl, rfl, hl⟩
        · rw [hl]; exact g6 hq
        · rw [hl]; simp
      · rw [eown]
        rcases hl with hl | ⟨rfl, rfl, rfl, hl⟩
        · rw [hl] at hlb2; exact g7 lb2 ps hlb2 hps
        · rw [hl] at hlb2; cases hlb2; rw [kCP] at hps; exact g7 lb ps hlb hps
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
      obtain ⟨a1, a2, a3, a4, -, -, -, a8, -⟩ := s11 r hr y w1 lb h1 hlb
      obtain ⟨Q, q1, q2, q3⟩ := hQ
      obtain ⟨Q', q1', q2', q3'⟩ := hQ'
      refine ⟨by rw [kT]; exact (hev _ _).mpr a1, kB, by rw [kTPA]; exact a3,
        fun b v hv0 => by rw [kT]; exact a4 b v (hv0.imp (hev _ _).mp (hev _ _).mp),
        fun c1 c2 => ?_, ⟨Q, q1, q2, fun a m' hq => ?_⟩,
        ⟨Q', q1', q2', fun a hq => ?_⟩, fun c1 c2 c3 c4 => ?_, fun hp => ?_⟩
      · obtain ⟨d1, v, d3, d4⟩ := hpa c1 c2
        exact ⟨d1, kP', v, (hev _ _).mpr d3, d4⟩
      · obtain ⟨b1, b2, b3, b4⟩ := q3 a m' hq
        refine ⟨b1, b2, ?_, b4⟩
        rcases b3 with b3 | ⟨rfl, rfl⟩
        · exact hdm _ _ _ b3
        · exact ⟨n, by rw [esent]; exact hm, by rw [edel]; simp⟩
      · obtain ⟨b1, b2, m', b3, b4⟩ := q3' a hq
        refine ⟨b1, b2, m', ?_, b4⟩
        rcases b3 with b3 | ⟨rfl, rfl⟩
        · exact hdm _ _ _ b3
        · exact ⟨n, by rw [esent]; exact hm, by rw [edel]; simp⟩
      · rw [f4] at c2; rw [f2] at c3
        rcases kM with ⟨e1, e2, e3, -, -, e6⟩ | ⟨e1, -⟩
        · rw [e6] at c1; rw [kT] at c3 ⊢; rw [kC, e2, e3]
          obtain ⟨d1, d2⟩ := a8 c1 c2 c3 kP
          exact ⟨(hev _ _).mpr d1, (hev _ _).mpr d2⟩
        · rw [kT] at c3; exact absurd (hacc2 c1 e1 c2 c3) id
      · rw [kP'] at hp; cases hp
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
    · exact ⟨w2, lb2, h2, hl2, by rw [kT]; exact hle⟩
  · intro r hr y w2 lb2 h2 hl2
    obtain ⟨w1, h1, he, hl⟩ := hlbv r y w2 lb2 h2 hl2
    rw [(fld w1 w2 he).2.1]
    rcases hl with hl | ⟨-, -, rfl, rfl⟩
    · exact hA.lastLeBal r hr y w1 lb2 h1 hl
    · rw [kT]; exact hA.lastLeBal r hr y w1 lb h1 hlb
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
    · rw [kT] at hv0
      exact hA.paNoAcc r hr y w1 lb h1 hlb (hpaS hs) v ((hev _ _).mp hv0)
  · intro r hr y w2 lb2 h2 hl2 hs hp hc' hb
    obtain ⟨w1, h1, he, hl⟩ := hlbv r y w2 lb2 h2 hl2
    obtain ⟨-, f2, f3, f4, -⟩ := fld w1 w2 he
    obtain ⟨v, hv0⟩ := hp
    rw [f4] at hc' ⊢; rw [f2] at hb; rw [f3]
    rcases hl with hl | ⟨-, -, rfl, rfl⟩
    · exact hA.paLeader r hr y w1 lb2 h1 hl hs ⟨v, (hev _ _).mp hv0⟩ hc' hb
    · rw [kT] at hv0 hb ⊢
      exact hA.paLeader r hr y w1 lb h1 hlb (hpaS hs) ⟨v, (hev _ _).mp hv0⟩ hc' hb
  · intro r hr y w2 lb2 h2 hl2 hp
    obtain ⟨w1, h1, -, hl⟩ := hlbv r y w2 lb2 h2 hl2
    rcases hl with hl | ⟨-, hy, rfl, rfl⟩
    · obtain ⟨d1, d2, d3, d4, d5⟩ := hA.prepNoProp r hr y w1 lb2 h1 hl hp
      exact ⟨d1, fun v h' => d2 v ((hev _ _).mp h'), fun v h' => d3 v ((hev _ _).mp h'), d4, d5⟩
    · rw [kP'] at hp; cases hp
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
      · rw [kT]; exact hlt
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
      · rw [kC] at hc'; exact m3 r hr y w1 lb cs h1 hlb hc'
  · intro fr' to m' hm'
    exact (hev _ _).mpr (hA.prSent fr' to m' (by rw [emsgs] at hm'; exact hm'))
  · intro r m' he hs; exact hA.selfOk r m' ((hev _ _).mp he) hs
  · intro r m' he; exact hA.selfRaw r m' ((hev _ _).mp he)
  · -- pm: other bookkeepings keep what `InvPM` reads; the counted one by `LbCount`
    have hP := hA.pm
    have hmono : ∀ r e, S.ev r e → S'.ev r e := fun r e h => (hev r e).mpr h
    have hold' : ∀ r e, S'.ev r e → S.ev r e := fun r e h => (hev r e).mp h
    have hmsg : ∀ fr' to m', m' ∈ S'.msgs fr' to → m' ∈ S.msgs fr' to :=
      fun fr' to m' h => by rw [emsgs] at h; exact h
    have hsnt : ∀ fr' to m', m' ∈ S.sent fr' to → m' ∈ S'.sent fr' to :=
      fun fr' to m' h => by rw [esent]; exact h
    have hcv' : ∀ y u, S.committedVal y u → S'.committedVal y u := fun y u h => (hcv y u).mpr h
    have hbalR : ∀ r y w1, (S.rep r).inst y = some w1 →
        ∃ w', (S'.rep r).inst y = some w' ∧ zz w1.bal ≤ zz w'.bal := by
      intro r y w1 h1
      obtain ⟨w2, h2, he, -⟩ := hv' r y w1 h1
      exact ⟨w2, h2, by rw [(fld w1 w2 he).2.1]; exact Int.le_refl _⟩
    exact {
      arOk := PMProof.arOk_frame hP (fun a r m h => hmsg _ _ _ h) (fun r y b v h => hold' _ _ h)
        (fun q y b v h => Or.inl (hold' _ _ h)) hmono hcv' hbalR
      commitProp := PMProof.commitProp_frame hP (fun r y c u h => hold' _ _ h) hmono
      commitMsgProp := PMProof.commitMsgProp_frame hP (fun fr to m h => hmsg _ _ _ h) hmono
      lbProp := by
        intro r hr y w2 lb2 h2 hl2 hs ⟨v, hv0⟩
        obtain ⟨w1, h1, -, hl⟩ := hlbv r y w2 lb2 h2 hl2
        rcases hl with hl | ⟨-, -, rfl, rfl⟩
        · exact PMProof.propAt_mono hmono (hP.lbProp r hr y w1 lb2 h1 hl hs ⟨v, hold' _ _ hv0⟩)
        · rcases kM with ⟨e1, -, -, -, -, e6⟩ | ⟨e1, -⟩
          · rw [e1, kC]
            exact PMProof.propAt_mono hmono (hP.lbProp r hr y _ lb h1 hlb (by rw [← e6]; exact hs)
              ⟨v, by rw [← kT]; exact hold' _ _ hv0⟩)
          · rw [kT] at hv0
            exact absurd (hold' _ _ hv0) (hA.paNoAcc r hr y _ lb h1 hlb e1 v)
      parCom := PMProof.parCom_frame hP (fun a r m h => hmsg _ _ _ h) hmono
      parSt := PMProof.parSt_frame hP (fun a r m h => hmsg _ _ _ h) hsnt
      paFresh := by
        intro r hr y w2 lb2 h2 hl2 hs h0 ⟨v, hv0⟩
        obtain ⟨w1, h1, -, hl⟩ := hlbv r y w2 lb2 h2 hl2
        rcases hl with hl | ⟨-, -, rfl, rfl⟩
        · exact hP.paFresh r hr y w1 lb2 h1 hl hs h0 ⟨v, hold' _ _ hv0⟩
        · rcases kM with ⟨e1, -, -, e4, -, e6⟩ | ⟨-, e2, -⟩
          · rw [e1]
            exact hP.paFresh r hr y _ lb h1 hlb (by rw [← e6]; exact hs) (by rw [← e4]; exact h0)
              ⟨v, by rw [← kT]; exact hold' _ _ hv0⟩
          · exact absurd h0 e2
      paCmds := by
        intro r hr y w2 lb2 h2 hl2 hs v hv0
        obtain ⟨w1, h1, -, hl⟩ := hlbv r y w2 lb2 h2 hl2
        rcases hl with hl | ⟨-, -, rfl, rfl⟩
        · exact hP.paCmds r hr y w1 lb2 h1 hl hs v (hold' _ _ hv0)
        · rw [kC]
          exact hP.paCmds r hr y _ lb h1 hlb (hpaS hs) v (by rw [← kT]; exact hold' _ _ hv0)
      paSent := PMProof.ps_frame hP (fun y w2 lb2 h2 hl2 => by
          obtain ⟨w1, h1, -, hl⟩ := hlbv _ y w2 lb2 h2 hl2
          rcases hl with hl | ⟨-, -, rfl, rfl⟩
          · exact ⟨w1, lb2, h1, hl, rfl, rfl⟩
          · exact ⟨_, lb, h1, hlb, kT, kPS⟩)
        (fun r b h _ => by rw [epend] at h; exact h)
        (fun y a h => by rw [esent, show S'.outbox = S.outbox by rw [← hS']] at h; exact h)
      pendPA := fun r b h => hP.pendPA r b (by rw [epend] at h; exact h)
      paVoteMsg := PMProof.paVoteMsg_frame hP (fun r y b st v h => hold' _ _ h) hsnt
      parNoPA := PMProof.parNoPA_frame hP (fun a r m h => hmsg _ _ _ h)
        (fun r y b st v h => hold' _ _ h)
      aeF := by
        intro r hr y w2 lb2 h2 hl2 hs hae
        obtain ⟨w1, h1, -, hl⟩ := hlbv r y w2 lb2 h2 hl2
        rcases hl with hl | ⟨rfl, rfl, rfl, rfl⟩
        · obtain ⟨a, a', m1, m2, d1, d2, d3, d4, d5, d6, d7⟩ := hP.aeF r hr y w1 lb2 h1 hl hs hae
          exact ⟨a, a', m1, m2, hsnt _ _ _ d1, hsnt _ _ _ d2, d3, d4, d5, d6, d7⟩
        · obtain ⟨a, a', m1, m2, d1, d2, d3, d4, d5, d6, d7⟩ := haeF hs hae
          exact ⟨a, a', m1, m2, hsnt _ _ _ d1, hsnt _ _ _ d2, d3, d4, d5, d6, d7⟩
      repLead := PMProof.repLead_frame hP (fun r m e h => (hprepR r m e).mp h) hbalR
      paGe := PMProof.paGe_frame hP (fun r y b st v h => hold' _ _ h) (fun r y b v h => hold' _ _ h)
      phAttrs := PMProof.phAttrs_frame hP (fun r y b v h => hold' _ _ h) hmono
      accWit := PMProof.accWit_frame hP (fun r y b v h => hold' _ _ h) hmono hcv'
      accVote := PMProof.accVote_frame hP (fun r y b v h => hold' _ _ h) hmono
      cmdSafe := CmdSafeProof.cmdSafe_frame hP hsafeM (fun r y b v h => hold' _ _ h)
      accSup := CmdSafeProof.accSup_frame hP hmono (fun r y b v h => hold' _ _ h) }
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
    · rw [hl] at hl2; cases hl2; exact ⟨w1, lb, h1, by rw [h5]; exact hlb, by rw [← kCP]; exact hne⟩

end LbCountProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
