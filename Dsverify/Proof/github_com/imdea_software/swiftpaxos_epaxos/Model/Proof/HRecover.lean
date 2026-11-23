/-
`startRecoveryForInstance` (`hRecover`, `Step.recover`): the law `inv_step_recover`. Cases: the
instance is committed (nothing happens); the replica has no record of it (a default NONE record
is created first: `inv_default_rec`); the ballot would overflow (nothing more); the recovery
starts (`inv_recover_start`: a fresh ballot `n` made, the record's `bal` raised to `n`, a fresh
preparing bookkeeping holding the own report, the events `makeBallot x n` and `selfReply`, and
the Prepare broadcast left pending).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.RecPhase1
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Decide

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace RecoverProof

open HStepProof HLocal SafeProof AuxProof RecCommitProof RecAcceptProof

/-- A step of an idle replica is a handler step. -/
theorem hs_apply (S : Sys) (i : Nat) (σ : RState) (os : List Out) (hidle : S.idle i) :
    HS S (S.applyStep i (σ, os)) i σ (evsOf os) (sendsOf os) (pendFold os none) := by
  have hp : S.pending i = none := hidle.1
  refine ⟨by simp, by rw [hist_applyStep], fun fr' to => ?_, by simp, ?_, ?_, ?_, by simp,
    by simp, by simp, by simp, by simp, by simp, by simp⟩
  · rw [msgs_applyStep _ _ _ _ hp]
  · funext r; simp only [Sys.applyStep_pending, upd_apply]; split <;> simp_all
  · intro d hd'; simp only [Sys.applyStep_delivered]; exact hd'
  · intro fr' to n' hd'; simp only [Sys.applyStep_delivered] at hd'; exact Or.inl hd'

/-- (`InvPM`) A handler step of an idle replica appends its direct sends to its outbox. -/
private theorem pmr_outbox_eq {S S' : Sys} {i : Nat} {σ' : RState} {E : List Event}
    {snd : Nat → List Msg} {pend : Option Bcast} (hH : HS S S' i σ' E snd pend)
    (hidle : S.pending i = none) (fr to : Nat) :
    S'.outbox fr to = S.outbox fr to ++ (if fr = i then snd to else []) := by
  have h1 := hH.msgs fr to
  have hi : S'.intended fr to = if fr = i then intendedOf pend to else S.intended fr to := by
    unfold Sys.intended
    rw [hH.pending]
    by_cases hf : fr = i
    · subst hf; simp only [upd_same, if_true]; rfl
    · simp only [upd_other _ _ _ _ hf, hf, if_false]
  unfold Sys.msgs at h1
  rw [hH.sent, hi] at h1
  by_cases hf : fr = i
  · subst hf
    have h0 : S.intended fr to = [] := by unfold Sys.intended; rw [hidle]
    simp only [if_true, h0, List.append_nil] at h1 ⊢
    have h2 : S.sent fr to ++ (S'.outbox fr to ++ intendedOf pend to) =
        S.sent fr to ++ ((S.outbox fr to ++ snd to) ++ intendedOf pend to) := by
      simpa only [List.append_assoc] using h1
    exact List.append_cancel_right (List.append_cancel_left h2)
  · simp only [hf, if_false, List.append_nil] at h1 ⊢
    have h2 : S.sent fr to ++ (S'.outbox fr to ++ S.intended fr to) =
        S.sent fr to ++ (S.outbox fr to ++ S.intended fr to) := by
      simpa only [List.append_assoc] using h1
    exact List.append_cancel_right (List.append_cancel_left h2)

/-- (`InvPM`) A handler step of an idle replica without direct sends keeps the thrifty
broadcasts' recipients. -/
private theorem pmr_rcpt {S S' : Sys} {i : Nat} {σ' : RState} {E : List Event}
    {pend : Option Bcast} (hH : HS S S' i σ' E (fun _ => []) pend)
    (hidle : S.pending i = none) (fr to : Nat) :
    S'.sent fr to ++ S'.outbox fr to = S.sent fr to ++ S.outbox fr to := by
  rw [hH.sent, pmr_outbox_eq hH hidle]; split <;> simp

/-- (`InvPM`) `paSent` after a handler step of an idle replica without direct sends whose
pending broadcast is not a tracking one, when the leaders' bookkeepings at their initial ballot
are old ones. -/
private theorem pmr_paSent {S S' : Sys} {i : Nat} {σ' : RState} {E : List Event}
    {pend : Option Bcast} (hP : InvPM S) (hH : HS S S' i σ' E (fun _ => []) pend)
    (hidle : S.pending i = none) (hpend : ∀ b, pend = some b → b.trackPA = false)
    (hlb : ∀ x w' lb', (S'.rep x.q).inst x = some w' → w'.lb = some lb' →
      lb'.lastTriedBallot = initBal x → (S.rep x.q).inst x = some w') :
    ∀ x w lb, x.q < nR → (S'.rep x.q).inst x = some w → w.lb = some lb →
      lb.lastTriedBallot = initBal x →
      lb.preAcceptsSent.toNat ≤ 2 * fR - 1 ∧
      (∀ b, S'.pending x.q = some b → b.x = x → b.trackPA = true →
        b.m.isPAat x (initBal x) = true ∧ b.sent = lb.preAcceptsSent.toNat ∧ b.need ≤ 2 * fR - 1) ∧
      (S'.paRcpt x).length ≤ lb.preAcceptsSent.toNat := by
  intro x w' lb' hq hw' hlb' hlt
  obtain ⟨h1, h2, h3⟩ := hP.paSent x w' lb' hq (hlb x w' lb' hw' hlb' hlt) hlb' hlt
  refine ⟨h1, fun b hb hbx ht => ?_, ?_⟩
  · rw [hH.pending] at hb
    by_cases hr : x.q = i
    · rw [hr, upd_same] at hb; rw [hpend b hb] at ht; cases ht
    · rw [upd_other _ _ _ _ hr] at hb; exact h2 b hb hbx ht
  · have he : S'.paRcpt x = S.paRcpt x := by
      unfold Sys.paRcpt; simp only [pmr_rcpt hH hidle]
    rw [he]; exact h3

/-- **Creating a default record keeps the invariant** (for an instance of another row, in range,
that the replica does not hold yet). -/
theorem inv_default_rec (S : Sys) (i : Nat) (x : InstId) (hS : Inv S) (hi : i < nR)
    (hidle : S.idle i) (hq : x.q < nR) (hx : (x.i : Int) ≤ zz ((S.rep i).crtInstance x.q))
    (hnone : (S.rep i).inst x = none) :
    Inv (S.applyStep i ((S.rep i).setInst x (newInstanceDefault x), [])) := by
  have hH := hs_apply S i ((S.rep i).setInst x (newInstanceDefault x)) [] hidle
  generalize hS' : S.applyStep i ((S.rep i).setInst x (newInstanceDefault x), []) = S' at hH
  have hE : evsOf ([] : List Out) = [] := rfl
  have hsd : sendsOf ([] : List Out) = fun _ => [] := by funext to; rfl
  have hpd : pendFold ([] : List Out) none = none := rfl
  rw [hE, hsd, hpd] at hH
  generalize hw'd : newInstanceDefault x = w' at hH
  have hA := hS.2
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, s21, s22, s23, s24, s25, s26, s27⟩ := hS.1
  have hxi : x.i + 1 < MAX_INSTANCE := by
    have h1 := hA.crtOwn i hi x.q hq
    have h2 := s1.2.2.1 x.q hq x.q hq
    simp only [toN, zz] at h1 h2 hx ⊢; omega
  have hxqi : x.q ≠ i := by
    intro h
    obtain ⟨w, lb, hw, -⟩ := hA.ownRow x.q hq x.i (by rw [h] at hx ⊢; exact hx)
    rw [h, show (⟨i, x.i⟩ : InstId) = x by rw [← h]] at hw
    rw [hnone] at hw; cases hw
  have hev : ∀ r e, S'.ev r e ↔ S.ev r e := by intro r e; rw [hH.ev_iff]; simp
  have hevB : ∀ r e r' e', S'.evBefore r e r' e' ↔ S.evBefore r e r' e' := by
    intro r e r' e'; simp only [Sys.evBefore, hH.hist, List.map_nil, List.append_nil]
  have hmsgs : ∀ fr to m', m' ∈ S'.msgs fr to ↔ m' ∈ S.msgs fr to := by
    intro fr to m'; rw [hH.mem_msgs]; simp [intendedOf]
  have hcv' : ∀ y u, S'.committedVal y u ↔ S.committedVal y u := by
    intro y u; simp only [Sys.committedVal, hev, hmsgs]
  have hprepR : ∀ r m' e, S'.prepReport r m' e ↔ S.prepReport r m' e := by
    intro r m' e; simp only [Sys.prepReport, hev, hmsgs]
  have hcnt : ∀ fr to p, S'.cnt fr to p = S.cnt fr to p := by
    intro fr to p; rw [hH.cnt_eq]; split <;> simp [intendedOf]
  have hall : ∀ fr to p, S.allDeliv fr to p → S'.allDeliv fr to p :=
    fun fr to p h => hH.allDeliv_old h (fun _ m hm => by simp [intendedOf] at hm)
  have hdm : ∀ a r m', S.deliveredMsg a r m' → S'.deliveredMsg a r m' :=
    fun a r m' h => hH.deliveredMsg_old h
  have hrep : ∀ r y, (S'.rep r).inst y =
      if r = i ∧ y = x then some w' else (S.rep r).inst y := by
    intro r y
    rw [hH.rep]
    by_cases hr : r = i
    · subst hr; simp only [upd_same, RState.setInst, upd_apply, true_and]
    · simp [upd_other _ _ _ _ hr, hr]
  have R1 : ∀ r y w2, (S'.rep r).inst y = some w2 →
      (i = r ∧ x = y ∧ w' = w2) ∨ ((S.rep r).inst y = some w2 ∧ ¬ (r = i ∧ y = x)) := by
    intro r y w2 h; rw [hrep] at h; split at h
    · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; simp only [Option.some.injEq] at h
      exact Or.inl ⟨rfl, rfl, h⟩
    · rename_i hc; exact Or.inr ⟨h, hc⟩
  have R2 : ∀ r y w1, (S.rep r).inst y = some w1 → (S'.rep r).inst y = some w1 := by
    intro r y w1 h
    rw [hrep, if_neg]; · exact h
    rintro ⟨rfl, rfl⟩; rw [hnone] at h; cases h
  have R3 : (S'.rep i).inst x = some w' := by rw [hrep]; simp
  have hfl : ∀ r, (S'.rep r).id = (S.rep r).id ∧ (S'.rep r).peerOrder = (S.rep r).peerOrder ∧
      (S'.rep r).crtInstance = (S.rep r).crtInstance ∧
      (S'.rep r).conflicts = (S.rep r).conflicts ∧
      (S'.rep r).execedUpTo = (S.rep r).execedUpTo ∧ (S'.rep r).store = (S.rep r).store := by
    intro r
    by_cases hr : r = i
    · subst hr; rw [hH.rep_self]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [hH.rep_other hr]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have W : w'.cmds = none ∧ w'.bal = W32 (-1) ∧ w'.vbal = W32 (-1) ∧ w'.status = stNONE ∧
      w'.lb = none ∧ w'.id = x := by
    rw [← hw'd]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨W1, W2, W3, W4, W5, W6⟩ := W
  have hnovote : ∀ b st u, ¬ S.ev i (.vote x b st u) := by
    intro b st u h
    obtain ⟨w1, h1, -⟩ := s5.2 i hi x b st u h
    rw [hnone] at h1; cases h1
  have hex : ∀ r y, (S'.rep r).executed y ↔ (S.rep r).executed y := by
    intro r y
    constructor
    · rintro ⟨w2, h2, hs⟩
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · rw [W4] at hs; cases hs
      · exact ⟨w2, h, hs⟩
    · rintro ⟨w1, h1, hs⟩; exact ⟨w1, R2 r y w1 h1, hs⟩
  have hsafeM : SafeMono S S' := by
    refine safeMono_same S S' (fun r y w1 h1 => ⟨w1, R2 r y w1 h1, rfl, id⟩)
      (fun r e h => (hev r e).mpr h) (fun r e _ h => (hev r e).mp h)
      (fun fr to m h => (hmsgs _ _ _).mp h)
  have hsafe : Inv.safe S' := safe_frame hsafeM s26 (fun r y b v h => (hev _ _).mp h)
    (fun r y b v h => (hev _ _).mp h)
  have hhist : S'.hist = S.hist := by rw [hH.hist]; simp
  have hmsgsE : S'.msgs = S.msgs := by
    funext fr to; rw [hH.msgs]; split <;> simp [intendedOf]
  have hdE : S'.dEdge = S.dEdge := by funext y z; simp only [Sys.dEdge, hcv']
  have hsO : S'.sccOrd = S.sccOrd := by funext y z; simp only [Sys.sccOrd, hcv']
  have hslot : ∀ r, Sys.slotsOn (S'.rep r) (S.execLog r) = Sys.slotsOn (S.rep r) (S.execLog r) := by
    intro r; funext k
    by_cases hr : r = i
    · subst hr
      refine RecCommitProof.slotsOn_congr _ _ _ _ (fun y hy => ?_)
      rw [hrep, if_neg]; rintro ⟨-, hyx⟩; rw [hyx] at hy
      obtain ⟨w1, h1, -⟩ := ((s18 r hi).2.1 x).mp hy
      rw [hnone] at h1; cases h1
    · rw [hH.rep_other hr]
  have hlx : ∀ r k, S'.lexec r k = S.lexec r k := by
    intro r k
    have hcur : S'.curSlots r k = S.curSlots r k := by
      by_cases hr : r = i
      · subst hr; simp only [Sys.curSlots, hH.execCur, hidle.2]
      · simp only [Sys.curSlots, hH.execCur, hH.execIdx, hH.rep_other hr]
    simp only [Sys.lexec, hcur, hH.execLog, hslot]
  have hwf : Inv.wf S' := by
    obtain ⟨w1', w2', w3', w4', w5', w6', w7', w8'⟩ := s1
    refine ⟨fun r hr => by rw [(hfl r).1]; exact w1' r hr, fun r hr y w2 h2 => ?_,
      fun r hr q hq => by rw [(hfl r).2.2.1]; exact w3' r hr q hq,
      fun r hr q k p hk => ?_, fun r hr q hq n' hn' => ?_, fun fr' to hne => ?_,
      fun fr' to n' hn' => ?_, fun r b' hb' => ?_⟩
    · rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, -⟩
      · refine ⟨W6, hq, hxi, fun hs => absurd W4 hs, fun lb2 hl2 => (by rw [W5] at hl2; cases hl2),
          fun h' => absurd h' hxqi, fun lb2 ps hl2 => (by rw [W5] at hl2; cases hl2)⟩
      · obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := w2' r hr y w2 h
        exact ⟨g1, g2, g3, g4, g5, g6, fun lb ps hlb hps => by rw [hH.owner]; exact g7 lb ps hlb hps⟩
    · rw [(hfl r).2.2.2.1] at hk
      obtain ⟨k1', k2', k3'⟩ := w4' r hr q k p hk
      have grow : ∀ y, (S.rep r).inst y ≠ none → (S'.rep r).inst y ≠ none := by
        intro y hy hy'
        obtain ⟨w1, h1⟩ := Option.ne_none_iff_exists'.mp hy
        rw [R2 r y w1 h1] at hy'; cases hy'
      exact ⟨k1', fun h0 => grow _ (k2' h0), fun h0 => grow _ (k3' h0)⟩
    · rw [(hfl r).2.2.2.2.1] at hn'
      exact (hex r _).mpr (w5' r hr q hq n' hn')
    · rw [hmsgsE] at hne; exact w6' fr' to hne
    · rcases hH.delOk fr' to n' hn' with h | h
      · rw [hH.sent]; exact w7' fr' to n' h
      · rw [hH.sent]; exact h
    · rw [hH.pending] at hb'
      by_cases hr : r = i
      · subst hr; simp at hb'
      · rw [upd_other _ _ _ _ hr] at hb'
        obtain ⟨d1, d2, d3, d4, d5, d6, w1, lb1, h1, hl1⟩ := w8' r b' hb'
        exact ⟨d1, by rw [hH.execCur]; exact d2, d3, d4, d5, d6, w1, lb1, R2 r _ w1 h1, hl1⟩
  have hbal : Inv.ballots S' := by
    refine ⟨fun r hr y w2 h2 => ?_, fun r hr y c st u he => ?_⟩
    · rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · rw [W2, W3]; exact Int.le_refl _
      · exact s5.1 r hr y w2 h
    · obtain ⟨w1, h1, hle⟩ := s5.2 r hr y c st u ((hev _ _).mp he)
      exact ⟨w1, R2 r y w1 h1, hle⟩
  have hlbI : Inv.lbInv S' := by
    intro r hr y w2 lb2 h2 hl2
    rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, -⟩
    · rw [W5] at hl2; cases hl2
    · obtain ⟨a1, a2, a3, a4, a5, ⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩, a8, a9⟩ :=
        s11 r hr y w2 lb2 h hl2
      refine ⟨(hev _ _).mpr a1, a2, a3,
        fun c u hv0 => a4 c u (hv0.imp (hev _ _).mp (hev _ _).mp),
        fun c1 c2 => ?_, ⟨Q, q1, q2, fun a m' hq => ?_⟩, ⟨Q', q1', q2', fun a hq => ?_⟩,
        fun c1 c2 c3 c4 => ?_, fun hp => ?_⟩
      · obtain ⟨d1, d2, u, d3, d4⟩ := a5 c1 c2; exact ⟨d1, d2, u, (hev _ _).mpr d3, d4⟩
      · obtain ⟨b1, b2, b3, b4⟩ := q3 a m' hq; exact ⟨b1, b2, hdm _ _ _ b3, b4⟩
      · obtain ⟨b1, b2, m', b3, b4⟩ := q3' a hq; exact ⟨b1, b2, m', hdm _ _ _ b3, b4⟩
      · obtain ⟨d1, d2⟩ := a8 c1 c2 c3 c4; exact ⟨(hev _ _).mpr d1, (hev _ _).mpr d2⟩
      · obtain ⟨c1, c2⟩ := a9 hp
        refine ⟨c1, fun e he' => ?_⟩
        obtain ⟨d1, d2, d3⟩ := c2 e he'
        refine ⟨d1, d2, ?_⟩
        rcases d3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact Or.inl ⟨e1, hdm _ _ _ e2⟩
        · exact Or.inr ⟨e1, (hev _ _).mpr e2⟩
  have hagr : Inv.agreement S' := by
    refine ⟨fun y u u' h1 h2 => s12.1 y u u' ((hcv' _ _).mp h1) ((hcv' _ _).mp h2),
      fun r hr y w2 h2 hc' => ?_⟩
    rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
    · rw [W4] at hc'; rcases hc' with h | h <;> cases h
    · obtain ⟨d1, d2⟩ := s12.2 r hr y w2 h hc'
      exact ⟨d1, (hcv' _ _).mpr d2⟩
  have hexec : Inv.execClosed S' ∧ Inv.execCursor S' ∧ Inv.execOrder S' ∧
      Inv.execPrefix S' := by
    refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_⟩
    · obtain ⟨e1, e2, e3⟩ := s18 r hr
      refine ⟨by rw [hH.execLog]; exact e1, fun y => by rw [hH.execLog, hex]; exact e2 y,
        fun y w2 h2 hs => ?_⟩
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, hne⟩
      · rw [W4] at hs; cases hs
      obtain ⟨d1, d2⟩ := e3 y w2 h hs
      refine ⟨(hcv' _ _).mpr d1, fun z hz => ?_⟩
      rw [hex, hH.execCur]
      apply d2 z
      obtain ⟨w3, h3, hq', hz'⟩ := hz
      rw [hrep, if_neg hne] at h3
      exact ⟨w3, h3, hq', hz'⟩
    · by_cases hri : r = i
      · subst r
        have hc0 : S.execCur i = [] := hidle.2
        rw [hH.execCur, hH.execIdx]
        exact ⟨fun _ => (s19 i hr).1 hc0, fun h => absurd hc0 h⟩
      · rw [hH.rep_other hri, hH.execCur, hH.execIdx]; exact s19 r hr
    · intro r hr a c y z hac h1 h2 ht
      rw [hH.execLog] at h1 h2; rw [hdE] at ht ⊢; rw [hsO]
      exact s20 r hr a c y z hac h1 h2 ht
    · obtain ⟨p1, p2, p3⟩ := s21
      refine ⟨fun r hr k => ?_, fun r hr k => ?_, fun r hr k pre e post h => ?_⟩
      · rw [hlx, hH.gexec]; exact p1 r hr k
      · rw [hlx, (hfl r).2.2.2.2.2]; exact p2 r hr k
      · rw [hlx] at h; rw [hH.gexec]; exact p3 r hr k pre e post h
  have hrepo : Inv.reports S' := reports_frame hsafeM (fun r m e h => (hprepR r m e).mp h)
    (fun r m e y b st u _ h => (hevB _ _ _ _).mp h) (fun r e _ h => (hev r e).mp h) s27
  have hsimple : Inv.msgWf S' ∧ Inv.replyTargets S' ∧ Inv.noTPA S' ∧ Inv.ballotOwner S' ∧
      Inv.oneProposal S' ∧ Inv.votesFollowProposals S' ∧ Inv.repliesReportVotes S' ∧
      Inv.prepReplyHighest S' ∧ Inv.decidedChosen S' ∧ Inv.depsCover S' ∧ Inv.witnesses S' ∧
      Inv.attrsCover S' ∧ Inv.slots S' ∧ Inv.clientOps S' ∧ Inv.commitMsgs S' ∧
      Inv.pendingKind S' := by
    have hso : S'.slotOp = S.slotOp := by funext s; simp only [Sys.slotOp, hH.owner]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro fr to m h; rw [hmsgsE] at h; exact s2 fr to m h
    · intro fr to m y h hy hk
      rw [hmsgsE] at h
      obtain ⟨w1, lb1, h1, hl1⟩ := s3 fr to m y h hy hk
      exact ⟨w1, lb1, R2 to y w1 h1, hl1⟩
    · intro fr to m h; rw [hmsgsE] at h; exact s4 fr to m h
    all_goals
      simp only [Inv.ballotOwner, Inv.oneProposal, Inv.votesFollowProposals,
        Inv.repliesReportVotes, Inv.prepReplyHighest, Inv.decidedChosen, Inv.depsCover,
        Inv.witnesses, Inv.attrsCover, Inv.slots, Inv.clientOps, Inv.commitMsgs, Inv.pendingKind,
        Sys.committedVal, Sys.ev, Sys.evBefore, Sys.prepReport, Sys.slowChosen, Sys.fastReplies,
        hhist, hmsgsE, hH.owner, hH.ops, hH.gexec, hH.fired, hso, hH.pending] at *
    · exact s6
    · exact s7
    · exact s8
    · exact s9
    · exact s10
    · exact s13
    · exact s15
    · exact s16
    · exact s17
    · exact s22
    · exact s23
    · exact s24
    · intro r b' hb'
      by_cases hr : r = i
      · subst hr; simp at hb'
      · rw [upd_other _ _ _ _ hr] at hb'; exact s25 r b' hb'
  obtain ⟨n2, n3, n4, n6, n7, n8, n9, n10, n13, n15, n16, n17, n22, n23, n24, n25⟩ := hsimple
  refine ⟨⟨hwf, n2, n3, n4, hbal, n6, n7, n8, n9, n10, hlbI, hagr, n13,
    chosenSafe_of_safe _ hwf hbal n6 n8 hsafe, n15, n16, n17, hexec.1, hexec.2.1, hexec.2.2.1,
    hexec.2.2.2, n22, n23, n24, n25, hsafe, hrepo⟩, ?_⟩
  have hlbv : ∀ r y w2 lb2, (S'.rep r).inst y = some w2 → w2.lb = some lb2 →
      (S.rep r).inst y = some w2 := by
    intro r y w2 lb2 h2 hl2
    rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
    · rw [W5] at hl2; cases hl2
    · exact h
  have hnotlb : ∀ r y, (S.rep r).inst y = none → ∀ w1 lb1, (S'.rep r).inst y = some w1 →
      w1.lb = some lb1 → False := by
    intro r y hn w1 lb1 h1 hl1; rw [hlbv r y w1 lb1 h1 hl1] at hn; cases hn
  exact {
    stRange := fun r hr y w2 h2 => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · exact Or.inl W4
      · exact hA.stRange r hr y w2 h
    cmdsSome := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · exact absurd W4 hs
      · exact hA.cmdsSome r hr y w2 h hs
    noneRec := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, -⟩
      · exact ⟨by rw [W3]; decide, fun b st u hv => hnovote b st u ((hev _ _).mp hv)⟩
      · obtain ⟨d1, d2⟩ := hA.noneRec r hr y w2 h hs
        exact ⟨d1, fun c st u hv0 => d2 c st u ((hev _ _).mp hv0)⟩
    vbalNonneg := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · exact absurd W4 hs
      · exact hA.vbalNonneg r hr y w2 h hs
    votesLe := fun r hr y w2 h2 c st u hv0 => by
      rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, -⟩
      · exact absurd ((hev _ _).mp hv0) (hnovote c st u)
      · exact hA.votesLe r hr y w2 h c st u ((hev _ _).mp hv0)
    recVote := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · rw [W4] at hs; rcases hs with (h | h) | h <;> cases h
      · exact (hev _ _).mpr (hA.recVote r hr y w2 h hs)
    accKeep := fun r hr y w2 h2 c u hv0 hle => by
      rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, -⟩
      · exact absurd ((hev _ _).mp hv0) (hnovote c _ u)
      · exact hA.accKeep r hr y w2 h c u ((hev _ _).mp hv0) hle
    recCommit := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · rw [W4] at hs; rcases hs with h | h <;> cases h
      · obtain ⟨c, u, d1, d2⟩ := hA.recCommit r hr y w2 h hs
        exact ⟨c, u, (hev _ _).mpr d1, d2⟩
    commitRec := fun r y c u hr he => by
      obtain ⟨w1, h1, hs⟩ := hA.commitRec r y c u hr ((hev _ _).mp he)
      exact ⟨w1, R2 r y w1 h1, hs⟩
    fastCommitEv := fun r y u he => by
      obtain ⟨d1, c, d2⟩ := hA.fastCommitEv r y u ((hev _ _).mp he)
      exact ⟨d1, c, (hev _ _).mpr d2⟩
    makerLb := fun r y c hr he => by
      obtain ⟨w1, lb1, h1, hl1, hle⟩ := hA.makerLb r y c hr ((hev _ _).mp he)
      exact ⟨w1, lb1, R2 r y w1 h1, hl1, hle⟩
    lastLeBal := fun r hr y w2 lb2 h2 hl2 => hA.lastLeBal r hr y w2 lb2 (hlbv r y w2 lb2 h2 hl2) hl2
    peerOk := fun r hr => by rw [(hfl r).2.1]; exact hA.peerOk r hr
    crtOwn := fun r hr q hq => by rw [(hfl r).2.2.1, (hfl q).2.2.1]; exact hA.crtOwn r hr q hq
    crtRec := fun r hr y w2 h2 => by
      rw [(hfl y.q).2.2.1]
      rcases R1 r y w2 h2 with ⟨rfl, rfl, -⟩ | ⟨h, -⟩
      · exact Int.le_trans hx (hA.crtOwn _ hi _ hq)
      · exact hA.crtRec r hr y w2 h
    crtMsg := fun fr to m' y hm' hy => by
      rw [(hfl y.q).2.2.1]; rw [hmsgsE] at hm'; exact hA.crtMsg fr to m' y hm' hy
    crtEv := fun r e y he hy => by
      rw [(hfl y.q).2.2.1]; exact hA.crtEv r e y ((hev _ _).mp he) hy
    ownRow := fun q hq' j hj => by
      rw [(hfl q).2.2.1] at hj
      obtain ⟨w1, lb1, h1, hl1⟩ := hA.ownRow q hq' j hj
      exact ⟨w1, lb1, R2 q _ w1 h1, hl1⟩
    paNoAcc := fun r hr y w2 lb2 h2 hl2 hs u hv0 =>
      hA.paNoAcc r hr y w2 lb2 (hlbv r y w2 lb2 h2 hl2) hl2 hs u ((hev _ _).mp hv0)
    paLeader := fun r hr y w2 lb2 h2 hl2 hs hp hc' hb' => by
      obtain ⟨u, hu⟩ := hp
      exact hA.paLeader r hr y w2 lb2 (hlbv r y w2 lb2 h2 hl2) hl2 hs ⟨u, (hev _ _).mp hu⟩ hc' hb'
    prepNoProp := fun r hr y w2 lb2 h2 hl2 hp => by
      obtain ⟨d1, d2, d3, d4, d5⟩ := hA.prepNoProp r hr y w2 lb2 (hlbv r y w2 lb2 h2 hl2) hl2 hp
      exact ⟨d1, fun u h' => d2 u ((hev _ _).mp h'), fun u h' => d3 u ((hev _ _).mp h'), d4, d5⟩
    paMsgOnce := fun fr to y c => by rw [hcnt]; exact hA.paMsgOnce fr to y c
    accMsgOnce := fun fr to y c => by rw [hcnt]; exact hA.accMsgOnce fr to y c
    paVoteDeliv := fun r y c st u hst hv0 => by
      rcases hA.paVoteDeliv r y c st u hst ((hev _ _).mp hv0) with ⟨u0, h0⟩ | h0
      · exact Or.inl ⟨u0, (hev _ _).mpr h0⟩
      · exact Or.inr (fun fr' => hall _ _ _ (h0 fr'))
    parOnce := fun a r y c h1 => by
      rw [hcnt] at h1 ⊢
      obtain ⟨d1, d2⟩ := hA.parOnce a r y c h1
      exact ⟨d1, hall _ _ _ d2⟩
    arFrom := fun a r m' hm' => by
      rw [hmsgsE] at hm'
      obtain ⟨c, u, d1, d2⟩ := hA.arFrom a r m' hm'
      exact ⟨c, u, d1, (hev _ _).mpr d2⟩
    arOnce := fun a r y c h1 => by
      rw [hcnt] at h1 ⊢
      rcases hA.arOnce a r y c h1 with ⟨w1, lb1, h1', hl1, hlt'⟩ | ⟨d1, d2⟩
      · exact Or.inl ⟨w1, lb1, R2 r y w1 h1', hl1, hlt'⟩
      · exact Or.inr ⟨d1, hall _ _ _ d2⟩
    commitBal := fun fr to m' hm' => by rw [hmsgsE] at hm'; exact hA.commitBal fr to m' hm'
    sentPR := fun r to m' he => by
      obtain ⟨d1, d2, d3⟩ := hA.sentPR r to m' ((hev _ _).mp he)
      refine ⟨fun hr => ?_, fun c st u hb' => d2 c st u ((hevB _ _ _ _).mp hb'),
        fun to' m2 hb' hy => d3 to' m2 ((hevB _ _ _ _).mp hb') hy⟩
      obtain ⟨w1, h1, hle⟩ := d1 hr
      exact ⟨w1, R2 r _ w1 h1, hle⟩
    confCover := fun r hr e y cy he hrec c hc' => by
      rw [(hfl r).2.2.2.1]; exact hA.confCover r hr e y cy ((hev _ _).mp he) hrec c hc'
    classWf := fun r hr => by
      have hcl : (S'.rep r).lastScan = (S.rep r).lastScan ∧
          (S'.rep r).lastPut = (S.rep r).lastPut := by
        rw [hH.rep]; by_cases h : r = i
        · subst h; simp [RState.setInst]
        · simp [upd_apply, h]
      refine AuxProof.clsWf_keep (hA.classWf r hr) hcl.1 hcl.2 (fun y h => ?_)
      obtain ⟨w1, h1⟩ := Option.ne_none_iff_exists'.mp h
      rw [R2 r y w1 h1]; simp
    classCover := fun r hr e y cy he hrec => by
      have hcl : (S'.rep r).lastScan = (S.rep r).lastScan ∧
          (S'.rep r).lastPut = (S.rep r).lastPut := by
        rw [hH.rep]; by_cases h : r = i
        · subst h; simp [RState.setInst]
        · simp [upd_apply, h]
      rw [hcl.1, hcl.2]; exact hA.classCover r hr e y cy ((hev _ _).mp he) hrec
    paAttrs := fun r y c st u hst hv0 =>
      (hev _ _).mpr (hA.paAttrs r y c st u hst ((hev _ _).mp hv0))
    valOk := fun r y c u hv0 => by
      rw [hH.owner]; exact hA.valOk r y c u (hv0.imp (hev _ _).mp (hev _ _).mp)
    cmdsNe := by
      obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hA.cmdsNe
      refine ⟨fun fr to m' hm' => n1 fr to m' (by rw [hmsgsE] at hm'; exact hm'),
        fun r hr y w2 cs h2 hc' => ?_,
        fun r hr y w2 lb2 cs h2 hl2 hc' => n3 r hr y w2 lb2 cs (hlbv r y w2 lb2 h2 hl2) hl2 hc',
        fun fr to m' hm' => n4 fr to m' (by rw [hmsgsE] at hm'; exact hm'),
        fun r m' he => n5 r m' ((hev _ _).mp he),
        fun r y c u hv0 => n6 r y c u (hv0.imp (hev _ _).mp (hev _ _).mp)⟩
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · rw [W1] at hc'; cases hc'
      · exact n2 r hr y w2 cs h hc'
    prSent := fun fr to m' hm' => by
      rw [hmsgsE] at hm'; exact (hev _ _).mpr (hA.prSent fr to m' hm')
    selfOk := fun r m' he hs => hA.selfOk r m' ((hev _ _).mp he) hs
    selfRaw := fun r m' he => hA.selfRaw r m' ((hev _ _).mp he)
    pm := by
      have hpd : S'.pending = S.pending := by
        funext r; rw [hH.pending]
        by_cases hr : r = i
        · subst hr; rw [upd_same, hidle.1]
        · rw [upd_other _ _ _ _ hr]
      exact PMProof.pm_frame hA.pm (fun r e h => (hev r e).mpr h)
        (fun r e h => Or.inl ((hev r e).mp h)) (fun fr to m h => by rw [hmsgsE] at h; exact h)
        (fun fr to m h => by rw [hH.sent]; exact h) (fun y u h => (hcv' y u).mpr h)
        (fun r y w1 h => ⟨w1, R2 r y w1 h, Int.le_refl _⟩)
        (fun r y w2 lb2 h2 hl2 => ⟨w2, lb2, hlbv r y w2 lb2 h2 hl2, hl2, PMProof.LbPM.refl _⟩)
        (pmr_paSent hA.pm hH hidle.1 (fun b h => by cases h)
          (fun y w2 lb2 h2 hl2 _ => hlbv _ y w2 lb2 h2 hl2))
        (fun r b h => Or.inl (by rw [hpd] at h; exact h)),
    ownerCrt := fun y ps h => by
      rw [hH.owner] at h; rw [(hfl y.q).2.2.1]; exact hA.ownerCrt y ps h
    execLo := AuxProof.execLo_of_eq hA.execLo (fun r _ => (hfl r).2.2.2.2.1)
    exec := ExecOrd.invExec_hs hS.1 hA.exec hH hidle hagr (by rw [← hS']; funext r; simp) (fun r y h => by rw [hrep, if_neg]; rintro ⟨h1, h2⟩; rcases h with h | h; exact h h1; exact h h2) R3
      (fun w0 h0 _ => by rw [hnone] at h0; cases h0)
      (fun lb2 hl _ => by rw [W5] at hl; cases hl) }

/-! ## The recovery's start -/

theorem cycle_ok (i : Nat) (hi : i < nR) : (List.map (fun j => (i + 1 + j) % nR) (List.range (nR - 1))).Nodup ∧
    ∀ p ∈ List.map (fun j => (i + 1 + j) % nR) (List.range (nR - 1)), p < nR ∧ p ≠ i := by
  simp only [nR] at hi ⊢
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> decide

theorem mbz_spec (σ : RState) (bal : w32) (hid : σ.id < nR) :
    zz bal < makeBallotZ σ bal (W32 0) ∧ (nR : Int) ≤ makeBallotZ σ bal (W32 0) ∧
    makeBallotZ σ bal (W32 0) % nR = σ.id := by
  have h0 : sint.Z (W32 0) = 0 := by decide
  generalize hR : makeBallotZ σ bal (W32 0) = R
  unfold makeBallotZ at hR
  simp only [h0] at hR
  simp only [nR] at hid ⊢
  split at hR <;> (subst hR; simp only [zz, nR] at *; refine ⟨?_, ?_, ?_⟩ <;> omega)

/-- The own report `startRecoveryForInstance` builds. -/
def prOf (i : Nat) (x : InstId) (w : InstRec) (n : w32) : PrepareReply :=
  { acceptorId := W32 i, replica := W32 x.q, inst := W32 x.i, ballot := n,
    vballot := w.vbal, status := w.status, command := w.cmds.getD [],
    seq := w.seq, deps := w.deps }

/-- The bookkeeping `startRecoveryForInstance` builds. -/
def lbROf (i : Nat) (x : InstId) (w : InstRec) (n : w32) : LbRec :=
  { clientProposals := w.lb.bind (·.clientProposals), ballot := w.vbal,
    allEqual := true, preAcceptOKs := W64 0, acceptOKs := W64 0, nacks := W64 0,
    prepareReplies := [⟨prOf i x w n, decide (w.cmds = none)⟩], preparing := true,
    tryingToPreAccept := false, lastTriedBallot := n, cmds := w.cmds,
    status := w.status, seq := w.seq, deps := w.deps,
    leaderResponded := decide (i = x.q), preAcceptsSent := W64 0 }

theorem recover_eq (σ : RState) (x : InstId) (w : InstRec) (hw : σ.inst x = some w)
    (hnc : ¬ (stGe w.status stCOMMITTED = true ∧ w.cmds ≠ none))
    (hov : ¬ (2 ^ 31 - 1 : Int) < makeBallotZ σ w.bal (W32 0)) :
    hRecover σ x =
      (σ.setInst x { w with lb := some (lbROf σ.id x w (W32 (makeBallotZ σ w.bal (W32 0)))),
                            bal := W32 (makeBallotZ σ w.bal (W32 0)) },
       [Out.ev (.makeBallot x (W32 (makeBallotZ σ w.bal (W32 0)))),
        Out.ev (.selfReply (prOf σ.id x w (W32 (makeBallotZ σ w.bal (W32 0))))),
        Out.bcast (bcastPrepareOf (σ.setInst x { w with
          lb := some (lbROf σ.id x w (W32 (makeBallotZ σ w.bal (W32 0)))),
          bal := W32 (makeBallotZ σ w.bal (W32 0)) }) x (W32 (makeBallotZ σ w.bal (W32 0))))]) := by
  have hr : recOr σ x = w := by simp [recOr, hw]
  unfold hRecover
  rw [getOrDefault_eq, hr, setInst_self σ x w hw]
  simp only
  rw [if_neg hnc, if_neg hov]
  rfl

theorem toN_W32' (k : Nat) (hk : k < MAX_INSTANCE) : toN (W32 (k : Int)) = k := by
  have : zz (W32 (k : Int)) = k := zz_W32 _ (by omega) (by simp [MAX_INSTANCE] at hk; omega)
  simp only [toN]; simp only [zz] at this; rw [this]; simp

/-- **The recovery's start keeps the invariant.** -/
theorem inv_recover_start (S : Sys) (i : Nat) (x : InstId) (w : InstRec) (hS : Inv S)
    (hi : i < nR) (hidle : S.idle i) (hq : x.q < nR) (hw : (S.rep i).inst x = some w)
    (hnc : ¬ (stGe w.status stCOMMITTED = true ∧ w.cmds ≠ none))
    (hov : ¬ (2 ^ 31 - 1 : Int) < makeBallotZ (S.rep i) w.bal (W32 0)) :
    Inv (S.applyStep i (hRecover (S.rep i) x)) := by
  have hA := hS.2
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, s21, s22, s23, s24, s25, s26, s27⟩ := hS.1
  have hid : (S.rep i).id = i := s1.1 i hi
  obtain ⟨mb1, mb2, mb3⟩ := mbz_spec (S.rep i) w.bal (by rw [hid]; exact hi)
  rw [hid] at mb3
  rw [recover_eq _ x w hw hnc hov, hid]
  generalize hn : W32 (makeBallotZ (S.rep i) w.bal (W32 0)) = n
  have hzn : zz n = makeBallotZ (S.rep i) w.bal (W32 0) := by
    rw [← hn]; exact zz_W32 _ (by simp only [nR] at mb2; omega) (by omega)
  rw [← hzn] at mb1 mb2 mb3
  have hxi : x.i + 1 < MAX_INSTANCE := (s1.2.1 i hi x w hw).2.2.1
  have hx' : (⟨toN (W32 (x.q : Int)), toN (W32 (x.i : Int))⟩ : InstId) = x := by
    rw [toN_W32 _ hq, toN_W32' _ (by omega)]
  have hnc' : ¬ isCommitted w.status := by
    intro hc; apply hnc
    exact ⟨DecideProof.stGe_of_committed hc, hA.cmdsSome i hi x w hw
      (by intro h; rw [h] at hc; rcases hc with h | h <;> cases h)⟩
  have hbn : (balOwner n) = i := by
    simp only [balOwner]; rw [mb3]; simp
  have hnI : n ≠ initBal x := by
    intro h; rw [h, zz_initBal x hq] at mb2; simp [nR] at mb2 hq; omega
  have hnoMk : ∀ r, ¬ S.ev r (.makeBallot x n) := by
    intro r h
    rcases (s6.1 r x n h).1 with ⟨h1, -⟩ | ⟨-, h2⟩
    · rw [h1] at mb2; simp [nR] at mb2 hq; omega
    · rw [hbn] at h2; subst h2
      obtain ⟨w1, lb1, h1, hl1, hle⟩ := hA.makerLb i x n hi h
      rw [hw] at h1; cases h1
      have := hA.lastLeBal i hi x w lb1 hw hl1
      omega
  have hnoPh : ∀ r u, ¬ S.ev r (.phase1 x n u) := by
    intro r u h
    obtain ⟨p, p', -, hp, -⟩ := s6.2.1 r x n u h
    exact hnoMk r (List.mem_of_getElem? hp)
  have hnoAcc : ∀ r u, ¬ S.ev r (.accept x n u) := fun r u h => hnoMk r (s6.2.2.1 r x n u h)
  generalize hpr : prOf i x w n = pr
  generalize hlbR : lbROf i x w n = lbR
  have P : pr.acceptorId = W32 i ∧ pr.replica = W32 x.q ∧ pr.inst = W32 x.i ∧ pr.ballot = n ∧
      pr.vballot = w.vbal ∧ pr.status = w.status ∧ pr.command = w.cmds.getD [] ∧
      pr.seq = w.seq ∧ pr.deps = w.deps := by
    rw [← hpr]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨P1, P2, P3, P4, P5, P6, P7, P8, P9⟩ := P
  have hprx : (⟨toN pr.replica, toN pr.inst⟩ : InstId) = x := by rw [P2, P3]; exact hx'
  have L : lbR.clientProposals = w.lb.bind (·.clientProposals) ∧ lbR.ballot = w.vbal ∧
      lbR.preAcceptOKs = W64 0 ∧ lbR.acceptOKs = W64 0 ∧
      lbR.prepareReplies = [⟨pr, decide (w.cmds = none)⟩] ∧ lbR.preparing = true ∧
      lbR.tryingToPreAccept = false ∧ lbR.lastTriedBallot = n ∧ lbR.cmds = w.cmds ∧
      lbR.status = w.status ∧ lbR.deps = w.deps ∧ lbR.leaderResponded = decide (i = x.q) := by
    rw [← hlbR, ← hpr]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, L12⟩ := L
  generalize hw'd : ({ w with lb := some lbR, bal := n } : InstRec) = w'
  have W : w'.cmds = w.cmds ∧ w'.bal = n ∧ w'.vbal = w.vbal ∧ w'.status = w.status ∧
      w'.seq = w.seq ∧ w'.deps = w.deps ∧ w'.lb = some lbR ∧ w'.id = w.id ∧
      instVal w' = instVal w := by
    rw [← hw'd]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨W1, W2, W3, W4, W5, W6, W7, W8, W9⟩ := W
  have hH := hs_apply S i ((S.rep i).setInst x w') [Out.ev (.makeBallot x n), Out.ev (.selfReply pr),
    Out.bcast (bcastPrepareOf ((S.rep i).setInst x w') x n)] hidle
  generalize hS' : S.applyStep i ((S.rep i).setInst x w', [Out.ev (.makeBallot x n),
    Out.ev (.selfReply pr), Out.bcast (bcastPrepareOf ((S.rep i).setInst x w') x n)]) = S' at hH
  have e1 : evsOf [Out.ev (.makeBallot x n), Out.ev (.selfReply pr),
      Out.bcast (bcastPrepareOf ((S.rep i).setInst x w') x n)] = [.makeBallot x n, .selfReply pr] := rfl
  have e2 : sendsOf [Out.ev (.makeBallot x n), Out.ev (.selfReply pr),
      Out.bcast (bcastPrepareOf ((S.rep i).setInst x w') x n)] = fun _ => [] := by funext to; rfl
  have e3 : pendFold [Out.ev (.makeBallot x n), Out.ev (.selfReply pr),
      Out.bcast (bcastPrepareOf ((S.rep i).setInst x w') x n)] none =
      (bcastPrepareOf ((S.rep i).setInst x w') x n).norm := rfl
  rw [e1, e2, e3] at hH
  generalize hB : bcastPrepareOf ((S.rep i).setInst x w') x n = B at hH
  have hBx : B.x = x := by rw [← hB]; rfl
  have hBm : B.m = .prepare ⟨W32 i, W32 x.q, W32 x.i, n⟩ := by
    rw [← hB]; simp [bcastPrepareOf, RState.setInst, hid]
  have hBp : B.peers = List.map (fun j => (i + 1 + j) % nR) (List.range (nR - 1)) := by
    rw [← hB]; simp [bcastPrepareOf, cyclePeers, RState.setInst, hid]
  have hBn : B.need = nR - 1 ∧ B.sent = 0 := by rw [← hB]; exact ⟨rfl, rfl⟩
  have hcyc := cycle_ok i hi
  -- events
  have hE : ∀ r e, S'.ev r e ↔ S.ev r e ∨ (r = i ∧ (e = .makeBallot x n ∨ e = .selfReply pr)) := by
    intro r e; rw [hH.ev_iff]; simp
  have hold : ∀ r e, S'.ev r e → (∀ y c, e ≠ .makeBallot y c) → (∀ m', e ≠ .selfReply m') →
      S.ev r e := by
    intro r e he h1 h2
    rcases (hE r e).mp he with h | ⟨-, rfl | rfl⟩
    · exact h
    · exact absurd rfl (h1 _ _)
    · exact absurd rfl (h2 _)
  have hselfO : ∀ m', S.ev i (.selfReply m') → m' ≠ pr := by
    intro m' h he; rw [he] at h
    obtain ⟨w1, h1, hle⟩ := s27.2.2.2.2.1 i _ (.selfReply pr) hi ⟨h, Or.inr rfl⟩
    rw [hprx, hw] at h1; cases h1; rw [P4] at hle; omega
  have hnotEold : ∀ r e, S.ev r e → r = i → e ∉ [Event.makeBallot x n, .selfReply pr] := by
    intro r e he hr h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact hnoMk r he
    · subst hr; exact hselfO pr he rfl
  have hevB : ∀ r e r' e', S'.evBefore r e r' e' → S.ev r' e' → S.evBefore r e r' e' :=
    fun r e r' e' h h' => hH.evBefore_back h h' (hnotEold r' e' h')
  have hmsgs : ∀ fr to m', m' ∈ S'.msgs fr to ↔ m' ∈ S.msgs fr to ∨
      (fr = i ∧ m' = .prepare ⟨W32 i, W32 x.q, W32 x.i, n⟩ ∧
        to ∈ List.map (fun j => (i + 1 + j) % nR) (List.range (nR - 1))) := by
    intro fr to m'
    rw [hH.mem_msgs]
    constructor
    · rintro (h | ⟨hf, h | h⟩)
      · exact Or.inl h
      · cases h
      · obtain ⟨h1, h2⟩ := mem_intended_norm h
        rw [hBm] at h1; rw [hBp] at h2; exact Or.inr ⟨hf, h1, h2⟩
    · rintro (h | ⟨hf, rfl, hto⟩)
      · exact Or.inl h
      · refine Or.inr ⟨hf, Or.inr ?_⟩
        have hne : B.norm = some B := by
          unfold Bcast.norm; rw [if_neg]; rintro (h | h)
          · rw [hBp] at h; rw [h] at hto; cases hto
          · rw [hBn.1, hBn.2] at h; simp [nR] at h
        rw [hne]; simp only [intendedOf]; rw [hBp, if_pos hto, hBm]; simp
  have hmk1 : ∀ r y c, S'.ev r (.makeBallot y c) → S.ev r (.makeBallot y c) ∨
      (r = i ∧ y = x ∧ c = n) := by
    intro r y c h
    rcases (hE r _).mp h with h | ⟨hr, h | h⟩
    · exact Or.inl h
    · simp only [Event.makeBallot.injEq] at h; exact Or.inr ⟨hr, h.1, h.2⟩
    · cases h
  have hvote : ∀ r y c st u, S'.ev r (.vote y c st u) → S.ev r (.vote y c st u) :=
    fun r y c st u h => hold r _ h (fun _ _ h => by cases h) (fun _ h => by cases h)
  have hacc : ∀ r y c u, S'.ev r (.accept y c u) → S.ev r (.accept y c u) :=
    fun r y c u h => hold r _ h (fun _ _ h => by cases h) (fun _ h => by cases h)
  have hph : ∀ r y c u, S'.ev r (.phase1 y c u) → S.ev r (.phase1 y c u) :=
    fun r y c u h => hold r _ h (fun _ _ h => by cases h) (fun _ h => by cases h)
  have hcntP : ∀ fr to (p : Msg → Bool), p (.prepare ⟨W32 i, W32 x.q, W32 x.i, n⟩) = false →
      S'.cnt fr to p = S.cnt fr to p := by
    intro fr to p hp
    rw [hH.cnt_eq]
    split
    · simp only [List.nil_append, Nat.add_eq_left, List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro m' hm'
      obtain ⟨h1, -⟩ := mem_intended_norm hm'
      rw [h1, hBm, hp]; simp
    · rfl
  have hallP : ∀ fr to (p : Msg → Bool), p (.prepare ⟨W32 i, W32 x.q, W32 x.i, n⟩) = false →
      S.allDeliv fr to p → S'.allDeliv fr to p := by
    intro fr to p hp h
    refine hH.allDeliv_old h (fun _ m' hm' => ?_)
    simp only [List.nil_append] at hm'
    obtain ⟨h1, -⟩ := mem_intended_norm hm'
    rw [h1, hBm, hp]
  have hcv' : ∀ y u, S'.committedVal y u ↔ S.committedVal y u := by
    intro y u
    constructor
    · rintro (⟨r, b', h⟩ | ⟨fr, to, m', hm', hy, rfl⟩)
      · exact Or.inl ⟨r, b', hold r _ h (fun _ _ h => by cases h) (fun _ h => by cases h)⟩
      · rcases (hmsgs _ _ _).mp hm' with h | ⟨-, h, -⟩
        · exact Or.inr ⟨fr, to, m', h, hy, rfl⟩
        · cases h
    · rintro (⟨r, b', h⟩ | ⟨fr, to, m', hm', hy, rfl⟩)
      · exact Or.inl ⟨r, b', hH.ev_old h⟩
      · exact Or.inr ⟨fr, to, m', hH.msgs_old hm', hy, rfl⟩
  have hprepR : ∀ r m' e, S'.prepReport r m' e ↔ S.prepReport r m' e ∨
      (i = r ∧ pr = m' ∧ e = .selfReply pr) := by
    intro r m' e
    constructor
    · rintro ⟨he, ⟨to, hm', rfl⟩ | rfl⟩
      · refine Or.inl ⟨hold r _ he (fun _ _ h => by cases h) (fun _ h => by cases h),
          Or.inl ⟨to, ?_, rfl⟩⟩
        rcases (hmsgs _ _ _).mp hm' with h | ⟨-, h, -⟩
        · exact h
        · cases h
      · rcases (hE r _).mp he with h | ⟨hr, h | h⟩
        · exact Or.inl ⟨h, Or.inr rfl⟩
        · cases h
        · simp only [Event.selfReply.injEq] at h; subst h; exact Or.inr ⟨hr.symm, rfl, rfl⟩
    · rintro (⟨he, ⟨to, hm', rfl⟩ | rfl⟩ | ⟨rfl, rfl, rfl⟩)
      · exact ⟨hH.ev_old he, Or.inl ⟨to, hH.msgs_old hm', rfl⟩⟩
      · exact ⟨hH.ev_old he, Or.inr rfl⟩
      · exact ⟨hH.ev_new (by simp), Or.inr rfl⟩
  -- records
  have hrep : ∀ r y, (S'.rep r).inst y =
      if r = i ∧ y = x then some w' else (S.rep r).inst y := by
    intro r y
    rw [hH.rep]
    by_cases hr : r = i
    · subst hr; simp only [upd_same, RState.setInst, upd_apply, true_and]
    · simp [upd_other _ _ _ _ hr, hr]
  have R1 : ∀ r y w2, (S'.rep r).inst y = some w2 →
      (i = r ∧ x = y ∧ w' = w2) ∨ ((S.rep r).inst y = some w2 ∧ ¬ (r = i ∧ y = x)) := by
    intro r y w2 h; rw [hrep] at h; split at h
    · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; simp only [Option.some.injEq] at h
      exact Or.inl ⟨rfl, rfl, h⟩
    · rename_i hc; exact Or.inr ⟨h, hc⟩
  have R2 : ∀ r y w1, (S.rep r).inst y = some w1 →
      (i = r ∧ x = y ∧ w = w1) ∨ (S'.rep r).inst y = some w1 := by
    intro r y w1 h
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [hw] at h; cases h; exact Or.inl ⟨rfl, rfl, rfl⟩
    · right; rw [hrep, if_neg hc]; exact h
  have R3 : (S'.rep i).inst x = some w' := by rw [hrep]; simp
  have hfl : ∀ r, (S'.rep r).id = (S.rep r).id ∧ (S'.rep r).peerOrder = (S.rep r).peerOrder ∧
      (S'.rep r).crtInstance = (S.rep r).crtInstance ∧
      (S'.rep r).conflicts = (S.rep r).conflicts ∧
      (S'.rep r).execedUpTo = (S.rep r).execedUpTo ∧ (S'.rep r).store = (S.rep r).store := by
    intro r
    by_cases hr : r = i
    · subst hr; rw [hH.rep_self]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [hH.rep_other hr]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- the record's core is kept
  have C1 : ∀ r y w2, (S'.rep r).inst y = some w2 → ∃ w1, (S.rep r).inst y = some w1 ∧
      w2.cmds = w1.cmds ∧ w2.vbal = w1.vbal ∧ w2.status = w1.status ∧ w2.seq = w1.seq ∧
      w2.deps = w1.deps ∧ w2.id = w1.id ∧ instVal w2 = instVal w1 ∧ zz w1.bal ≤ zz w2.bal := by
    intro r y w2 h2
    rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, -⟩
    · exact ⟨w, hw, W1, W3, W4, W5, W6, W8, W9, by rw [W2]; omega⟩
    · exact ⟨w2, h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩
  have C2 : ∀ r y w1, (S.rep r).inst y = some w1 → ∃ w2, (S'.rep r).inst y = some w2 ∧
      w2.cmds = w1.cmds ∧ w2.vbal = w1.vbal ∧ w2.status = w1.status ∧ w2.seq = w1.seq ∧
      w2.deps = w1.deps ∧ instVal w2 = instVal w1 ∧ zz w1.bal ≤ zz w2.bal := by
    intro r y w1 h1
    rcases R2 r y w1 h1 with ⟨rfl, rfl, rfl⟩ | h
    · exact ⟨w', R3, W1, W3, W4, W5, W6, W9, by rw [W2]; omega⟩
    · exact ⟨w1, h, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩
  have hex : ∀ r y, (S'.rep r).executed y ↔ (S.rep r).executed y := by
    intro r y
    constructor
    · rintro ⟨w2, h2, hs⟩
      obtain ⟨w1, h1, -, -, e3, -⟩ := C1 r y w2 h2
      exact ⟨w1, h1, by rw [← e3]; exact hs⟩
    · rintro ⟨w1, h1, hs⟩
      obtain ⟨w2, h2, -, -, e3, -⟩ := C2 r y w1 h1
      exact ⟨w2, h2, by rw [e3]; exact hs⟩
  have hcmdsE : ∀ r y, ((S'.rep r).inst y).bind (·.cmds) = ((S.rep r).inst y).bind (·.cmds) := by
    intro r y
    cases h2 : (S'.rep r).inst y with
    | none =>
      cases h1 : (S.rep r).inst y with
      | none => rfl
      | some w1 => obtain ⟨w2, h2', -⟩ := C2 r y w1 h1; rw [h2] at h2'; cases h2'
    | some w2 =>
      obtain ⟨w1, h1, e1, -⟩ := C1 r y w2 h2
      rw [h1]; simp only [Option.bind_some]; exact e1
  have hsafeM : SafeMono S S' := by
    refine ⟨fun r y w1 h1 => ?_, fun r e h => hH.ev_old h,
      fun r y c st u h => Or.inl (hvote r y c st u h),
      fun y u h => Or.inl (hold _ _ h (fun _ _ h => by cases h) (fun _ h => by cases h)),
      fun a y m' h hy hb' => ?_⟩
    · obtain ⟨w2, h2, -, -, e3, -, -, -, hle⟩ := C2 r y w1 h1
      exact ⟨w2, h2, hle, fun h => Or.inl (by rw [e3]; exact h)⟩
    · rcases (hmsgs _ _ _).mp h with h | ⟨-, h, -⟩
      · exact Or.inl h
      · cases h
  have hsafe : Inv.safe S' := safe_frame hsafeM s26 (fun r y b v h => hacc _ _ _ _ h)
    (fun r y b v h => hph _ _ _ _ h)
  have hwq : w.id = x ∧ x.q < nR ∧ x.i + 1 < MAX_INSTANCE ∧ (w.status ≠ stNONE → depsOk w.deps) :=
    let h := s1.2.1 i hi x w hw; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  have hwf : Inv.wf S' := by
    obtain ⟨w1', w2', w3', w4', w5', w6', w7', w8'⟩ := s1
    refine ⟨fun r hr => by rw [(hfl r).1]; exact w1' r hr, fun r hr y w2 h2 => ?_,
      fun r hr q hq' => by rw [(hfl r).2.2.1]; exact w3' r hr q hq',
      fun r hr q k p hk => ?_, fun r hr q hq' n' hn' => ?_, fun fr' to hne => ?_,
      fun fr' to n' hn' => ?_, fun r b' hb' => ?_⟩
    · rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, -⟩
      · obtain ⟨g1, g2, g3, g4, -, -, g7⟩ := w2' i hi x w hw
        refine ⟨by rw [W8]; exact g1, g2, g3, fun hs => by rw [W6]; rw [W4] at hs; exact g4 hs,
          fun lb2 hl2 hs => ?_, fun _ => by rw [W7]; simp, fun lb2 ps hl2 hps => ?_⟩
        · rw [W7] at hl2; cases hl2; rw [L11]; rw [L10] at hs; exact g4 hs
        · rw [W7] at hl2; cases hl2; rw [hH.owner]; rw [L1] at hps
          cases hlw : w.lb with
          | none => rw [hlw] at hps; cases hps
          | some lb0 => rw [hlw] at hps; exact g7 lb0 ps hlw hps
      · obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := w2' r hr y w2 h
        exact ⟨g1, g2, g3, g4, g5, g6, fun lb ps hlb hps => by rw [hH.owner]; exact g7 lb ps hlb hps⟩
    · rw [(hfl r).2.2.2.1] at hk
      obtain ⟨k1', k2', k3'⟩ := w4' r hr q k p hk
      have grow : ∀ y, (S.rep r).inst y ≠ none → (S'.rep r).inst y ≠ none := by
        intro y hy hy'
        obtain ⟨w1, h1⟩ := Option.ne_none_iff_exists'.mp hy
        obtain ⟨w2, h2, -⟩ := C2 r y w1 h1
        rw [h2] at hy'; cases hy'
      exact ⟨k1', fun h0 => grow _ (k2' h0), fun h0 => grow _ (k3' h0)⟩
    · rw [(hfl r).2.2.2.2.1] at hn'
      exact (hex r _).mpr (w5' r hr q hq' n' hn')
    · by_cases h0 : S.msgs fr' to = []
      · obtain ⟨m', hm'⟩ := List.exists_mem_of_ne_nil _ hne
        rcases (hmsgs _ _ _).mp hm' with h | ⟨rfl, -, hto⟩
        · rw [h0] at h; cases h
        · exact ⟨hi, (hcyc.2 to hto).1, fun h => (hcyc.2 to hto).2 h.symm⟩
      · exact w6' fr' to h0
    · rcases hH.delOk fr' to n' hn' with h | h
      · rw [hH.sent]; exact w7' fr' to n' h
      · rw [hH.sent]; exact h
    · rw [hH.pending] at hb'
      by_cases hr : r = i
      · subst hr
        rw [upd_same] at hb'
        obtain ⟨rfl, hpn, hsn⟩ := norm_some hb'
        refine ⟨hi, by rw [hH.execCur]; exact hidle.2, hpn, hsn, by rw [hBp]; exact hcyc.1,
          fun q hq' => by rw [hBp] at hq'; exact hcyc.2 q hq', w', lbR, by rw [hBx]; exact R3, W7⟩
      · rw [upd_other _ _ _ _ hr] at hb'
        obtain ⟨d1, d2, d3, d4, d5, d6, w1, lb1, h1, hl1⟩ := w8' r b' hb'
        refine ⟨d1, by rw [hH.execCur]; exact d2, d3, d4, d5, d6, w1, lb1, ?_, hl1⟩
        rw [hrep, if_neg (fun h => hr h.1)]; exact h1
  have hbal : Inv.ballots S' := by
    refine ⟨fun r hr y w2 h2 => ?_, fun r hr y c st u he => ?_⟩
    · obtain ⟨w1, h1, -, e2, -, -, -, -, -, hle⟩ := C1 r y w2 h2
      rw [e2]; exact Int.le_trans (s5.1 r hr y w1 h1) hle
    · obtain ⟨w1, h1, hle⟩ := s5.2 r hr y c st u (hvote _ _ _ _ _ he)
      obtain ⟨w2, h2, -, -, -, -, -, -, hle'⟩ := C2 r y w1 h1
      exact ⟨w2, h2, Int.le_trans hle hle'⟩
  have hzq : 0 ≤ zz (W32 (x.q : Int)) ∧ zz (W32 (x.q : Int)) < nR := by
    rw [zz_W32 _ (by omega) (by simp [nR] at hq; omega)]; omega
  have hzi : 0 ≤ zz (W32 (x.i : Int)) := by
    rw [zz_W32 _ (by omega) (by simp [MAX_INSTANCE] at hxi; omega)]; omega
  have hown : Inv.ballotOwner S' := by
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := s6
    refine ⟨fun r y c he => ?_, fun r y c u he => hH.evBefore_old (o2 r y c u (hph _ _ _ _ he)),
      fun r y c u he => hH.ev_old (o3 r y c u (hacc _ _ _ _ he)),
      fun r to m' hm' => ?_, fun r to m' hm' => ?_, fun r to m' hm' => ?_⟩
    · rcases hmk1 r y c he with h | ⟨rfl, rfl, rfl⟩
      · refine ⟨(o1 r y c h).1, ?_⟩
        rw [hH.count_eq (fun hr => hnotEold r _ h hr)]
        exact (o1 r y c h).2
      · refine ⟨Or.inr ⟨mb2, hbn⟩, ?_⟩
        rw [hH.hist, List.filter_append, List.length_append]
        have h0 : (S.hist.filter (· = (r, .makeBallot y c))).length = 0 := by
          simp only [List.length_eq_zero_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
          intro a ha hae; subst hae; exact hnoMk r ha
        rw [h0]; simp
    · rcases (hmsgs _ _ _).mp hm' with h | ⟨hri, hpm, -⟩
      · obtain ⟨d1, d2⟩ := o4 r to m' h; exact ⟨d1, hH.ev_old d2⟩
      · simp only [Msg.prepare.injEq] at hpm; subst hpm
        rw [hri]
        refine ⟨rfl, hH.ev_new ?_⟩
        simp only [hx']; simp
    · rcases (hmsgs _ _ _).mp hm' with h | ⟨-, h, -⟩
      · obtain ⟨d1, d2⟩ := o5 r to m' h; exact ⟨d1, hH.ev_old d2⟩
      · cases h
    · rcases (hmsgs _ _ _).mp hm' with h | ⟨-, h, -⟩
      · obtain ⟨d1, d2⟩ := o6 r to m' h; exact ⟨d1, hH.ev_old d2⟩
      · cases h
  have hop : Inv.oneProposal S' := by
    obtain ⟨p1, p2, p3⟩ := s7
    refine ⟨fun r r' y c u u' he he' => ?_, fun r r' y c u u' he he' =>
      p2 r r' y c u u' (hacc _ _ _ _ he) (hacc _ _ _ _ he'), fun r r' y c u u' he he' =>
      p3 r r' y c u u' (hph _ _ _ _ he) (hacc _ _ _ _ he')⟩
    obtain ⟨d1, d2, d3⟩ := p1 r r' y c u u' (hph _ _ _ _ he) (hph _ _ _ _ he')
    refine ⟨d1, d2, ?_⟩
    rw [hH.count_eq (fun hr => hnotEold r _ (hph _ _ _ _ he) hr)]; exact d3
  have hvf : Inv.votesFollowProposals S' := by
    refine ⟨fun r y c st u he hst => ?_, fun r y c u he => ?_⟩
    · obtain ⟨l, u0, h1, h2⟩ := s8.1 r y c st u (hvote _ _ _ _ _ he) hst
      exact ⟨l, u0, hH.ev_old h1, h2⟩
    · obtain ⟨l, h1⟩ := s8.2 r y c u (hvote _ _ _ _ _ he); exact ⟨l, hH.ev_old h1⟩
  have hrr : Inv.repliesReportVotes S' := by
    obtain ⟨q1, q2, q3⟩ := s9
    refine ⟨fun r m' e hp => ?_, fun a r m' hm' => ?_, fun a r m' hm' => ?_⟩
    · rcases (hprepR r m' e).mp hp with hp0 | ⟨rfl, rfl, rfl⟩
      · obtain ⟨d1, d2, d3, d4, d5⟩ := q1 r m' e hp0
        refine ⟨d1, fun hs => hH.evBefore_old (d2 hs), fun hs => (hcv' _ _).mpr (d3 hs),
          fun hs c st u hb' => d4 hs c st u (hevB _ _ _ _ hb' hp0.1),
          fun c st u hb' => d5 c st u ?_⟩
        obtain ⟨pp, pp', hlt', h1, h2⟩ := hb'
        exact hevB _ _ _ _ ⟨pp, pp', hlt', h1, h2⟩ (hvote _ _ _ _ _ (List.mem_of_getElem? h2))
      · rw [hprx]
        refine ⟨P1, fun hs => ?_, fun hs => ?_, fun hs c st u hb' => ?_, fun c st u hb' => ?_⟩
        · rw [P6] at hs
          have hv := hA.recVote _ hi x w hw hs
          rw [P5, P6, P7, P8, P9]
          exact (hH.evBefore_iff _ _ _ _).mpr (Or.inr (Or.inl ⟨hv, rfl, by simp⟩))
        · rw [P6] at hs; exact absurd hs hnc'
        · rw [P6] at hs
          obtain ⟨pp, pp', -, h1, -⟩ := hb'
          exact (hA.noneRec _ hi x w hw hs).2 c st u (hvote _ _ _ _ _ (List.mem_of_getElem? h1))
        · exfalso
          obtain ⟨pp, pp', hlt', h1, h2⟩ := hb'
          have hv := hvote _ _ _ _ _ (List.mem_of_getElem? h2)
          obtain ⟨q, q', -, hq1, -⟩ := hevB _ _ _ _ ⟨pp, pp', hlt', h1, h2⟩ hv
          exact hselfO pr (List.mem_of_getElem? hq1) rfl
    · rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, h, -⟩
      · obtain ⟨d1, d2, d3, d4⟩ := q2 a r m' hm'
        refine ⟨?_, fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
        · obtain ⟨u, hu⟩ := d1; exact ⟨u, hH.ev_old hu⟩
        · obtain ⟨e1, u, e2, e3⟩ := d2 hs; exact ⟨e1, u, hH.ev_old e2, e3⟩
        · obtain ⟨u, e2, e3⟩ := d3 hs; exact ⟨u, hH.ev_old e2, e3⟩
        · obtain ⟨u, e2, e3⟩ := d4 hs; exact ⟨u, (hcv' _ _).mpr e2, e3⟩
      · cases h
    · rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, h, -⟩
      · rcases q3 a r m' hm' with ⟨u, hu⟩ | ⟨⟨c, u, hu⟩, c2⟩
        · exact Or.inl ⟨u, hH.evBefore_old hu⟩
        · refine Or.inr ⟨⟨c, u, hH.evBefore_old hu⟩, fun m2 e' hp hy hb' => ?_⟩
          have hsent : S.ev a (.sent r (.acceptReply m')) := by
            obtain ⟨pp, pp', -, -, h1⟩ := hu; exact List.mem_of_getElem? h1
          rcases (hprepR _ _ _).mp hp with hp0 | ⟨rfl, rfl, rfl⟩
          · exact c2 m2 e' hp0 hy (hevB _ _ _ _ hb' hsent)
          · exfalso
            obtain ⟨q, q', -, hq1, -⟩ := hevB _ _ _ _ hb' hsent
            exact hselfO pr (List.mem_of_getElem? hq1) rfl
      · cases h
  have hhi : Inv.prepReplyHighest S' := by
    intro r m' e hp c st u hb'
    rcases (hprepR r m' e).mp hp with hp0 | ⟨rfl, rfl, rfl⟩
    · exact s10 r m' e hp0 c st u (hevB _ _ _ _ hb' hp0.1)
    · obtain ⟨pp, pp', -, h1, -⟩ := hb'
      have hv := hvote _ _ _ _ _ (List.mem_of_getElem? h1)
      rw [hprx] at hv; rw [P5]; exact hA.votesLe _ hi x w hw c st u hv
  have hlbX : ∀ c, (∃ u, S.ev i (.phase1 x c u)) ∨ (∃ u, S.ev i (.accept x c u)) → zz c < zz n := by
    intro c hpa
    have hmk : S.ev i (.makeBallot x c) := by
      rcases hpa with ⟨u, h⟩ | ⟨u, h⟩
      · obtain ⟨p, p', -, hp, -⟩ := s6.2.1 i x c u h; exact List.mem_of_getElem? hp
      · exact s6.2.2.1 i x c u h
    obtain ⟨w1, lb1, h1, hl1, hle⟩ := hA.makerLb i x c hi hmk
    rw [hw] at h1; cases h1
    have := hA.lastLeBal i hi x w lb1 hw hl1
    omega
  have hlbI : Inv.lbInv S' := by
    intro r hr y w2 lb2 h2 hl2
    rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, hne⟩
    · rw [W7] at hl2; cases hl2
      refine ⟨by rw [L8]; exact hH.ev_new (by simp), ?_, L7, fun c u hv0 => ?_,
        fun _ c2 => (by rw [L3] at c2; exact absurd rfl c2),
        ⟨[], List.nodup_nil, by rw [L3]; rfl, fun a m' h => by cases h⟩,
        ⟨[], List.nodup_nil, by rw [L4]; rfl, fun a h => by cases h⟩,
        fun _ _ _ c4 => (by rw [L6] at c4; cases c4), fun _ => ?_⟩
      · rw [L2, L8]; have := s5.1 i hi x w hw; omega
      · rw [L8]
        rcases hv0 with hv0 | hv0
        · exact Int.le_of_lt (hlbX c (Or.inl ⟨u, hph _ _ _ _ hv0⟩))
        · exact Int.le_of_lt (hlbX c (Or.inr ⟨u, hacc _ _ _ _ hv0⟩))
      · rw [L5]
        refine ⟨by simp, fun e he => ?_⟩
        simp only [List.mem_singleton] at he; subst he
        refine ⟨by rw [P4, L8], by simp only [Msg.instOf]; rw [hprx], Or.inr ⟨?_, hH.ev_new (by simp)⟩⟩
        simp only; rw [P1]; exact toN_W32 i hi
    · obtain ⟨a1, a2, a3, a4, a5, ⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩, a8, a9⟩ :=
        s11 r hr y w2 lb2 h hl2
      refine ⟨hH.ev_old a1, a2, a3,
        fun c u hv0 => a4 c u (hv0.imp (hph _ _ _ _) (hacc _ _ _ _)),
        fun c1 c2 => ?_, ⟨Q, q1, q2, fun a m' hq => ?_⟩, ⟨Q', q1', q2', fun a hq => ?_⟩,
        fun c1 c2 c3 c4 => ?_, fun hp => ?_⟩
      · obtain ⟨d1, d2, u, d3, d4⟩ := a5 c1 c2; exact ⟨d1, d2, u, hH.ev_old d3, d4⟩
      · obtain ⟨b1, b2, b3, b4⟩ := q3 a m' hq; exact ⟨b1, b2, hH.deliveredMsg_old b3, b4⟩
      · obtain ⟨b1, b2, m', b3, b4⟩ := q3' a hq; exact ⟨b1, b2, m', hH.deliveredMsg_old b3, b4⟩
      · obtain ⟨d1, d2⟩ := a8 c1 c2 c3 c4; exact ⟨hH.ev_old d1, hH.ev_old d2⟩
      · obtain ⟨c1, c2⟩ := a9 hp
        refine ⟨c1, fun e he' => ?_⟩
        obtain ⟨d1, d2, d3⟩ := c2 e he'
        refine ⟨d1, d2, ?_⟩
        rcases d3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact Or.inl ⟨e1, hH.deliveredMsg_old e2⟩
        · exact Or.inr ⟨e1, hH.ev_old e2⟩
  have hagr : Inv.agreement S' := by
    refine ⟨fun y u u' h1 h2 => s12.1 y u u' ((hcv' _ _).mp h1) ((hcv' _ _).mp h2),
      fun r hr y w2 h2 hc' => ?_⟩
    obtain ⟨w1, h1, e1, -, e3, -, -, -, e7, -⟩ := C1 r y w2 h2
    rw [e3] at hc'
    obtain ⟨d1, d2⟩ := s12.2 r hr y w1 h1 hc'
    exact ⟨by rw [e1]; exact d1, (hcv' _ _).mpr (by rw [e7]; exact d2)⟩
  have hdE : S'.dEdge = S.dEdge := by funext y z; simp only [Sys.dEdge, hcv']
  have hsO : S'.sccOrd = S.sccOrd := by funext y z; simp only [Sys.sccOrd, hcv']
  have hdep : ∀ r y z, (S'.rep r).depEdge y z ↔ (S.rep r).depEdge y z := by
    intro r y z
    constructor
    · rintro ⟨w2, h2, hq', hz⟩
      obtain ⟨w1, h1, -, -, -, -, e5, -⟩ := C1 r y w2 h2
      exact ⟨w1, h1, hq', by rw [← e5]; exact hz⟩
    · rintro ⟨w1, h1, hq', hz⟩
      obtain ⟨w2, h2, -, -, -, -, e5, -⟩ := C2 r y w1 h1
      exact ⟨w2, h2, hq', by rw [e5]; exact hz⟩
  have hso : ∀ r, Sys.slotsOn (S'.rep r) = Sys.slotsOn (S.rep r) := by
    intro r; funext xs k; simp only [Sys.slotsOn, hcmdsE]
  have hlx : ∀ r k, S'.lexec r k = S.lexec r k := by
    intro r k
    simp only [Sys.lexec, Sys.curSlots, hso, hH.execCur, hH.execLog, hH.execIdx]
  have hexec : Inv.execClosed S' ∧ Inv.execCursor S' ∧ Inv.execOrder S' ∧
      Inv.execPrefix S' := by
    refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_⟩
    · obtain ⟨e1, e2, e3⟩ := s18 r hr
      refine ⟨by rw [hH.execLog]; exact e1, fun y => by rw [hH.execLog, hex]; exact e2 y,
        fun y w2 h2 hs => ?_⟩
      obtain ⟨w1, h1, -, -, f3, -, -, -, f7, -⟩ := C1 r y w2 h2
      rw [f3] at hs
      obtain ⟨d1, d2⟩ := e3 y w1 h1 hs
      refine ⟨(hcv' _ _).mpr (by rw [f7]; exact d1), fun z hz => ?_⟩
      rw [hex, hH.execCur]; exact d2 z ((hdep r y z).mp hz)
    · by_cases hri : r = i
      · subst r
        have hc0 : S.execCur i = [] := hidle.2
        rw [hH.execCur, hH.execIdx]
        exact ⟨fun _ => (s19 i hr).1 hc0, fun h => absurd hc0 h⟩
      · rw [hH.rep_other hri, hH.execCur, hH.execIdx]; exact s19 r hr
    · intro r hr a c y z hac h1 h2 ht
      rw [hH.execLog] at h1 h2; rw [hdE] at ht ⊢; rw [hsO]
      exact s20 r hr a c y z hac h1 h2 ht
    · obtain ⟨p1, p2, p3⟩ := s21
      refine ⟨fun r hr k => ?_, fun r hr k => ?_, fun r hr k pre e post h => ?_⟩
      · rw [hlx, hH.gexec]; exact p1 r hr k
      · rw [hlx, (hfl r).2.2.2.2.2]; exact p2 r hr k
      · rw [hlx] at h; rw [hH.gexec]; exact p3 r hr k pre e post h
  have hdc : Inv.decidedChosen S' := by
    intro y u hu
    rcases s13 y u ((hcv' _ _).mp hu) with ⟨c, Q, q1, q2, q3⟩ | ⟨⟨Q, q1, q2, q3⟩, hf⟩
    · exact Or.inl ⟨c, Q, q1, q2, fun r hr => ⟨(q3 r hr).1, hH.ev_old (q3 r hr).2⟩⟩
    · refine Or.inr ⟨⟨Q, q1, q2, fun r hr => ?_⟩, hH.ev_old hf⟩
      obtain ⟨d1, d2, st, d3, d4⟩ := q3 r hr
      exact ⟨d1, d2, st, d3, hH.ev_old d4⟩
  have hdcv : Inv.depsCover S' := fun y z u u' hne h1 h2 hi' =>
    s15 y z u u' hne ((hcv' _ _).mp h1) ((hcv' _ _).mp h2) hi'
  have hwit : Inv.witnesses S' := by
    intro y u hu hn'
    obtain ⟨W, w1, w2, w3⟩ := s16 y u ((hcv' _ _).mp hu) hn'
    exact ⟨W, w1, w2, fun r hr => ⟨(w3 r hr).1, by
      obtain ⟨d, d1, d2⟩ := (w3 r hr).2; exact ⟨d, hH.ev_old d1, d2⟩⟩⟩
  have hac : Inv.attrsCover S' := by
    intro r e y cy z cz d hrec hne hb' hi'
    refine s17 r e y cy z cz d hrec hne (hevB _ _ _ _ hb' ?_) hi'
    obtain ⟨pp, pp', -, -, h⟩ := hb'
    exact hold r _ (List.mem_of_getElem? h) (fun _ _ h => by cases h) (fun _ h => by cases h)
  have hslots : Inv.slots S' := by
    refine ⟨fun y u hu => ?_, fun y ps h p hp => ?_⟩
    · rw [hH.owner]; exact s22.1 y u ((hcv' _ _).mp hu)
    · rw [hH.owner] at h; rw [hH.ops]; exact s22.2 y ps h p hp
  have hco : Inv.clientOps S' := by
    have hso' : S'.slotOp = S.slotOp := by funext s; simp only [Sys.slotOp, hH.owner]
    exact ExecOrd.clientOps_frame s23 hH.ops hH.gexec hH.fired (fun _ _ _ => by rw [hso'])
      (fun y v h => (hcv' _ _).mpr h)
  have hcm : Inv.commitMsgs S' := by
    intro fr to m' hm'
    rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, h, -⟩
    · obtain ⟨r, c, h⟩ := s24 fr to m' hm'
      exact ⟨r, c, hH.ev_old h⟩
    · cases h
  have hpk : Inv.pendingKind S' := by
    intro r b' hb'
    rw [hH.pending] at hb'
    by_cases hr : r = i
    · subst hr; rw [upd_same] at hb'
      obtain ⟨rfl, -⟩ := norm_some hb'
      rw [hBm]; rfl
    · rw [upd_other _ _ _ _ hr] at hb'; exact s25 r b' hb'
  have hrt : Inv.replyTargets S' := by
    intro fr to m' y hm' hy hk'
    rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, rfl, -⟩
    · obtain ⟨w1, lb1, h1, hl1⟩ := s3 fr to m' y hm' hy hk'
      rcases R2 to y w1 h1 with ⟨rfl, rfl, rfl⟩ | h
      · exact ⟨w', lbR, R3, W7⟩
      · exact ⟨w1, lb1, h, hl1⟩
    · rcases hk' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
  have hmw : Inv.msgWf S' := by
    intro fr to m' hm'
    rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, rfl, -⟩
    · exact s2 fr to m' hm'
    · refine ⟨fun q n' hq' => ?_, fun ds hds => by simp [Msg.depsFields] at hds⟩
      simp only [Msg.rawId, Option.some.injEq, Prod.mk.injEq] at hq'
      obtain ⟨rfl, rfl⟩ := hq'
      exact ⟨hzq.1, hzq.2, hzi, by rw [toN_W32' _ (by omega)]; exact hxi⟩
  have hntpa : Inv.noTPA S' := by
    intro fr to m' hm'
    rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, rfl, -⟩
    · exact s4 fr to m' hm'
    · exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
  have hrepo : Inv.reports S' := by
    obtain ⟨c1', c2', c3', c4', c5', c6', c7', c8', c9'⟩ := s27
    refine ⟨fun r m' e hp => ?_, fun r m' e hp => ?_, fun r m' e hp => ?_,
      fun r m' e hp c u hb' => ?_, fun r m' e hr hp => ?_,
      fun r y c st st' u u' h1 h2 h3 h4 => c6' r y c st st' u u' h1 h2 (hvote _ _ _ _ _ h3)
        (hvote _ _ _ _ _ h4), fun y u m' e h1 h2 h3 => ?_,
      fun r y u h1 u' => fastBlocked_mono hsafeM (c8' r y u (hacc _ _ _ _ h1) u'),
      fun r m' e hp => ?_⟩
    · rcases (hprepR r m' e).mp hp with hp0 | ⟨rfl, rfl, rfl⟩
      · exact c1' r m' e hp0
      · rw [P6]; exact hA.stRange _ hi x w hw
    · rcases (hprepR r m' e).mp hp with hp0 | ⟨rfl, rfl, rfl⟩
      · exact c2' r m' e hp0
      · intro hs; rw [P6] at hs; rw [P5]; exact (hA.noneRec _ hi x w hw hs).1
    · rcases (hprepR r m' e).mp hp with hp0 | ⟨rfl, rfl, rfl⟩
      · exact c3' r m' e hp0
      · intro hs; rw [P6] at hs; rw [P9]; exact (hwq.2.2.2 hs).1
    · rcases (hprepR r m' e).mp hp with hp0 | ⟨rfl, rfl, rfl⟩
      · exact c4' r m' e hp0 c u (hevB _ _ _ _ hb' hp0.1)
      · obtain ⟨pp, pp', -, h1, -⟩ := hb'
        have hv := hvote _ _ _ _ _ (List.mem_of_getElem? h1)
        rw [hprx] at hv
        intro hle; rw [P6]; rw [P5] at hle
        exact hA.accKeep _ hi x w hw c u hv hle
    · rcases (hprepR r m' e).mp hp with hp0 | ⟨rfl, rfl, rfl⟩
      · obtain ⟨w1, h1, hle⟩ := c5' r m' e hr hp0
        obtain ⟨w2, h2, -, -, -, -, -, -, hle'⟩ := C2 r _ w1 h1
        exact ⟨w2, h2, Int.le_trans hle hle'⟩
      · rw [hprx, P4]; exact ⟨w', R3, by rw [W2]; exact Int.le_refl _⟩
    · rcases (hprepR _ m' e).mp h2 with hp0 | ⟨hr, rfl, rfl⟩
      · exact c7' y u m' e (hold _ _ h1 (fun _ _ h => by cases h) (fun _ h => by cases h)) hp0 h3
      · exfalso
        obtain ⟨-, c, hc⟩ := hA.fastCommitEv _ y u (hold _ _ h1 (fun _ _ h => by cases h)
          (fun _ h => by cases h))
        rw [hprx] at h3; subst h3
        obtain ⟨w1, h1', hs⟩ := hA.commitRec _ _ c u (by rw [← hr]; exact hi) hc
        rw [← hr, hw] at h1'; cases h1'; exact hnc' hs
    · rcases (hprepR r m' e).mp hp with hp0 | ⟨rfl, rfl, rfl⟩
      · exact c9' r m' e hp0
      · rw [P5, P4]; have := s5.1 _ hi x w hw; omega
  refine ⟨⟨hwf, hmw, hrt, hntpa, hbal, hown, hop, hvf, hrr, hhi, hlbI,
    hagr, hdc, chosenSafe_of_safe _ hwf hbal hown hvf hsafe, hdcv, hwit, hac, hexec.1,
    hexec.2.1, hexec.2.2.1, hexec.2.2.2, hslots, hco, hcm, hpk, hsafe, hrepo⟩, ?_⟩
  have hlbv : ∀ r y w2 lb2, (S'.rep r).inst y = some w2 → w2.lb = some lb2 →
      (i = r ∧ x = y ∧ w' = w2 ∧ lbR = lb2) ∨
        ((S.rep r).inst y = some w2 ∧ ¬ (r = i ∧ y = x)) := by
    intro r y w2 lb2 h2 hl2
    rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | h
    · rw [W7] at hl2; cases hl2; exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inr h
  have hcntPA : ∀ fr to y c, S'.cnt fr to (Msg.isPAat y c) = S.cnt fr to (Msg.isPAat y c) :=
    fun fr to y c => hcntP fr to _ rfl
  have hcntAcc : ∀ fr to y c, S'.cnt fr to (Msg.isAccAt y c) = S.cnt fr to (Msg.isAccAt y c) :=
    fun fr to y c => hcntP fr to _ rfl
  have hcntPAR : ∀ fr to y c, S'.cnt fr to (Msg.isPARat y c) = S.cnt fr to (Msg.isPARat y c) :=
    fun fr to y c => hcntP fr to _ rfl
  have hcntAR : ∀ fr to y c, S'.cnt fr to (Msg.isARat y c) = S.cnt fr to (Msg.isARat y c) :=
    fun fr to y c => hcntP fr to _ rfl
  have hlbn : ∀ lb1, w.lb = some lb1 → zz lb1.lastTriedBallot < zz n := by
    intro lb1 hl1; have := hA.lastLeBal i hi x w lb1 hw hl1; omega
  exact {
    stRange := fun r hr y w2 h2 => by
      obtain ⟨w1, h1, -, -, e3, -⟩ := C1 r y w2 h2
      rw [e3]; exact hA.stRange r hr y w1 h1
    cmdsSome := fun r hr y w2 h2 hs => by
      obtain ⟨w1, h1, e1, -, e3, -⟩ := C1 r y w2 h2
      rw [e3] at hs; rw [e1]; exact hA.cmdsSome r hr y w1 h1 hs
    noneRec := fun r hr y w2 h2 hs => by
      obtain ⟨w1, h1, -, e2, e3, -⟩ := C1 r y w2 h2
      rw [e3] at hs
      obtain ⟨d1, d2⟩ := hA.noneRec r hr y w1 h1 hs
      exact ⟨by rw [e2]; exact d1, fun c st u hv0 => d2 c st u (hvote _ _ _ _ _ hv0)⟩
    vbalNonneg := fun r hr y w2 h2 hs => by
      obtain ⟨w1, h1, -, e2, e3, -⟩ := C1 r y w2 h2
      rw [e3] at hs; rw [e2]; exact hA.vbalNonneg r hr y w1 h1 hs
    votesLe := fun r hr y w2 h2 c st u hv0 => by
      obtain ⟨w1, h1, -, e2, -⟩ := C1 r y w2 h2
      rw [e2]; exact hA.votesLe r hr y w1 h1 c st u (hvote _ _ _ _ _ hv0)
    recVote := fun r hr y w2 h2 hs => by
      obtain ⟨w1, h1, -, e2, e3, -, -, -, e7, -⟩ := C1 r y w2 h2
      rw [e3] at hs ⊢; rw [e2, e7]; exact hH.ev_old (hA.recVote r hr y w1 h1 hs)
    accKeep := fun r hr y w2 h2 c u hv0 hle => by
      obtain ⟨w1, h1, -, e2, e3, -⟩ := C1 r y w2 h2
      rw [e2] at hle; rw [e3]; exact hA.accKeep r hr y w1 h1 c u (hvote _ _ _ _ _ hv0) hle
    recCommit := fun r hr y w2 h2 hs => by
      obtain ⟨w1, h1, -, -, e3, -, -, -, -, hle⟩ := C1 r y w2 h2
      rw [e3] at hs
      obtain ⟨c, u, d1, d2⟩ := hA.recCommit r hr y w1 h1 hs
      exact ⟨c, u, hH.ev_old d1, Int.le_trans d2 hle⟩
    commitRec := fun r y c u hr he => by
      have h := hold _ _ he (fun _ _ h => by cases h) (fun _ h => by cases h)
      obtain ⟨w1, h1, hs⟩ := hA.commitRec r y c u hr h
      obtain ⟨w2, h2, -, -, e3, -⟩ := C2 r y w1 h1
      exact ⟨w2, h2, by rw [e3]; exact hs⟩
    fastCommitEv := fun r y u he => by
      obtain ⟨d1, c, d2⟩ := hA.fastCommitEv r y u
        (hold _ _ he (fun _ _ h => by cases h) (fun _ h => by cases h))
      exact ⟨d1, c, hH.ev_old d2⟩
    makerLb := fun r y c hr he => by
      rcases hmk1 r y c he with h | ⟨rfl, rfl, rfl⟩
      · obtain ⟨w1, lb1, h1, hl1, hle⟩ := hA.makerLb r y c hr h
        rcases R2 r y w1 h1 with ⟨rfl, rfl, rfl⟩ | h'
        · exact ⟨w', lbR, R3, W7, by rw [L8]; have := hlbn lb1 hl1; omega⟩
        · exact ⟨w1, lb1, h', hl1, hle⟩
      · exact ⟨w', lbR, R3, W7, by rw [L8]; exact Int.le_refl _⟩
    lastLeBal := fun r hr y w2 lb2 h2 hl2 => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, rfl, rfl⟩ | ⟨h, -⟩
      · rw [L8, W2]; exact Int.le_refl _
      · exact hA.lastLeBal r hr y w2 lb2 h hl2
    peerOk := fun r hr => by rw [(hfl r).2.1]; exact hA.peerOk r hr
    crtOwn := fun r hr q hq' => by rw [(hfl r).2.2.1, (hfl q).2.2.1]; exact hA.crtOwn r hr q hq'
    crtRec := fun r hr y w2 h2 => by
      rw [(hfl y.q).2.2.1]
      obtain ⟨w1, h1, -⟩ := C1 r y w2 h2
      exact hA.crtRec r hr y w1 h1
    crtMsg := fun fr to m' y hm' hy => by
      rw [(hfl y.q).2.2.1]
      rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, rfl, -⟩
      · exact hA.crtMsg fr to m' y hm' hy
      · simp only [Msg.instOf, Option.some.injEq] at hy
        rw [hx'] at hy; subst hy; exact hA.crtRec i hi x w hw
    crtEv := fun r e y he hy => by
      rw [(hfl y.q).2.2.1]
      rcases (hE r e).mp he with h | ⟨-, rfl | rfl⟩
      · exact hA.crtEv r e y h hy
      · simp only [Event.instOf, Option.some.injEq] at hy; subst hy
        exact ⟨hq, hA.crtRec i hi x w hw⟩
      · simp only [Event.instOf, Option.some.injEq] at hy; rw [hprx] at hy; subst hy
        exact ⟨hq, hA.crtRec i hi x w hw⟩
    ownRow := fun q hq' j hj => by
      rw [(hfl q).2.2.1] at hj
      obtain ⟨w1, lb1, h1, hl1⟩ := hA.ownRow q hq' j hj
      rcases R2 q _ w1 h1 with ⟨rfl, hx'', rfl⟩ | h
      · exact ⟨w', lbR, by rw [← hx'']; exact R3, W7⟩
      · exact ⟨w1, lb1, h, hl1⟩
    paNoAcc := fun r hr y w2 lb2 h2 hl2 hs u hv0 => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨rfl, rfl, -, rfl⟩ | ⟨h, -⟩
      · rw [L8] at hv0; exact hnoAcc _ u (hacc _ _ _ _ hv0)
      · exact hA.paNoAcc r hr y w2 lb2 h hl2 hs u (hacc _ _ _ _ hv0)
    paLeader := fun r hr y w2 lb2 h2 hl2 hs hp hc' hb' => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨rfl, rfl, -, rfl⟩ | ⟨h, -⟩
      · obtain ⟨u, hu⟩ := hp; rw [L8] at hu; exact absurd (hph _ _ _ _ hu) (hnoPh _ u)
      · obtain ⟨u, hu⟩ := hp
        exact hA.paLeader r hr y w2 lb2 h hl2 hs ⟨u, hph _ _ _ _ hu⟩ hc' hb'
    prepNoProp := fun r hr y w2 lb2 h2 hl2 hp => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨rfl, rfl, -, rfl⟩ | ⟨h, -⟩
      · rw [L8]
        refine ⟨mb2, fun u h' => hnoPh _ u (hph _ _ _ _ h'),
          fun u h' => hnoAcc _ u (hacc _ _ _ _ h'), fun e he hn' => ?_, fun hl => ?_⟩
        · rw [L5] at he; simp only [List.mem_singleton] at he; subst he
          simp only [decide_eq_true_eq] at hn'
          rw [P6]
          by_cases hs : w.status = stNONE
          · exact hs
          · exact absurd hn' (hA.cmdsSome _ hi x w hw hs)
        · rw [L12] at hl; simp only [decide_eq_true_eq] at hl
          rw [L5]
          exact ⟨_, List.mem_singleton_self _, by simp only; rw [P1, toN_W32 _ hi]; exact hl⟩
      · obtain ⟨d1, d2, d3, d4, d5⟩ := hA.prepNoProp r hr y w2 lb2 h hl2 hp
        exact ⟨d1, fun u h' => d2 u (hph _ _ _ _ h'), fun u h' => d3 u (hacc _ _ _ _ h'), d4, d5⟩
    paMsgOnce := fun fr to y c => by rw [hcntPA]; exact hA.paMsgOnce fr to y c
    accMsgOnce := fun fr to y c => by rw [hcntAcc]; exact hA.accMsgOnce fr to y c
    paVoteDeliv := fun r y c st u hst hv0 => by
      rcases hA.paVoteDeliv r y c st u hst (hvote _ _ _ _ _ hv0) with ⟨u0, h0⟩ | h0
      · exact Or.inl ⟨u0, hH.ev_old h0⟩
      · exact Or.inr (fun fr' => hallP _ _ _ rfl (h0 fr'))
    parOnce := fun a r y c h1 => by
      rw [hcntPAR] at h1 ⊢
      obtain ⟨d1, d2⟩ := hA.parOnce a r y c h1
      exact ⟨d1, hallP _ _ _ rfl d2⟩
    arFrom := fun a r m' hm' => by
      rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, h, -⟩
      · obtain ⟨c, u, d1, d2⟩ := hA.arFrom a r m' hm'
        exact ⟨c, u, d1, hH.ev_old d2⟩
      · cases h
    arOnce := fun a r y c h1 => by
      rw [hcntAR] at h1 ⊢
      rcases hA.arOnce a r y c h1 with ⟨w1, lb1, h1', hl1, hlt'⟩ | ⟨d1, d2⟩
      · refine Or.inl ?_
        rcases R2 r y w1 h1' with ⟨rfl, rfl, rfl⟩ | h
        · exact ⟨w', lbR, R3, W7, by rw [L8]; have := hlbn lb1 hl1; omega⟩
        · exact ⟨w1, lb1, h, hl1, hlt'⟩
      · exact Or.inr ⟨d1, hallP _ _ _ rfl d2⟩
    commitBal := fun fr to m' hm' => by
      rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, h, -⟩
      · exact hA.commitBal fr to m' hm'
      · cases h
    sentPR := fun r to m' he => by
      have he0 := hold _ _ he (fun _ _ h => by cases h) (fun _ h => by cases h)
      obtain ⟨d1, d2, d3⟩ := hA.sentPR r to m' he0
      refine ⟨fun hr => ?_, fun c st u hb' => d2 c st u ?_, fun to' m2 hb' hy => d3 to' m2 ?_ hy⟩
      · obtain ⟨w1, h1, hle⟩ := d1 hr
        obtain ⟨w2, h2, -, -, -, -, -, -, hle'⟩ := C2 r _ w1 h1
        exact ⟨w2, h2, Int.le_trans hle hle'⟩
      · obtain ⟨pp, pp', hlt', h1, h2⟩ := hb'
        exact hevB _ _ _ _ ⟨pp, pp', hlt', h1, h2⟩ (hvote _ _ _ _ _ (List.mem_of_getElem? h2))
      · obtain ⟨pp, pp', hlt', h1, h2⟩ := hb'
        exact hevB _ _ _ _ ⟨pp, pp', hlt', h1, h2⟩
          (hold _ _ (List.mem_of_getElem? h2) (fun _ _ h => by cases h) (fun _ h => by cases h))
    confCover := fun r hr e y cy he hrec c hc' => by
      rw [(hfl r).2.2.2.1]
      rcases (hE r e).mp he with h | ⟨-, rfl | rfl⟩
      · exact hA.confCover r hr e y cy h hrec c hc'
      · cases hrec
      · cases hrec
    classWf := fun r hr => by
      have hcl : (S'.rep r).lastScan = (S.rep r).lastScan ∧
          (S'.rep r).lastPut = (S.rep r).lastPut := by
        rw [hH.rep]; by_cases h : r = i
        · subst h; simp [RState.setInst]
        · simp [upd_apply, h]
      refine AuxProof.clsWf_keep (hA.classWf r hr) hcl.1 hcl.2 (fun y h => ?_)
      obtain ⟨w1, h1⟩ := Option.ne_none_iff_exists'.mp h
      rcases R2 r y w1 h1 with ⟨rfl, rfl, -⟩ | h2
      · rw [R3]; simp
      · rw [h2]; simp
    classCover := fun r hr e y cy he hrec => by
      have hcl : (S'.rep r).lastScan = (S.rep r).lastScan ∧
          (S'.rep r).lastPut = (S.rep r).lastPut := by
        rw [hH.rep]; by_cases h : r = i
        · subst h; simp [RState.setInst]
        · simp [upd_apply, h]
      rw [hcl.1, hcl.2]
      rcases (hE r e).mp he with h | ⟨-, rfl | rfl⟩
      · exact hA.classCover r hr e y cy h hrec
      · cases hrec
      · cases hrec
    paAttrs := fun r y c st u hst hv0 =>
      hH.ev_old (hA.paAttrs r y c st u hst (hvote _ _ _ _ _ hv0))
    valOk := fun r y c u hv0 => by
      rw [hH.owner]; exact hA.valOk r y c u (hv0.imp (hph _ _ _ _) (hacc _ _ _ _))
    cmdsNe := by
      obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hA.cmdsNe
      refine ⟨fun fr to m' hm' cs hcs => ?_,
        fun r hr y w2 cs h2 hc' => ?_, fun r hr y w2 lb2 cs h2 hl2 hc' => ?_,
        fun fr to m' hm' => ?_, fun r m' he hs => ?_,
        fun r y c u hv0 => n6 r y c u (hv0.imp (hph _ _ _ _) (hacc _ _ _ _))⟩
      · rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, rfl, -⟩
        · exact n1 fr to m' hm' cs hcs
        · simp [Msg.commandField] at hcs
      · obtain ⟨w1, h1, e1, -⟩ := C1 r y w2 h2
        rw [e1] at hc'; exact n2 r hr y w1 cs h1 hc'
      · rcases hlbv r y w2 lb2 h2 hl2 with ⟨rfl, rfl, -, rfl⟩ | ⟨h, -⟩
        · rw [L9] at hc'; exact n2 _ hi x w cs hw hc'
        · exact n3 r hr y w2 lb2 cs h hl2 hc'
      · rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, h, -⟩
        · exact n4 fr to m' hm'
        · cases h
      · rcases (hE r _).mp he with h | ⟨-, h | h⟩
        · exact n5 r m' h hs
        · cases h
        · simp only [Event.selfReply.injEq] at h; subst h
          rw [P6] at hs; rw [P7]
          obtain ⟨cs, hcs⟩ := Option.ne_none_iff_exists'.mp (hA.cmdsSome _ hi x w hw hs)
          rw [hcs]; exact n2 _ hi x w cs hw hcs
    prSent := fun fr to m' hm' => by
      rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, h, -⟩
      · exact hH.ev_old (hA.prSent fr to m' hm')
      · cases h
    selfOk := fun r m' he hs => by
      rcases (hE r _).mp he with h | ⟨-, h | h⟩
      · exact hA.selfOk r m' h hs
      · cases h
      · simp only [Event.selfReply.injEq] at h; subst h
        rw [P6] at hs; rw [P9]; exact hwq.2.2.2 hs
    selfRaw := fun r m' he => by
      rcases (hE r _).mp he with h | ⟨-, h | h⟩
      · exact hA.selfRaw r m' h
      · cases h
      · simp only [Event.selfReply.injEq] at h; subst h
        rw [P2, toN_W32 _ hq]
    pm := by
      have hP := hA.pm
      have hmono : ∀ r e, S.ev r e → S'.ev r e := fun r e h => hH.ev_old h
      have hsent : ∀ fr to (m' : Msg), m' ∈ S.sent fr to → m' ∈ S'.sent fr to := by
        intro fr to m' h; rw [hH.sent]; exact h
      have hmsgO : ∀ fr to (m' : Msg), m' ∈ S'.msgs fr to → (∀ p, m' ≠ .prepare p) →
          m' ∈ S.msgs fr to := by
        intro fr to m' h hn
        rcases (hmsgs _ _ _).mp h with h | ⟨-, rfl, -⟩
        · exact h
        · exact absurd rfl (hn _)
      have hcv : ∀ y u, S.committedVal y u → S'.committedVal y u := fun y u h => (hcv' y u).mpr h
      have hbalP : ∀ r y w1, (S.rep r).inst y = some w1 →
          ∃ w2, (S'.rep r).inst y = some w2 ∧ zz w1.bal ≤ zz w2.bal := by
        intro r y w1 h
        obtain ⟨w2, h2, -, -, -, -, -, -, hle⟩ := C2 r y w1 h
        exact ⟨w2, h2, hle⟩
      have hcmE : ∀ r y c u, S'.ev r (.commit y c u) → S.ev r (.commit y c u) :=
        fun r y c u h => hold r _ h (fun _ _ h => by cases h) (fun _ h => by cases h)
      have hBpa : ∀ b', B.norm = some b' → b'.trackPA = false ∧ ∀ y c, b'.m.isPAat y c = false := by
        intro b' hb'
        obtain ⟨rfl, -, -⟩ := norm_some hb'
        refine ⟨by rw [← hB]; rfl, fun y c => ?_⟩
        rw [hBm]; rfl
      exact {
        arOk := PMProof.arOk_frame hP (fun a r m' h => hmsgO _ _ _ h (fun _ h => by cases h)) hacc
          (fun q y c v h => Or.inl (hvote _ _ _ _ _ h)) hmono hcv hbalP
        commitProp := PMProof.commitProp_frame hP hcmE hmono
        commitMsgProp := PMProof.commitMsgProp_frame hP
          (fun fr to m' h => hmsgO _ _ _ h (fun _ h => by cases h)) hmono
        lbProp := fun r hr y w2 lb2 h2 hl2 hs hv => by
          obtain ⟨v, hv⟩ := hv
          rcases hlbv r y w2 lb2 h2 hl2 with ⟨rfl, rfl, -, rfl⟩ | ⟨h, -⟩
          · rw [L8] at hv; exact absurd (hacc _ _ _ _ hv) (hnoAcc _ v)
          · exact PMProof.propAt_mono hmono (hP.lbProp r hr y w2 lb2 h hl2 hs ⟨v, hacc _ _ _ _ hv⟩)
        parCom := PMProof.parCom_frame hP (fun a r m' h => hmsgO _ _ _ h (fun _ h => by cases h))
          hmono
        parSt := PMProof.parSt_frame hP (fun a r m' h => hmsgO _ _ _ h (fun _ h => by cases h))
          hsent
        paFresh := fun r hr y w2 lb2 h2 hl2 hs h0 hp => by
          rcases hlbv r y w2 lb2 h2 hl2 with ⟨rfl, rfl, -, rfl⟩ | ⟨h, -⟩
          · obtain ⟨v, hv⟩ := hp; rw [L8] at hv; exact absurd (hph _ _ _ _ hv) (hnoPh _ v)
          · obtain ⟨v, hv⟩ := hp
            exact hP.paFresh r hr y w2 lb2 h hl2 hs h0 ⟨v, hph _ _ _ _ hv⟩
        paCmds := fun r hr y w2 lb2 h2 hl2 hs v hv => by
          rcases hlbv r y w2 lb2 h2 hl2 with ⟨rfl, rfl, -, rfl⟩ | ⟨h, -⟩
          · rw [L8] at hv; exact absurd (hph _ _ _ _ hv) (hnoPh _ v)
          · exact hP.paCmds r hr y w2 lb2 h hl2 hs v (hph _ _ _ _ hv)
        paSent := pmr_paSent hP hH hidle.1 (fun b' hb' => (hBpa b' hb').1)
          (fun y w2 lb2 h2 hl2 hlt' => by
            rcases hlbv _ y w2 lb2 h2 hl2 with ⟨-, rfl, -, rfl⟩ | ⟨h, -⟩
            · rw [L8] at hlt'; exact absurd hlt' hnI
            · exact h)
        pendPA := fun r b' hb' y c hc => by
          rw [hH.pending] at hb'
          by_cases hr : r = i
          · subst hr; rw [upd_same] at hb'; rw [(hBpa b' hb').2 y c] at hc; cases hc
          · rw [upd_other _ _ _ _ hr] at hb'; exact hP.pendPA r b' hb' y c hc
        paVoteMsg := PMProof.paVoteMsg_frame hP hvote hsent
        parNoPA := PMProof.parNoPA_frame hP
          (fun a r m' h => hmsgO _ _ _ h (fun _ h => by cases h)) hvote
        aeF := fun r hr y w2 lb2 h2 hl2 hs hae => by
          rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
          · rw [← hlbR] at hae; cases hae
          · obtain ⟨a, a', m1, m1', g1, g2, g3, g4, g5, g6, g7⟩ :=
              hP.aeF r hr y w2 lb2 h hl2 hs hae
            exact ⟨a, a', m1, m1', hsent _ _ _ g1, hsent _ _ _ g2, g3, g4, g5, g6, g7⟩
        repLead := fun r m' e hp hr => by
          rcases (hprepR r m' e).mp hp with hp | ⟨rfl, rfl, -⟩
          · obtain ⟨w1, h1, hlt'⟩ := hP.repLead r m' e hp hr
            obtain ⟨w2, h2, hle⟩ := hbalP _ _ w1 h1
            exact ⟨w2, h2, Int.lt_of_lt_of_le hlt' hle⟩
          · rw [hprx]
            refine ⟨w', R3, ?_⟩
            rw [W2, zz_initBal x hq]
            have : x.q < nR := hq
            omega
        paGe := PMProof.paGe_frame hP hvote hph
        phAttrs := PMProof.phAttrs_frame hP hph hmono
        accWit := PMProof.accWit_frame hP hacc hmono hcv
        accVote := PMProof.accVote_frame hP hacc hmono
        cmdSafe := CmdSafeProof.cmdSafe_frame hP hsafeM hph
        accSup := CmdSafeProof.accSup_frame hP hmono hacc },
    ownerCrt := fun y ps h => by
      rw [hH.owner] at h; rw [(hfl y.q).2.2.1]; exact hA.ownerCrt y ps h
    execLo := AuxProof.execLo_of_eq hA.execLo (fun r _ => (hfl r).2.2.2.2.1)
    exec := ExecOrd.invExec_hs hS.1 hA.exec hH hidle hagr (by rw [← hS']; funext r; simp [Out.reprop]) (fun r y h => by rw [hrep, if_neg]; rintro ⟨h1, h2⟩; rcases h with h | h; exact h h1; exact h h2) R3
      (fun w0 h0 _ => by rw [hw] at h0; cases h0; exact W1)
      (fun lb2 hl hne => by
        rw [W7] at hl; cases hl; rw [L1] at hne
        cases hlw : w.lb with
        | none => rw [hlw] at hne; exact absurd rfl hne
        | some lb0 => rw [hlw] at hne; exact ⟨w, lb0, hw, hlw, hne⟩) }

theorem applyStep_same (S : Sys) (i : Nat) : S.applyStep i (S.rep i, []) = S := by
  simp only [Sys.applyStep, List.foldl_nil, upd_eta]

/-- **`startRecoveryForInstance` keeps the invariant.** -/
theorem inv_step_recover' (S : Sys) (i : Nat) (x : InstId) (hS : Inv S) (hi : i < nR)
    (hidle : S.idle i) (hq : x.q < nR) (hx : (x.i : Int) ≤ zz ((S.rep i).crtInstance x.q)) :
    Inv (S.applyStep i (hRecover (S.rep i) x)) := by
  -- the main case, for a state holding a record of `x`
  have main : ∀ S0 : Sys, Inv S0 → S0.idle i → ∀ w, (S0.rep i).inst x = some w →
      Inv (S0.applyStep i (hRecover (S0.rep i) x)) := by
    intro S0 hS0 hidle0 w hw
    by_cases hnc : stGe w.status stCOMMITTED = true ∧ w.cmds ≠ none
    · have : hRecover (S0.rep i) x = (S0.rep i, []) := by
        unfold hRecover
        rw [getOrDefault_eq, show recOr (S0.rep i) x = w by simp [recOr, hw],
          setInst_self _ x w hw]
        simp only; rw [if_pos hnc]
      rw [this, applyStep_same]; exact hS0
    by_cases hov : (2 ^ 31 - 1 : Int) < makeBallotZ (S0.rep i) w.bal (W32 0)
    · have : hRecover (S0.rep i) x = (S0.rep i, []) := by
        unfold hRecover
        rw [getOrDefault_eq, show recOr (S0.rep i) x = w by simp [recOr, hw],
          setInst_self _ x w hw]
        simp only; rw [if_neg hnc, if_pos hov]
      rw [this, applyStep_same]; exact hS0
    · exact inv_recover_start S0 i x w hS0 hi hidle0 hq hw hnc hov
  cases hw : (S.rep i).inst x with
  | some w => exact main S hS hidle w hw
  | none =>
    have h0 := inv_default_rec S i x hS hi hidle hq hx hw
    generalize hS0 : S.applyStep i ((S.rep i).setInst x (newInstanceDefault x), []) = S0 at h0
    have hrep0 : S0.rep i = (S.rep i).setInst x (newInstanceDefault x) := by
      rw [← hS0]; simp
    have hidle0 : S0.idle i := by
      rw [← hS0]; refine ⟨?_, ?_⟩
      · simp only [Sys.applyStep_pending]; simp [hidle.1]; rfl
      · simp only [Sys.applyStep, List.foldl_nil]; exact hidle.2
    have hw0 : (S0.rep i).inst x = some (newInstanceDefault x) := by
      rw [hrep0]; simp [RState.setInst]
    have hrec : hRecover (S.rep i) x = hRecover (S0.rep i) x := by
      unfold hRecover
      rw [getOrDefault_eq, getOrDefault_eq,
        show recOr (S.rep i) x = newInstanceDefault x by simp [recOr, hw],
        show recOr (S0.rep i) x = newInstanceDefault x by simp [recOr, hw0],
        setInst_self _ x _ hw0, hrep0]
    have happ : ∀ r, S.applyStep i r = S0.applyStep i r := by
      intro r; rw [← hS0]
      simp only [Sys.applyStep, List.foldl_nil, upd_upd_same]
    rw [hrec, happ]
    exact main S0 h0 hidle0 _ hw0

end RecoverProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
