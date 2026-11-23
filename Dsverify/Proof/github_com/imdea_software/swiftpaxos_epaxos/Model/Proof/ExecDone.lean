/-
The executor ends an instance (`Sys.instDone`, p-modelexec): the instance's record goes from
COMMITTED to EXECUTED and moves from the component to the log. The execution sequence (log, then
component) is unchanged, so are the executed slots (`lexec`) and the global sequences.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.ExecStep
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.AuxFrameX

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs AuxProof SafeProof

namespace ExecOrd

section
variable {S : Sys} (hS : Inv S) {i : Nat} {x : InstId} {rest : List InstId} {w : InstRec}
  (hi : i < nR) (hcur : S.execCur i = x :: rest) (hw : (S.rep i).inst x = some w)
  (hidx : S.execIdx i = (w.cmds.getD []).length)
include hS hi hcur hw hidx

theorem inv_step_instDone'' : Inv (S.instDone i x rest) := by
  have h0 := hS.1
  have hX := hS.2.exec
  -- the record is committed
  have hcne : S.execCur i ≠ [] := by rw [hcur]; simp
  obtain ⟨done, C, hsort, hCn, hdone, hready, hclosed, hscc, -⟩ := ((I0.ecu h0) i hi).2 hcne
  obtain ⟨w0, hw0, hst, hcm⟩ := hready x (by rw [hcur]; simp)
  rw [hw] at hw0; cases hw0
  have hcvx := ((I0.agr h0).2 i hi x w hw (Or.inl hst)).2
  have hxl : x ∉ S.execLog i := by
    intro h; obtain ⟨w', hw', hs'⟩ := ((I0.ecl h0 i hi).2.1 x).mp h
    rw [hw] at hw'; cases hw'; rw [hst] at hs'; exact absurd hs' (by decide)
  have hpend : S.pending i = none := by
    cases hp : S.pending i with
    | none => rfl
    | some b => exact absurd (h0.1.2.2.2.2.2.2.2 i b hp).2.1 hcne
  -- the step
  have erep : (S.instDone i x rest).rep = upd S.rep i (execDone (S.rep i) x) := rfl
  have elog : (S.instDone i x rest).execLog = upd S.execLog i (S.execLog i ++ [x]) := rfl
  have ecur : (S.instDone i x rest).execCur = upd S.execCur i rest := rfl
  have eidx : (S.instDone i x rest).execIdx = upd S.execIdx i 0 := rfl
  have esent : (S.instDone i x rest).sent = S.sent := rfl
  have eob : (S.instDone i x rest).outbox = S.outbox := rfl
  have epend : (S.instDone i x rest).pending = S.pending := rfl
  have edel : (S.instDone i x rest).delivered = S.delivered := rfl
  have eops : (S.instDone i x rest).ops = S.ops := rfl
  have echan : (S.instDone i x rest).proposeChan = S.proposeChan := rfl
  have eown : (S.instDone i x rest).owner = S.owner := rfl
  have egex : (S.instDone i x rest).gexec = S.gexec := rfl
  have efir : (S.instDone i x rest).fired = S.fired := rfl
  have ehist : (S.instDone i x rest).hist = S.hist := rfl
  generalize S.instDone i x rest = S' at *
  have hexd : execDone (S.rep i) x = (S.rep i).setInst x { w with status := stEXECUTED } := by
    simp [execDone, hw]
  have hrec : ∀ r y, (S'.rep r).inst y =
      if r = i ∧ y = x then some { w with status := stEXECUTED } else (S.rep r).inst y := by
    intro r y; rw [erep]
    by_cases h : r = i
    · subst h; simp only [upd_same, hexd, RState.setInst, upd_apply, true_and]
    · simp [upd_other _ _ _ _ h, h]
  have hfld : ∀ r, (S'.rep r).id = (S.rep r).id ∧ (S'.rep r).crtInstance = (S.rep r).crtInstance ∧
      (S'.rep r).conflicts = (S.rep r).conflicts ∧ (S'.rep r).execedUpTo = (S.rep r).execedUpTo ∧
      (S'.rep r).store = (S.rep r).store ∧ (S'.rep r).peerOrder = (S.rep r).peerOrder := by
    intro r; rw [erep]
    by_cases h : r = i
    · subst h; simp [hexd, RState.setInst]
    · simp [upd_other _ _ _ _ h]
  -- records: the same, or `x` at `i` executed
  have hfwd : ∀ r y w1, (S.rep r).inst y = some w1 → ∃ w2, (S'.rep r).inst y = some w2 ∧
      CoreEqX w1 w2 ∧ w2.lb = w1.lb ∧ w2.id = w1.id ∧
      (w2 = w1 ∨ (r = i ∧ y = x ∧ w1 = w ∧ w2 = { w with status := stEXECUTED })) := by
    intro r y w1 h1
    by_cases hc : r = i ∧ y = x
    · have : w1 = w := by rw [hc.1, hc.2, hw] at h1; exact (Option.some.inj h1).symm
      subst w1
      refine ⟨{ w with status := stEXECUTED }, by rw [hrec, if_pos hc], ⟨rfl, rfl, rfl, Or.inr ⟨hst, rfl⟩, rfl, rfl,
        fun lb' h => ⟨lb', h, LbEq.refl _⟩, fun lb h => ⟨lb, h, LbEq.refl _⟩⟩, rfl, rfl,
        Or.inr ⟨hc.1, hc.2, rfl, rfl⟩⟩
    · refine ⟨w1, by rw [hrec, if_neg hc]; exact h1, ⟨rfl, rfl, rfl, Or.inl rfl, rfl, rfl,
        fun lb' h => ⟨lb', h, LbEq.refl _⟩, fun lb h => ⟨lb, h, LbEq.refl _⟩⟩, rfl, rfl, Or.inl rfl⟩
  have hbwd : ∀ r y w2, (S'.rep r).inst y = some w2 → ∃ w1, (S.rep r).inst y = some w1 ∧
      CoreEqX w1 w2 ∧ w2.lb = w1.lb ∧ w2.id = w1.id ∧
      (w2 = w1 ∨ (r = i ∧ y = x ∧ w1 = w ∧ w2 = { w with status := stEXECUTED })) := by
    intro r y w2 h2
    rw [hrec] at h2
    split at h2
    · rename_i hc
      have : w2 = { w with status := stEXECUTED } := (Option.some.inj h2).symm
      subst w2
      exact ⟨w, by rw [hc.1, hc.2]; exact hw, ⟨rfl, rfl, rfl, Or.inr ⟨hst, rfl⟩, rfl, rfl,
        fun lb' h => ⟨lb', h, LbEq.refl _⟩, fun lb h => ⟨lb, h, LbEq.refl _⟩⟩, rfl, rfl,
        Or.inr ⟨hc.1, hc.2, rfl, rfl⟩⟩
    · exact ⟨w2, h2, ⟨rfl, rfl, rfl, Or.inl rfl, rfl, rfl,
        fun lb' h => ⟨lb', h, LbEq.refl _⟩, fun lb h => ⟨lb, h, LbEq.refl _⟩⟩, rfl, rfl, Or.inl rfl⟩
  have hexe' : ∀ r y, (S'.rep r).executed y ↔ (S.rep r).executed y ∨ (r = i ∧ y = x) := by
    intro r y
    constructor
    · rintro ⟨w2, h2, hs2⟩
      obtain ⟨w1, h1, -, -, -, e | ⟨e1, e2, -, -⟩⟩ := hbwd r y w2 h2
      · subst e; exact Or.inl ⟨w2, h1, hs2⟩
      · exact Or.inr ⟨e1, e2⟩
    · rintro (⟨w1, h1, hs1⟩ | ⟨rfl, rfl⟩)
      · obtain ⟨w2, h2, -, -, -, e | ⟨-, -, e3, e4⟩⟩ := hfwd r y w1 h1
        · subst w2; exact ⟨w1, h2, hs1⟩
        · exact ⟨w2, h2, by rw [e4]⟩
      · exact ⟨_, by rw [hrec, if_pos ⟨rfl, rfl⟩], rfl⟩
  have hdep : ∀ r a b, (S'.rep r).depEdge a b ↔ (S.rep r).depEdge a b := by
    intro r a b
    constructor
    · rintro ⟨w2, h2, h3, h4⟩
      obtain ⟨w1, h1, c, -⟩ := hbwd r a w2 h2
      exact ⟨w1, h1, h3, by rw [← c.2.2.2.2.2.1]; exact h4⟩
    · rintro ⟨w1, h1, h3, h4⟩
      obtain ⟨w2, h2, c, -⟩ := hfwd r a w1 h1
      exact ⟨w2, h2, h3, by rw [c.2.2.2.2.2.1]; exact h4⟩
  have hcmd : ∀ r y, cmdsAt (S'.rep r) y = cmdsAt (S.rep r) y := by
    intro r y
    cases h1 : (S.rep r).inst y with
    | none =>
      cases h2 : (S'.rep r).inst y with
      | none => simp [cmdsAt, h1, h2]
      | some w2 => obtain ⟨w1, h1', -⟩ := hbwd r y w2 h2; rw [h1] at h1'; cases h1'
    | some w1 =>
      obtain ⟨w2, h2, c, -⟩ := hfwd r y w1 h1
      simp [cmdsAt, h1, h2, c.1]
  have hle : ∀ r, sccLe (S'.rep r) = sccLe (S.rep r) := by
    intro r; funext a b
    have : ∀ y, ((S'.rep r).inst y).map (·.seq) = ((S.rep r).inst y).map (·.seq) := by
      intro y
      cases h1 : (S.rep r).inst y with
      | none =>
        cases h2 : (S'.rep r).inst y with
        | none => rfl
        | some w2 => obtain ⟨w1, h1', -⟩ := hbwd r y w2 h2; rw [h1] at h1'; cases h1'
      | some w1 =>
        obtain ⟨w2, h2, c, -⟩ := hfwd r y w1 h1
        simp [h2, c.2.2.2.2.1]
    simp only [sccLe, this]
  have hmsgs : S'.msgs = S.msgs := by
    funext fr to; simp only [Sys.msgs, Sys.intended, esent, eob, epend]
  have hcvS : ∀ y v, S'.committedVal y v ↔ S.committedVal y v := by
    intro y v; simp only [Sys.committedVal, Sys.ev, ehist, hmsgs]
  have hev : ∀ r e, S'.ev r e ↔ S.ev r e := by intro r e; simp only [Sys.ev, ehist]
  have hdE : S'.dEdge = S.dEdge := by funext a b; simp only [Sys.dEdge, hcvS]
  have hsO : S'.sccOrd = S.sccOrd := by funext a b; simp only [Sys.sccOrd, hcvS]
  have hes : ∀ r, S'.eseq r = S.eseq r := by
    intro r; simp only [Sys.eseq, elog, ecur, upd_apply]
    split
    · rename_i h; subst h; rw [hcur]; simp
    · rfl
  have hlx : ∀ r k, S'.lexec r k = S.lexec r k := by
    intro r k
    have hso : Sys.slotsOn (S'.rep r) = Sys.slotsOn (S.rep r) := by
      funext xs k; exact slotsOn_congr_cmds _ _ k xs (fun y _ => hcmd r y)
    unfold Sys.lexec Sys.curSlots
    simp only [hso, elog, ecur, eidx, upd_apply]
    split
    · rename_i h; subst h
      rw [hcur]
      have hall : (blk (S.rep r) k x).filter (fun e => decide (e.1.2 < S.execIdx r)) =
          blk (S.rep r) k x := by
        rw [List.filter_eq_self]
        intro e he
        obtain ⟨h0e, h1, -⟩ := (mem_blk _ _ _ e).mp he
        simp only [cmdsAt, hw, Option.bind_some] at h1
        simp only [decide_eq_true_eq]; omega
      have hz : ∀ y, (blk (S.rep r) k y).filter (fun e => decide (e.1.2 < 0)) = [] := by
        intro y; rw [List.filter_eq_nil_iff]; intro a _; simp
      cases rest with
      | nil => simp only [slotsOn_eq, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, hall]
      | cons y ys => simp only [slotsOn_eq, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, hall, hz, upd_same]
    · rfl
  -- `Inv0`
  have hinst_bal : ∀ r y w1, (S.rep r).inst y = some w1 → ∃ w2, (S'.rep r).inst y = some w2 ∧
      w2.bal = w1.bal ∧ (stGe w1.status stACCEPTED = true → stGe w2.status stACCEPTED = true) := by
    intro r y w1 h1
    obtain ⟨w2, h2, c, -⟩ := hfwd r y w1 h1
    refine ⟨w2, h2, c.2.1, fun hg => ?_⟩
    rcases c.2.2.2.1 with e | ⟨-, e⟩
    · rw [e]; exact hg
    · rw [e]; decide
  have hsm : SafeMono S S' := safeMono_same S S' hinst_bal (fun r e h => (hev r e).mpr h)
    (fun r e _ h => (hev r e).mp h) (fun fr to m h => by rw [hmsgs] at h; exact h)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27⟩ := h0
  have hwf : Inv.wf S' := by
    obtain ⟨w1', w2', w3', w4', w5', w6', w7', w8'⟩ := h1
    refine ⟨fun r hr => by rw [(hfld r).1]; exact w1' r hr, fun r hr y w2 h2' => ?_,
      fun r hr q hq => by rw [(hfld r).2.1]; exact w3' r hr q hq, fun r hr q k p hk => ?_,
      fun r hr q hq n hn => ?_, fun fr to h => by rw [hmsgs] at h; exact w6' fr to h,
      fun fr to n h => by rw [edel, esent] at *; exact w7' fr to n h, fun r b hb => ?_⟩
    · obtain ⟨w1, h1', c, hlb, hid, -⟩ := hbwd r y w2 h2'
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := w2' r hr y w1 h1'
      refine ⟨by rw [hid]; exact a1, a2, a3, fun hs => ?_, by rw [hlb]; exact a5,
        by rw [hlb]; exact a6, by rw [hlb, eown]; exact a7⟩
      rw [c.2.2.2.2.2.1]
      rcases c.2.2.2.1 with e | ⟨e0, -⟩
      · rw [e] at hs; exact a4 hs
      · exact a4 (by rw [e0]; decide)
    · rw [(hfld r).2.2.1] at hk
      obtain ⟨b1, b2, b3⟩ := w4' r hr q k p hk
      refine ⟨b1, fun h => ?_, fun h => ?_⟩
      · intro hn; obtain ⟨w1, h1'⟩ := Option.ne_none_iff_exists'.mp (b2 h)
        obtain ⟨w2, h2', -⟩ := hfwd r _ w1 h1'; rw [h2'] at hn; cases hn
      · intro hn; obtain ⟨w1, h1'⟩ := Option.ne_none_iff_exists'.mp (b3 h)
        obtain ⟨w2, h2', -⟩ := hfwd r _ w1 h1'; rw [h2'] at hn; cases hn
    · rw [(hfld r).2.2.2.1] at hn
      exact (hexe' r _).mpr (Or.inl (w5' r hr q hq n hn))
    · rw [epend] at hb
      obtain ⟨b1, b2, b3, b4, b5, b6, wb, lbb, hwb, hlbb⟩ := w8' r b hb
      have hri : r ≠ i := by intro e; subst e; rw [hpend] at hb; cases hb
      obtain ⟨w2, h2', -, hlb2, -⟩ := hfwd r _ wb hwb
      refine ⟨b1, by rw [ecur, upd_other _ _ _ _ hri]; exact b2, b3, b4, b5, b6, w2, lbb, h2',
        by rw [hlb2]; exact hlbb⟩
  have hbal : Inv.ballots S' := by
    refine ⟨fun r hr y w2 h2' => ?_, fun r hr y b st v hv => ?_⟩
    · obtain ⟨w1, h1', c, -⟩ := hbwd r y w2 h2'
      rw [c.2.1, c.2.2.1]; exact h5.1 r hr y w1 h1'
    · obtain ⟨w1, h1', hle'⟩ := h5.2 r hr y b st v ((hev _ _).mp hv)
      obtain ⟨w2, h2', c, -⟩ := hfwd r y w1 h1'
      exact ⟨w2, h2', by rw [c.2.1]; exact hle'⟩
  have hown : Inv.ballotOwner S' := by
    simp only [Inv.ballotOwner, Sys.ev, Sys.evBefore, ehist, hmsgs] at h6 ⊢; exact h6
  have hvf : Inv.votesFollowProposals S' := by
    simp only [Inv.votesFollowProposals, Sys.ev, ehist] at h8 ⊢; exact h8
  have hsafe : Inv.safe S' := safe_same S S' hinst_bal (fun r e h => (hev r e).mpr h)
    (fun r e _ h => (hev r e).mp h) (fun fr to m h => by rw [hmsgs] at h; exact h) h26
  have h0' : Inv0 S' := by
    refine ⟨hwf, ?_, ?_, ?_, hbal, hown, ?_, hvf, ?_, ?_, ?_, ?_, ?_,
      chosenSafe_of_safe _ hwf hbal hown hvf hsafe, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hsafe, reports_frame hsm (fun r m e h => by simpa [Sys.prepReport, hev, hmsgs] using h)
        (fun r m e y b st u _ h => by simpa [Sys.evBefore, ehist] using h)
        (fun r e _ h => (hev r e).mp h) h27⟩
    · simp only [Inv.msgWf, hmsgs]; exact h2
    · intro fr to m y hm hy hk
      rw [hmsgs] at hm
      obtain ⟨w1, lb, h1', hlb⟩ := h3 fr to m y hm hy hk
      obtain ⟨w2, h2', -, hlb2, -⟩ := hfwd to y w1 h1'
      exact ⟨w2, lb, h2', by rw [hlb2]; exact hlb⟩
    · simp only [Inv.noTPA, hmsgs]; exact h4
    · simp only [Inv.oneProposal, Sys.ev, ehist] at h7 ⊢; exact h7
    · simp only [Inv.repliesReportVotes, Sys.prepReport, Sys.committedVal, Sys.ev, Sys.evBefore,
        ehist, hmsgs] at h9 ⊢; exact h9
    · simp only [Inv.prepReplyHighest, Sys.prepReport, Sys.ev, Sys.evBefore, ehist, hmsgs] at h10 ⊢
      exact h10
    · -- lbInv
      intro r hr y w2 lb h2' hlb
      obtain ⟨w1, h1', c, hlb2, -, e⟩ := hbwd r y w2 h2'
      rw [hlb2] at hlb
      obtain ⟨a1, a2, a3, a4, a5, ⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩, a8, a9⟩ :=
        h11 r hr y w1 lb h1' hlb
      have hdm : ∀ a r' m, S.deliveredMsg a r' m → S'.deliveredMsg a r' m := by
        rintro a r' m ⟨k, hk1, hk2⟩; exact ⟨k, by rw [esent]; exact hk1, by rw [edel]; exact hk2⟩
      refine ⟨(hev _ _).mpr a1, a2, a3, fun b v hv => a4 b v (hv.imp (hev _ _).mp (hev _ _).mp),
        fun h1'' h2'' => ?_, ⟨Q, q1, q2, fun a m h => ?_⟩, ⟨Q', q1', q2', fun a h => ?_⟩, ?_, ?_⟩
      · obtain ⟨d1, d2, v, d3, d4⟩ := a5 h1'' h2''; exact ⟨d1, d2, v, (hev _ _).mpr d3, d4⟩
      · obtain ⟨b1, b2, b3, b4⟩ := q3 a m h; exact ⟨b1, b2, hdm _ _ _ b3, b4⟩
      · obtain ⟨b1, b2, m, b3, b4⟩ := q3' a h; exact ⟨b1, b2, m, hdm _ _ _ b3, b4⟩
      · intro c1 c2 c3 c4
        rcases e with rfl | ⟨-, -, -, rfl⟩
        · obtain ⟨d1, d2⟩ := a8 c1 c2 c3 c4; exact ⟨(hev _ _).mpr d1, (hev _ _).mpr d2⟩
        · exact absurd (show stEXECUTED = stACCEPTED from c2) (by decide)
      · intro hp
        obtain ⟨c1, c2⟩ := a9 hp
        refine ⟨c1, fun e' he => ?_⟩
        obtain ⟨d1, d2, d3⟩ := c2 e' he
        refine ⟨d1, d2, ?_⟩
        rcases d3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact Or.inl ⟨e1, hdm _ _ _ e2⟩
        · exact Or.inr ⟨e1, (hev _ _).mpr e2⟩
    · -- agreement
      refine ⟨fun y v v' a b => h12.1 y v v' ((hcvS _ _).mp a) ((hcvS _ _).mp b),
        fun r hr y w2 h2' hs => ?_⟩
      obtain ⟨w1, h1', c, -⟩ := hbwd r y w2 h2'
      have hs1 : isCommitted w1.status := by
        rcases c.2.2.2.1 with e | ⟨e0, -⟩
        · rw [e] at hs; exact hs
        · exact Or.inl e0
      obtain ⟨d1, d2⟩ := h12.2 r hr y w1 h1' hs1
      exact ⟨by rw [c.1]; exact d1, by rw [c.instVal]; exact (hcvS _ _).mpr d2⟩
    · simp only [Inv.decidedChosen, Sys.committedVal, Sys.slowChosen, Sys.fastReplies, Sys.ev,
        ehist, hmsgs] at h13 ⊢; exact h13
    · intro a b va vb hab ha hb hi'
      exact h15 a b va vb hab ((hcvS _ _).mp ha) ((hcvS _ _).mp hb) hi'
    · intro y v hv hn
      obtain ⟨W, a1, a2, a3⟩ := h16 y v ((hcvS _ _).mp hv) hn
      exact ⟨W, a1, a2, fun r hr => by
        obtain ⟨b1, d, b2, b3⟩ := a3 r hr; exact ⟨b1, d, (hev _ _).mpr b2, b3⟩⟩
    · simp only [Inv.attrsCover, Sys.evBefore, ehist] at h17 ⊢; exact h17
    · -- execClosed
      intro r hr
      obtain ⟨e1, e2, e3⟩ := h18 r hr
      by_cases hri : r = i
      · subst hri
        rw [elog, ecur, upd_same, upd_same]
        refine ⟨List.nodup_append.mpr ⟨e1, by simp, fun a ha b hb e => ?_⟩, fun y => ?_,
          fun y w2 h2' hs => ?_⟩
        · simp only [List.mem_singleton] at hb; subst hb; subst e; exact hxl ha
        · rw [hexe', List.mem_append, List.mem_singleton, e2]
          constructor
          · rintro (h | rfl)
            · exact Or.inl h
            · exact Or.inr ⟨rfl, rfl⟩
          · rintro (h | ⟨-, rfl⟩)
            · exact Or.inl h
            · exact Or.inr rfl
        · obtain ⟨w1, h1', c, -, -, e⟩ := hbwd r y w2 h2'
          have hs1 : isCommitted w1.status := by
            rcases c.2.2.2.1 with e' | ⟨e0, -⟩
            · rw [e'] at hs; exact Or.inr hs
            · exact Or.inl e0
          refine ⟨(hcvS _ _).mpr (by rw [c.instVal]; exact (h12.2 r hr y w1 h1' hs1).2), fun z hz => ?_⟩
          · rw [hdep] at hz
            rw [hexe']
            rcases e with rfl | ⟨-, rfl, rfl, -⟩
            · -- an old executed instance
              rcases (e3 y w2 h1' hs).2 z hz with h | h
              · exact Or.inl (Or.inl h)
              · rw [hcur] at h
                rcases List.mem_cons.mp h with h | h
                · exact Or.inl (Or.inr ⟨rfl, h⟩)
                · exact Or.inr h
            · -- `x`: its edges stay in the component
              rcases hclosed y ((mem_sccSort _ _ _).mp (by rw [hsort, hcur]; simp)) z hz
                with h | h
              · exact Or.inl (Or.inl h)
              · have : z ∈ done ++ S.execCur r := by
                  rw [← hsort]; exact List.mem_mergeSort.mpr h
                rw [hcur] at this
                rcases List.mem_append.mp this with h | h
                · exact Or.inl (Or.inl (hdone z h))
                · rcases List.mem_cons.mp h with h | h
                  · exact Or.inl (Or.inr ⟨rfl, h⟩)
                  · exact Or.inr h
      · rw [elog, ecur, upd_other _ _ _ _ hri, upd_other _ _ _ _ hri]
        refine ⟨e1, fun y => ?_, fun y w2 h2' hs => ?_⟩
        · rw [hexe', e2]; simp [hri]
        · obtain ⟨w1, h1', c, -, -, e⟩ := hbwd r y w2 h2'
          rcases e with rfl | ⟨h, -⟩
          · obtain ⟨d1, d2⟩ := e3 y w2 h1' hs
            refine ⟨(hcvS _ _).mpr d1, fun z hz => ?_⟩
            rw [hdep] at hz; rw [hexe']
            rcases d2 z hz with h | h
            · exact Or.inl (Or.inl h)
            · exact Or.inr h
          · exact absurd h hri
    · -- execCursor
      intro r hr
      by_cases hri : r = i
      · subst hri
        rw [ecur, eidx, upd_same, upd_same]
        refine ⟨fun _ => rfl, fun hne => ?_⟩
        refine ⟨done ++ [x], C, ?_, hCn, fun y hy => ?_, fun y hy => ?_, fun y hy z hz => ?_,
          fun a ha b hb => ?_, fun y w2 _ _ => Nat.zero_le _⟩
        · rw [show sccSort (S'.rep r) C = sccSort (S.rep r) C by simp only [sccSort, hle], hsort,
            hcur]; simp
        · rw [hexe']
          rcases List.mem_append.mp hy with h | h
          · exact Or.inl (hdone y h)
          · simp only [List.mem_singleton] at h; exact Or.inr ⟨rfl, h⟩
        · obtain ⟨w1, h1', hs1, hc1⟩ := hready y (by rw [hcur]; exact List.mem_cons_of_mem _ hy)
          have hyx : y ≠ x := by
            intro e; subst e
            have hn : (sccSort (S.rep r) C).Nodup := (List.mergeSort_perm C _).nodup_iff.mpr hCn
            rw [hsort, hcur] at hn
            exact (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1 hy
          refine ⟨w1, by rw [hrec, if_neg (fun h => hyx h.2)]; exact h1', hs1, hc1⟩
        · rw [hdep] at hz; rw [hexe']
          rcases hclosed y hy z hz with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
        · rcases hscc a ha b hb with h | h
          · exact Or.inl h
          · exact Or.inr (tg_mono' (fun c d h => ⟨(hdep r c d).mpr h.1, h.2⟩) h)
      · have := h19 r hr
        rw [ecur, eidx, upd_other _ _ _ _ hri, upd_other _ _ _ _ hri]
        refine ⟨this.1, fun hne => ?_⟩
        obtain ⟨dn, C', a1, a2, a3, a4, a5, a6, a7⟩ := this.2 hne
        refine ⟨dn, C', by rw [show sccSort (S'.rep r) C' = sccSort (S.rep r) C' by
          simp only [sccSort, hle]]; exact a1, a2, fun y hy => (hexe' r y).mpr (Or.inl (a3 y hy)),
          fun y hy => ?_, fun y hy z hz => ?_, fun a ha b hb => ?_, fun y w2 hy hw2 => ?_⟩
        · obtain ⟨w1, h1', hs1, hc1⟩ := a4 y hy
          refine ⟨w1, by rw [hrec, if_neg (fun h => hri h.1)]; exact h1', hs1, hc1⟩
        · rw [hdep] at hz; rw [hexe']
          rcases a5 y hy z hz with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
        · rcases a6 a ha b hb with h | h
          · exact Or.inl h
          · exact Or.inr (tg_mono' (fun c d h => ⟨(hdep r c d).mpr h.1, h.2⟩) h)
        · rw [hrec, if_neg (fun h => hri h.1)] at hw2; exact a7 y w2 hy hw2
    · -- execOrder: the log is a prefix of the execution sequence
      intro r hr p q a b hpq ha hb ht
      rw [hdE] at ht ⊢; rw [hsO]
      have hpre : S'.execLog r <+: S.eseq r := by rw [← hes]; exact List.prefix_append _ _
      obtain ⟨t, ht'⟩ := hpre
      have ha' : (S.eseq r)[p]? = some a := by
        rw [← ht', List.getElem?_append_left (List.getElem?_eq_some_iff.mp ha).1]; exact ha
      have hb' : (S.eseq r)[q]? = some b := by
        rw [← ht', List.getElem?_append_left (List.getElem?_eq_some_iff.mp hb).1]; exact hb
      exact ord_before ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
        h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ hX hr (before_of_idx hpq ha' hb') ht
    · -- execPrefix
      obtain ⟨p1, p2, p3⟩ := h21
      refine ⟨fun r hr k => by rw [hlx, egex]; exact p1 r hr k,
        fun r hr k => by rw [hlx, (hfld r).2.2.2.2.1]; exact p2 r hr k,
        fun r hr k pre e post h => by rw [hlx] at h; rw [egex]; exact p3 r hr k pre e post h⟩
    · -- slots
      refine ⟨fun y v hv => by rw [eown]; exact h22.1 y v ((hcvS _ _).mp hv), fun y ps h => ?_⟩
      rw [eown] at h; rw [eops]; exact h22.2 y ps h
    · -- clientOps
      obtain ⟨c1, c2, c3, c4, c5⟩ := h23
      have hso' : S'.slotOp = S.slotOp := by funext s; simp only [Sys.slotOp, eown]
      refine ⟨by rw [eops]; exact c1, by rw [egex, hso']; exact c2, by rw [egex]; exact c3,
        fun k e he => ?_, by rw [efir, egex, hso']; exact c5⟩
      rw [egex] at he; rw [hso']
      obtain ⟨d1, d2, d3, d4, v, hv, hvc⟩ := c4 k e he
      exact ⟨d1, d2, by rw [egex]; exact d3, d4, v, (hcvS _ _).mpr hv, hvc⟩
    · simp only [Inv.commitMsgs, Sys.ev, ehist, hmsgs] at h24 ⊢; exact h24
    · simp only [Inv.pendingKind, epend] at h25 ⊢; exact h25
  -- `InvExec`
  have hdead : ∀ y, S'.propDead y ↔ S.propDead y := by
    intro y
    simp only [Sys.propDead, hcvS]
    constructor
    · rintro ⟨h1', h2'⟩
      refine ⟨h1', fun w1 lb h3 h4 => ?_⟩
      obtain ⟨w2, h5, -, hlb, -⟩ := hfwd _ y w1 h3
      exact h2' w2 lb h5 (by rw [hlb]; exact h4)
    · rintro ⟨h1', h2'⟩
      refine ⟨h1', fun w2 lb h3 h4 => ?_⟩
      obtain ⟨w1, h5, -, hlb, -⟩ := hbwd _ y w2 h3
      exact h2' w1 lb h5 (by rw [← hlb]; exact h4)
  have hso' : S'.slotOp = S.slotOp := by funext s; simp only [Sys.slotOp, eown]
  have hcls : ∀ r, (S'.rep r).lastScan = (S.rep r).lastScan ∧
      (S'.rep r).lastPut = (S.rep r).lastPut := by
    intro r; rw [erep]
    by_cases h : r = i
    · subst h; simp [hexd, RState.setInst]
    · simp [upd_other _ _ _ _ h]
  have hX' : InvExec S' := by
    refine ⟨fun r hr a b => ?_, fun r hr l1 l2 a b => ?_, fun k e => ?_,
      fun s s' p p' => ?_, fun j p s p' => ?_, fun j1 j2 n m p p' => ?_, fun j p => ?_⟩
    · rw [hes, hdE]; exact hX.reach r hr a b
    · rw [hes, hdE, hsO]; exact hX.ord r hr l1 l2 a b
    · rw [egex]; intro he
      obtain ⟨r, hr, h⟩ := hX.gloc k e he
      exact ⟨r, hr, by rw [hlx]; exact h⟩
    · rw [hso', hdead, hdead]; exact hX.tokSlot s s' p p'
    · rw [echan, hso', hdead]; exact hX.tokChan j p s p'
    · rw [echan]; exact hX.chanOnce j1 j2 n m p p'
    · rw [echan, eops]; exact hX.chanOps j p
  -- `InvAux`
  refine ⟨h0', aux_congr_ex S S' hS.2 h1.2.2.2.2.2.2.1 ⟨fun r y w2 h => ?_, fun r y w1 h => ?_,
    fun r => (hfld r).2.1, fun r hr => by rw [(hfld r).2.2.2.2.2]; exact hS.2.peerOk r hr,
    fun r e _ => hev r e, fun fr to => by rw [hmsgs]; exact List.Sublist.refl _,
    fun fr to n m h => ⟨n, by rw [← hmsgs]; exact h, Or.inl rfl⟩, fun d h => by rw [edel]; exact h,
    fun r to m h => (hev _ _).mp h, fun r e r' e' _ h => by simpa [Sys.evBefore, ehist] using h,
    fun r => (hfld r).2.2.1, eown, fun r e h => (hev r e).mpr h, hcls⟩ ?_ hX'
    (execLo_of_eq hS.2.execLo (fun r _ => (hfld r).2.2.2.1))⟩
  · obtain ⟨w1, h1', c, -⟩ := hbwd r y w2 h; exact ⟨w1, h1', c⟩
  · obtain ⟨w2, h2', c, -⟩ := hfwd r y w1 h; exact ⟨w2, h2', c⟩
  · refine PMProof.pm_frame hS.2.pm (fun r e h => (hev r e).mpr h) (fun r e h => Or.inl ((hev r e).mp h))
      (fun fr to m h => by rw [hmsgs] at h; exact h) (fun fr to m h => by rw [esent]; exact h)
      (fun y u h => by simpa only [Sys.committedVal, Sys.ev, ehist, hmsgs] using h)
      (fun r y w1 h => ?_) (fun r y w2 lb2 h hl => ?_) ?_
      (fun r b h => Or.inl (by rw [epend] at h; exact h))
    · obtain ⟨w2, h2', c, -⟩ := hfwd r y w1 h; exact ⟨w2, h2', by rw [c.2.1]; exact Int.le_refl _⟩
    · obtain ⟨w1, h1', -, hl', -⟩ := hbwd r y w2 h
      exact ⟨w1, lb2, h1', by rw [← hl']; exact hl, PMProof.LbPM.refl _⟩
    · refine PMProof.ps_frame hS.2.pm (fun y w2 lb2 h hl => ?_) (fun r b h _ => by rw [epend] at h; exact h)
        (fun y a h => by rw [esent, eob] at h; exact h)
      obtain ⟨w1, h1', -, hl', -⟩ := hbwd _ y w2 h
      exact ⟨w1, lb2, h1', by rw [← hl']; exact hl, rfl, rfl⟩

end

end ExecOrd

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
