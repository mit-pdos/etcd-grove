/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureT/EpSteps.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A2 (totality): the EPaxos handlers' steps (`Prepare`, `PreAccept`, `Accept`, `Commit`).
-/
module

public import Dsverify.Proof.gryff.PureT.EpBase

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.tot

open model kahn

theorem stOk_of {x : w8} (h : x = St.NONE ∨ x = St.PREACCEPTED ∨ x = St.PREACCEPTED_EQ ∨
    x = St.ACCEPTED ∨ x = St.COMMITTED ∨ x = St.EXECUTED) : stOk x := h

theorem sendPeer_eq (s : RState) (r' : Fin 3) (m : Msg) :
    sendPeer s (rid32 r') m = if rid32 r' = s.id then none else some (.send r' m) := by
  simp [sendPeer, sendTo_rid]

theorem rid32_eq_iff (a b : Fin 3) : rid32 a = rid32 b ↔ a = b :=
  ⟨rid32_inj, fun h => h ▸ rfl⟩

theorem PropC.updNe {st : Fin 3 → RState} {r L : Fin 3} {s' : RState} {q i : w32} (hL : L ≠ r)
    (h : PropC st L q i) : PropC (upd st r s') L q i := by
  unfold PropC; rw [upd_ne _ _ hL]; exact h

theorem own_none {st : Fin 3 → RState} {r : Fin 3} {s : RState} (h : Good st r s) {q i : w32}
    (hb : InstB (Pf st) q i) (hc : s.inst q i = none) (hq : q = rid32 r) : False := by
  subst hq; have := own_some h hb; rw [hc] at this; cases this

/-- A copy changed in fields no invariant mentions. -/
structure SameC (c c' : Copy) : Prop where
  cmds : c'.cmds = c.cmds
  status : c'.status = c.status
  leader : c'.leader = c.leader
  slot : c'.slot = c.slot
  lb : c'.lb = c.lb

theorem SameC.copyOK {q i : w32} {c c' : Copy} (h : SameC c c') (hc : CopyOK q i c) :
    CopyOK q i c' := by
  obtain ⟨a, b, d, e, f, g⟩ := hc
  exact ⟨h.cmds ▸ a, by rw [h.status, h.cmds]; exact b, h.leader ▸ d, h.slot ▸ e, h.status ▸ f,
    by rw [h.lb]; exact g⟩

theorem SameC.ownOK {c c' : Copy} (h : SameC c c') (hc : OwnOK c) : OwnOK c' := by
  obtain ⟨a, b, d⟩ := hc
  exact ⟨h.status ▸ a, by rw [h.lb, h.status]; exact b, by rw [h.lb]; exact d⟩

theorem SameC.mono {old : Option Copy} {c c' : Copy} (h : SameC c c') (ho : old = some c) :
    CopyMono old c' := by
  intro c0 h0; rw [ho] at h0; cases h0
  exact ⟨by rw [h.lb, h.status]; exact id, fun x => ⟨h.status ▸ x, h.cmds⟩⟩

/-- A copy at `r` replaced by one with the same shape. -/
theorem Good.setSame {st : Fin 3 → RState} {r : Fin 3} {s : RState} (h : Good st r s) {q i : w32}
    {c c' : Copy} (hc : s.inst q i = some c) (hs : SameC c c') : Good st r (s.setInst q i c') := by
  obtain ⟨hb, hcok⟩ := h.copy hc
  exact h.setInst hb (hs.copyOK hcok)
    (fun hq => hs.ownOK (h.si.ownOK i c (hq ▸ hc))) (hs.mono hc)

theorem stepPrepare_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (m : PrepareM)
    (hm : MInv (Pf st) st r (.prepare m)) : Ok (stepPrepare (st r) m) (Post st r) := by
  simp only [MInv, FromL] at hm
  obtain ⟨⟨L, hL, hlid, hPC⟩, hb⟩ := hm
  have hid := (hI r).id
  have hLr : L ≠ r := hL
  cases hc : (st r).inst m.replica m.inst with
  | none =>
    tsimp [stepPrepare, hb.inBox hI, hc, hlid, sendPeer_eq, hid, hLr, setInst_id, rid32_eq_iff]
    apply Ok.ret
    refine ((Good.refl hI).setInst hb ⟨rfl, by simp only; decide, rfl, rfl, stOk_of (by simp only; decide),
      by simp⟩
      (fun hq => (own_none (Good.refl hI) hb hc hq).elim) (by rw [hc]; simp [CopyMono])).post ?_
    simp only [List.mem_singleton, forall_eq, OutOk, MInv]
    exact ⟨hb, hPC.updNe hLr, rfl, by decide⟩
  | some c =>
    obtain ⟨-, hcok⟩ := (hI r).inst _ _ c hc
    tsimp [stepPrepare, hb.inBox hI, hc, hlid, sendPeer_eq, hid, hLr, setInst_id, rid32_eq_iff]
    have hout : ∀ c' : Copy, SameC c c' → ∀ (ok : w8),
        Post st r ((st r).setInst m.replica m.inst c', [Out.send L (Msg.prepareReply
          { acceptorId := rid32 r, replica := m.replica, inst := m.inst, ok, ballot := c'.ballot,
            vbal := c'.vbal, status := c'.status, cmds := c'.cmds, seq := c'.seq, deps := c'.deps,
            base := c'.base })]) := by
      intro c' hs ok
      refine ((Good.refl hI).setSame hc hs).post ?_
      have hk := hs.copyOK hcok
      simp only [List.mem_singleton, forall_eq, OutOk, MInv]
      exact ⟨hb, hPC.updNe hLr, hk.1, hk.2.1⟩
    split <;> (refine Ok.ret (hout _ ?_ _); exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

end Perennial.gryff.pure.tot

namespace Perennial.gryff.pure.tot
open model kahn

theorem OkO.of_eq {α : Type} {x : Option α} {P : α → Prop} (h : OkO x P) {a : α} (hx : x = Option.some a) :
    P a := by
  obtain ⟨b, hb, hp⟩ := h; rw [hx] at hb; cases hb; exact hp

theorem OkO.not_none {α : Type} {x : Option α} {P : α → Prop} (h : OkO x P)
    (hx : ∀ a, x = Option.some a → False) : False := by
  obtain ⟨b, hb, _⟩ := h; exact hx b hb

/-- A copy committed in place (`handleCommit`, the proposer's commit). -/
theorem Good.commitCopy {st : Fin 3 → RState} {r : Fin 3} {S : RState} (h : Good st r S)
    {q i : w32} {c : Copy} (hc : S.inst q i = some c) (hne : c.status ≠ St.EXECUTED)
    {cmds : List Cmd} (hcmds : cmdsOk cmds = true) {L : Option LB} (hL : L = c.lb ∨ L = none)
    {c'' : Copy} (h1 : c''.cmds = cmds) (h2 : c''.status = St.COMMITTED) (h3 : c''.leader = c.leader)
    (h4 : c''.slot = c.slot) (h5 : c''.lb = L) : Good st r (S.setInst q i c'') := by
  obtain ⟨hb, hcok⟩ := h.copy hc
  obtain ⟨-, -, hl, hs, -, hlb⟩ := hcok
  refine h.setInst hb ⟨h1 ▸ hcmds, by rw [h2]; intro h; exfalso; revert h; decide, h3 ▸ hl, h4 ▸ hs,
    stOk_of (by rw [h2]; decide), ?_⟩ ?_ ?_
  · intro lb hlb'; rw [h5] at hlb'
    rcases hL with rfl | rfl
    · exact hlb lb hlb'
    · cases hlb'
  · intro hq
    obtain ⟨o1, -, o3⟩ := h.si.ownOK i c (hq ▸ hc)
    refine ⟨by rw [h2]; decide, fun _ => Or.inl h2, ?_⟩
    intro lb hlb'; rw [h5] at hlb'
    rcases hL with rfl | rfl
    · exact o3 lb hlb'
    · cases hlb'
  · intro c0 h0; rw [hc] at h0; cases h0
    exact ⟨fun _ => Or.inr (Or.inl h2), fun hx => absurd hx hne⟩

theorem stepCommit_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (m : ECommitM)
    (hm : MInv (Pf st) st r (.commit m)) : Ok (stepCommit (st r) m) (Post st r) := by
  simp only [MInv] at hm
  obtain ⟨hb, hcmds⟩ := hm
  have hid := (hI r).id
  have hG0 := Good.raiseCrt hI (Good.refl (r := r) hI) hb
  cases hc : (st r).inst m.replica m.inst with
  | none =>
    tsimp [stepCommit, hb.inBox hI, hc, hcmds, setCrt_inst]
    obtain ⟨q', hq', -⟩ := id hb
    by_cases hcnd : sge m.inst ((st r).crt m.replica) = true
    all_goals simp only [hcnd, if_true, if_false, Bool.false_eq_true] at hG0 ⊢
    all_goals
      simp only [hq'] at hG0 hc ⊢
      have hG1 := hG0.setInst (q := rid32 q') (i := m.inst)
        (c := { cmds := m.cmds, ballot := 0, status := St.COMMITTED, seq := m.seq, deps := m.deps,
                base := m.base, lb := none, slot := m.inst, leader := rid32 q', vbal := 0 })
        (by rw [← hq']; exact hb) ⟨hcmds, fun h => by exfalso; simp only at h; revert h; decide, rfl, rfl,
          stOk_of (by simp only; decide), by simp⟩
        (fun he => (own_none (Good.refl (r := r) hI) (by rw [← hq']; exact hb) hc he).elim)
        (by (try simp only [setCrt_inst]); rw [hc]; simp [CopyMono])
      have hG2 := hG1.updConf m.cmds (q' := q') (i := m.inst) (by simp) m.seq
      obtain ⟨s', hs', hG3⟩ := hG2.updCommitted hI q'
      rw [hs']
      exact Ok.ret (hG3.post (by simp))
  | some c =>
    tsimp [stepCommit, hb.inBox hI, hc, hcmds, setCrt_inst]
    obtain ⟨q', hq', -⟩ := id hb
    by_cases hcnd : sge m.inst ((st r).crt m.replica) = true
    all_goals simp only [hcnd, if_true, if_false, Bool.false_eq_true] at hG0 ⊢
    all_goals simp only [hq'] at hG0 hc ⊢
    all_goals
      have hcok := (hG0.copy hc).2
      split
      · exact Ok.ret (hG0.post (by simp))
      · next hne =>
        split
        · next lb hlb =>
          split
          · split
            · next s' heq =>
              refine Ok.ret ((OkO.of_eq (Good.updCommitted hI ?_ q') heq).post (by simp))
              exact (hG0.propAppend lb.clientProposals (hcok.2.2.2.2.2 lb hlb).1).commitCopy
                hc hne hcmds (Or.inr rfl) rfl rfl rfl rfl rfl
            · next hx =>
              refine (OkO.not_none (Good.updCommitted (r := r) hI ?_ q') hx).elim
              exact (hG0.propAppend lb.clientProposals (hcok.2.2.2.2.2 lb hlb).1).commitCopy
                hc hne hcmds (Or.inr rfl) rfl rfl rfl rfl rfl
          · split
            · next s' heq =>
              refine Ok.ret ((OkO.of_eq (Good.updCommitted hI ?_ q') heq).post (by simp))
              exact hG0.commitCopy hc hne hcmds (Or.inl rfl) rfl rfl rfl rfl rfl
            · next hx =>
              refine (OkO.not_none (Good.updCommitted (r := r) hI ?_ q') hx).elim
              exact hG0.commitCopy hc hne hcmds (Or.inl rfl) rfl rfl rfl rfl rfl
        · split
          · next s' heq =>
            refine Ok.ret ((OkO.of_eq (Good.updCommitted hI ?_ q') heq).post (by simp))
            exact hG0.commitCopy hc hne hcmds (Or.inl rfl) rfl rfl rfl rfl rfl
          · next hx =>
            refine (OkO.not_none (Good.updCommitted (r := r) hI ?_ q') hx).elim
            exact hG0.commitCopy hc hne hcmds (Or.inl rfl) rfl rfl rfl rfl rfl

/-- A copy replaced in an uncommitted state by one with its bookkeeping. -/
theorem Good.replaceLb {st : Fin 3 → RState} {r : Fin 3} {S : RState} (h : Good st r S)
    {q i : w32} {c : Copy} (hc : S.inst q i = some c) (hnc : ¬ committedSt c.status) {c' : Copy}
    (hcmds : cmdsOk c'.cmds = true)
    (hpre : (c'.status = St.PREACCEPTED ∨ c'.status = St.PREACCEPTED_EQ) → c'.cmds ≠ [])
    (hl : c'.leader = c.leader) (hs : c'.slot = c.slot) (hst : stOk c'.status)
    (hnn : c'.status ≠ St.NONE) (hlb : c'.lb = c.lb) : Good st r (S.setInst q i c') := by
  obtain ⟨hb, hcok⟩ := h.copy hc
  obtain ⟨-, -, hl0, hs0, -, hlb0⟩ := hcok
  refine h.setInst hb ⟨hcmds, hpre, hl ▸ hl0, hs ▸ hs0, hst, by rw [hlb]; exact hlb0⟩ ?_ ?_
  · intro hq
    obtain ⟨-, o2, o3⟩ := h.si.ownOK i c (hq ▸ hc)
    refine ⟨hnn, fun hn => absurd (o2 (hlb ▸ hn)) hnc, by rw [hlb]; exact o3⟩
  · intro c0 h0; rw [hc] at h0; cases h0
    refine ⟨fun hx => ?_, fun hx => absurd (Or.inr hx) hnc⟩
    rcases hx with hx | hx
    · exact Or.inl (hlb ▸ hx)
    · exact absurd hx hnc

theorem Good.newCopy {st : Fin 3 → RState} {r : Fin 3} {S : RState} (h : Good st r S)
    {q i : w32} {c : Copy} (hb : InstB (Pf st) q i) (hc : S.inst q i = none) (hcok : CopyOK q i c) :
    Good st r (S.setInst q i c) :=
  h.setInst hb hcok (fun hq => (own_none h hb hc hq).elim) (by rw [hc]; intro c0 h0; cases h0)

theorem FromL.updNe {st : Fin 3 → RState} {r : Fin 3} {l q i : w32} (h : FromL st r l q i)
    (s' : RState) : ∃ L, L ≠ r ∧ l = rid32 L ∧ PropC (upd st r s') L q i := by
  obtain ⟨L, h1, h2, h3⟩ := h; exact ⟨L, h1, h2, h3.updNe h1⟩

theorem stepAccept_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (m : EAcceptM)
    (hm : MInv (Pf st) st r (.accept m)) : Ok (stepAccept (st r) m) (Post st r) := by
  simp only [MInv] at hm
  obtain ⟨hF, hb, hcmds⟩ := hm
  obtain ⟨L, hL, hlid, hPC⟩ := id hF
  have hid := (hI r).id
  have hLr : L ≠ r := hL
  have hG0 := Good.raiseCrt hI (Good.refl (r := r) hI) hb
  cases hc : (st r).inst m.replica m.inst with
  | none =>
    tsimp [stepAccept, hb.inBox hI, hc, hcmds, setCrt_inst, hlid, sendPeer_eq, hid, hLr, setInst_id,
      rid32_eq_iff, setCrt_id]
    by_cases hcnd : sge m.inst ((st r).crt m.replica) = true
    all_goals simp only [hcnd, if_true, if_false, Bool.false_eq_true] at hG0 ⊢
    all_goals
      apply Ok.ret
      refine (hG0.newCopy hb (by first | exact hc | simpa using hc) ⟨hcmds,
        fun h => by exfalso; simp only at h; revert h; decide, rfl, rfl,
        stOk_of (by simp only; decide), by simp⟩).post ?_
      simp only [List.mem_singleton, forall_eq, OutOk, MInv]
      exact ⟨hb, hPC.updNe hLr⟩
  | some c =>
    tsimp [stepAccept, hb.inBox hI, hc, hcmds, setCrt_inst, hlid, sendPeer_eq, hid, hLr, setInst_id,
      rid32_eq_iff, setCrt_id]
    have hout : ∀ (S : RState) (ok : w8) (b : w32), Good st r S →
        Post st r (S, [Out.send L (Msg.acceptReply (AcceptReplyM.mk m.replica m.inst ok b))]) := by
      intro S ok b hS
      refine hS.post ?_
      simp only [List.mem_singleton, forall_eq, OutOk, MInv]
      exact ⟨hb, hPC.updNe hLr⟩
    split
    · exact Ok.ret ((Good.refl hI).post (by simp))
    · next hnc =>
      have hcok := (hI r).inst _ _ c hc
      by_cases hcnd : sge m.inst ((st r).crt m.replica) = true
      all_goals simp only [hcnd, if_true, if_false, Bool.false_eq_true] at hG0 ⊢
      all_goals
        split
        · exact Ok.ret (hout _ _ _ hG0)
        · refine Ok.ret (hout _ _ _ (hG0.replaceLb (by first | exact hc | simpa using hc) hnc hcmds
            (fun h => by exfalso; simp only at h; revert h; decide) rfl rfl
            (stOk_of (by simp only; decide)) (by simp only; decide) rfl))

theorem Good.updConf' {st : Fin 3 → RState} {r : Fin 3} {s : RState} (h : Good st r s)
    (cmds : List Cmd) {q : w32} {q' : Fin 3} (hq : q = rid32 q') {i : w32}
    (hi : (s.inst q i).isSome) (seq : w32) : Good st r (updateConflicts s cmds q i seq) := by
  subst hq; exact h.updConf cmds hi seq

theorem stOk_pre (b : Bool) : stOk (if b = true then St.PREACCEPTED else St.PREACCEPTED_EQ) := by
  cases b
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inl rfl)

theorem pre_ne_none (b : Bool) : (if b = true then St.PREACCEPTED else St.PREACCEPTED_EQ) ≠ St.NONE := by
  cases b <;> decide

/-- The two replies to a PreAccept from `L`. -/
theorem preAcc_out {st : Fin 3 → RState} {r L : Fin 3} {q i : w32}
    (hb : InstB (Pf st) q i) (hPC : PropC st L q i) (hLr : L ≠ r) (S : RState) :
    (∀ (x : PreAcceptReplyM), x.replica = q → x.inst = i →
      OutOk (Pf st) (upd st r S) (Out.send L (.preAcceptReply x))) ∧
    (q = rid32 L → OutOk (Pf st) (upd st r S) (Out.send L (.preAcceptOK ⟨i⟩))) := by
  refine ⟨fun x h1 h2 => ?_, fun hq => ?_⟩
  · simp only [OutOk, MInv, h1, h2]; exact ⟨hb, hPC.updNe hLr⟩
  · simp only [OutOk, MInv]; subst hq; exact ⟨hb, hPC.updNe hLr⟩

theorem stepPreAccept_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (m : PreAcceptM)
    (hm : MInv (Pf st) st r (.preAccept m)) : Ok (stepPreAccept (st r) m) (Post st r) := by
  simp only [MInv] at hm
  obtain ⟨hF, hb, hcmds, hne⟩ := hm
  obtain ⟨L, hL, hlid, hPC⟩ := id hF
  obtain ⟨c0, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
  have hhd : m.cmds.head? = some c0 := by rw [hcs]; rfl
  have hid := (hI r).id
  have hLr : L ≠ r := hL
  have hG0 := Good.raiseCrt hI (Good.refl (r := r) hI) hb
  cases hc : (st r).inst m.replica m.inst with
  | none =>
    tsimp [stepPreAccept, hb.inBox hI, hc, hcmds, setCrt_inst, hlid, sendPeer_eq, hid, hLr, setInst_id,
      rid32_eq_iff, setCrt_id, hhd, updConf_id]
    obtain ⟨q', hq', -⟩ := id hb
    have ho := preAcc_out hb hPC hLr
    by_cases hcnd : sge m.inst ((st r).crt m.replica) = true
    all_goals simp only [hcnd, if_true, if_false, Bool.false_eq_true] at hG0 ⊢
    all_goals
      split
      · split
        · apply Ok.ret
          refine (Good.updConf' (hG0.newCopy hb (by first | exact hc | simpa using hc) ⟨hcmds, fun _ => hne, rfl, rfl,
            stOk_of (by simp only; decide), by simp⟩) m.cmds hq' (by simp) m.seq).post ?_
          simp only [List.mem_singleton, forall_eq]; exact (ho _).1 _ rfl rfl
        · split
          · apply Ok.ret
            refine (Good.updConf' (hG0.newCopy hb (by first | exact hc | simpa using hc) ⟨hcmds, fun _ => hne, rfl, rfl,
              stOk_pre _, by simp⟩) m.cmds hq' (by simp) m.seq).post ?_
            simp only [List.mem_singleton, forall_eq]; exact (ho _).1 _ rfl rfl
          · next hcond =>
            have hrl : m.replica = rid32 L :=
              Classical.byContradiction fun hx => hcond (by simp [hx])
            apply Ok.ret
            refine (Good.updConf' (hG0.newCopy hb (by first | exact hc | simpa using hc) ⟨hcmds, fun _ => hne, rfl, rfl,
              stOk_pre _, by simp⟩) m.cmds hq' (by simp) m.seq).post ?_
            simp only [List.mem_singleton, forall_eq]; exact (ho _).2 hrl
      · next hx =>
        exact (OkO.not_none (updAttr_ok _ (confOk hI hG0.si) _ _ _ _)
          (fun a ha => hx a.1 a.2.1 a.2.2 ha)).elim
  | some c =>
    tsimp [stepPreAccept, hb.inBox hI, hc, hcmds, setCrt_inst, hlid, sendPeer_eq, hid, hLr, setInst_id,
      rid32_eq_iff, setCrt_id, hhd, updConf_id]
    obtain ⟨q', hq', -⟩ := id hb
    have ho := preAcc_out hb hPC hLr
    split
    · exact Ok.ret ((Good.refl hI).post (by simp))
    · next hnc0 =>
      have hnc : ¬ committedSt c.status := fun h => hnc0 (by
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h))
      by_cases hcnd : sge m.inst ((st r).crt m.replica) = true
      all_goals simp only [hcnd, if_true, if_false, Bool.false_eq_true] at hG0 ⊢
      all_goals
        have hnack : ∀ x : PreAcceptReplyM, x.replica = m.replica → x.inst = m.inst →
            Ok (pure (_, [Out.send L (.preAcceptReply x)])) (Post st r) := fun x h1 h2 =>
          Ok.ret (hG0.post (by simp only [List.mem_singleton, forall_eq]; exact (ho _).1 x h1 h2))
        split
        · split
          · split
            · exact hnack _ rfl rfl
            · apply Ok.ret
              refine Good.post (Good.updConf' ?_ m.cmds hq' (by simp) m.seq) ?_
              · refine hG0.replaceLb (by first | exact hc | simpa using hc) hnc ?_ ?_ ?_ ?_ ?_ ?_ ?_
                all_goals first
                  | exact hcmds
                  | exact fun _ => hne
                  | rfl
                  | exact stOk_of (by simp only; decide)
                  | (simp only; decide)
              simp only [List.mem_singleton, forall_eq]; exact (ho _).1 _ rfl rfl
          · split
            · exact hnack _ rfl rfl
            · split
              · apply Ok.ret
                refine Good.post (Good.updConf' ?_ m.cmds hq' (by simp) m.seq) ?_
                · refine hG0.replaceLb (by first | exact hc | simpa using hc) hnc ?_ ?_ ?_ ?_ ?_ ?_ ?_
                  all_goals first
                    | exact hcmds
                    | exact fun _ => hne
                    | rfl
                    | exact stOk_pre _
                    | exact pre_ne_none _
                simp only [List.mem_singleton, forall_eq]; exact (ho _).1 _ rfl rfl
              · next hcond =>
                have hrl : m.replica = rid32 L :=
                  Classical.byContradiction fun hx => hcond (by simp [hx])
                apply Ok.ret
                refine Good.post (Good.updConf' ?_ m.cmds hq' (by simp) m.seq) ?_
                · refine hG0.replaceLb (by first | exact hc | simpa using hc) hnc ?_ ?_ ?_ ?_ ?_ ?_ ?_
                  all_goals first
                    | exact hcmds
                    | exact fun _ => hne
                    | rfl
                    | exact stOk_pre _
                    | exact pre_ne_none _
                simp only [List.mem_singleton, forall_eq]; exact (ho _).2 hrl
        · next hx =>
          exact (OkO.not_none (updAttr_ok _ (confOk hI hG0.si) _ _ _ _)
            (fun a ha => hx a.1 a.2.1 a.2.2 ha)).elim

theorem updateCommitted_form {s s' : RState} {q : w32} (h : updateCommitted s q = some s') :
    ∃ cu, s' = { s with committedUpTo := cu } := by
  simp only [updateCommitted] at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · cases h

theorem Good.updCommitted' {st : Fin 3 → RState} (hI : InvS st) {r : Fin 3} {s : RState}
    (h : Good st r s) {q : w32} {q' : Fin 3} (hq : q = rid32 q') :
    OkO (updateCommitted s q) (fun s' => Good st r s' ∧ ∃ cu, s' = { s with committedUpTo := cu }) := by
  subst hq
  obtain ⟨s', h1, h2⟩ := h.updCommitted hI q'
  exact ⟨s', h1, h2, updateCommitted_form h1⟩

/-- The commit at the proposer (`leaderCommit`): the copy `c` (from `c0`, with the same commands,
leader, slot) committed with bookkeeping `lb` (from `c0`'s, the same proposals and candidate). -/
theorem leaderCommit_ok {st : Fin 3 → RState} {r : Fin 3} (hI : InvS st) {S : RState}
    (hG : Good st r S) {q i : w32} {q' : Fin 3} (hq : q = rid32 q') {c0 c : Copy}
    (hc0 : S.inst q i = some c0) (hne : c0.status ≠ St.EXECUTED) (hcm : c.cmds = c0.cmds)
    (hl : c.leader = c0.leader) (hs : c.slot = c0.slot) {lb0 lb : LB} (hlb0 : c0.lb = some lb0)
    (hp : lb.clientProposals = lb0.clientProposals) (hri : lb.recoveryInst = lb0.recoveryInst) :
    Ok (leaderCommit S q i c lb) (Post st r) := by
  obtain ⟨hb, hcok⟩ := hG.copy hc0
  obtain ⟨hcm0, -, hl0, hs0, -, hlb⟩ := hcok
  have hLB : LBok lb := by
    obtain ⟨a, b⟩ := hlb lb0 hlb0
    exact ⟨hp ▸ a, hri ▸ b⟩
  have hG1 : Good st r (S.setInst q i { c with status := St.COMMITTED, lb := some lb }) := by
    refine hG.setInst hb ⟨hcm ▸ hcm0, fun h => by exfalso; simp only at h; revert h; decide,
      hl ▸ hl0, hs ▸ hs0, stOk_of (by simp only; decide), fun lb' h => by cases h; exact hLB⟩ ?_ ?_
    · intro hq'
      obtain ⟨-, -, o3⟩ := (hG.si.ownOK i c0 (hq' ▸ hc0))
      refine ⟨(by simp only; decide), (fun h => by simp at h), ?_⟩
      intro lb' h; simp only [Option.some.injEq] at h; subst h; rw [hp]; exact o3 lb0 hlb0
    · intro c' h; rw [hc0] at h; cases h
      exact ⟨fun _ => Or.inr (Or.inl rfl), fun hx => absurd hx hne⟩
  obtain ⟨S2, hS2, hG2, cu, rfl⟩ := hG1.updCommitted' hI hq
  have hid := (hI r).id
  have hid2 : ({ S.setInst q i { c with status := St.COMMITTED, lb := some lb } with
      committedUpTo := cu }).id = rid32 r := by rw [← hG.si.id]; rfl
  simp only [leaderCommit, hS2]
  have hout : ∀ (S' : RState) (c' : Copy), c'.cmds = c.cmds → ∀ x ∈ (peers r).map
      (fun d => Out.send d (Msg.commit (ECommitM.mk q i c'.cmds c'.seq c'.deps c'.base))),
      OutOk (Pf st) (upd st r S') x := by
    intro S' c' hc' x hx
    simp only [List.mem_map] at hx
    obtain ⟨d, -, rfl⟩ := hx
    simp only [OutOk, MInv]
    exact ⟨hb, by rw [hc', hcm]; exact hcm0⟩
  split
  · next hcond =>
    have hG3 := (hG2.propAppend lb.clientProposals (fun p hp' => hLB.1 p hp')).setInst
      (q := q) (i := i) (c := { c with status := St.COMMITTED, lb := none }) hb
      ⟨hcm ▸ hcm0, (fun h => by exfalso; simp only at h; revert h; decide),
        hl ▸ hl0, hs ▸ hs0, stOk_of (by simp only; decide), (fun lb' h => by simp at h)⟩
      (fun _ => ⟨(by simp only; decide), (fun _ => Or.inl rfl), (fun lb' h => by simp at h)⟩)
      (fun c' h => by
        simp only [setInst_inst] at h; simp at h; subst h
        exact ⟨fun _ => Or.inr (Or.inl rfl), fun hx => ⟨by revert hx; simp only; decide, rfl⟩⟩)
    rw [bcastCommit, bcast_eq (by simpa using hid2)]
    exact Ok.ret (hG3.post (hout _ _ rfl))
  · rw [bcastCommit, bcast_eq hid2]
    exact Ok.ret (hG2.post (hout _ _ rfl))

end Perennial.gryff.pure.tot
