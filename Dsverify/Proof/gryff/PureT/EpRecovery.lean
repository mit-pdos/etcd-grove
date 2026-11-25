/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureT/EpRecovery.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A2 (totality): phase 1 (`startPhase1`), the recovery (`startRecoveryForInstance`,
`handlePrepareReply`).
-/
module

public import Dsverify.Proof.gryff.PureT.EpReplies

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.tot

open model kahn

theorem InstB.inBox' {P : Fin 3 → Nat} (hP : ∀ q, P q ≤ 24) {q i : w32} (h : InstB P q i) :
    model.inBox q i = true := by
  obtain ⟨q', rfl, hlt⟩ := h
  have h24 := hP q'
  have hq := rid32_toInt q'
  have hi := toInt_small (x := i) (by omega)
  unfold model.inBox
  simp only [SLOTS, sint.Z]
  apply decide_eq_true
  have := q'.isLt
  omega

/-- `startPhase1` of a batch `cmds` (non-empty, of the system's shape) at a state `S` whose copy
of `(q, i)` may be replaced by the new PREACCEPTED copy. -/
theorem startPhase1_ok {st' : Fin 3 → RState} {r : Fin 3} (hP : ∀ q, Pf st' q ≤ 24) {S : RState}
    (hid : S.id = rid32 r)
    (hconf : ∀ q : Nat, q < 3 → ∀ hi, S.confAt q = some hi →
      inBox (BitVec.ofNat 32 q) hi = true ∧ (S.inst (BitVec.ofNat 32 q) hi).isSome)
    {q i : w32} {q' : Fin 3} (hq : q = rid32 q') (hb : InstB (Pf st') q i) (b : w32)
    (proposals : List Proposal) {cmds : List Cmd} (hcm : cmdsOk cmds = true) (hne : cmds ≠ [])
    (hG : ∀ c : Copy, c.cmds = cmds → c.status = St.PREACCEPTED → c.slot = i → c.leader = q →
      (∃ lb, c.lb = some lb ∧ lb.clientProposals = proposals ∧ lb.recoveryInst = none) →
      Good st' r (S.setInst q i c)) :
    Ok (startPhase1 S q i b proposals cmds) (Post st' r) := by
  obtain ⟨c0, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
  have hh : cmds.head? = some c0 := by rw [hcs]; rfl
  tsimp [startPhase1, hh, hb.inBox' hP]
  split
  all_goals
    split
    · rename_i seq deps _ _
      split
      · rename_i outs heq
        refine Ok.ret (Good.post (Good.updConf' (hG _ ?_ ?_ ?_ ?_ ?_) cmds hq (by simp) seq)
          (OkO.of_eq (preAccept_out (by simp [hid]) hb (by simp) b hcm hne seq deps _) heq))
        all_goals first | rfl | exact ⟨_, rfl, rfl, rfl⟩
      · rename_i hx
        exact (OkO.not_none (preAccept_out (st := st') (r := r) (by simp [hid]) hb (by simp) b hcm hne seq
          deps _) hx).elim
    · rename_i hx
      exact (OkO.not_none (updAttr_ok S hconf _ _ _ _) (fun a ha => hx a.1 a.2.1 a.2.2 ha)).elim

theorem rowOk_eq {q : w32} (h : rowOk q = true) : ∃ q' : Fin 3, q = rid32 q' := by
  simp only [rowOk, decide_eq_true_eq, sint.Z] at h
  have hq : q.toNat < 3 := by
    rw [BitVec.toInt_eq_toNat_cond] at h
    split at h <;> omega
  refine ⟨⟨q.toNat, hq⟩, ?_⟩
  simp [rid32]

theorem recover_instB {st : Fin 3 → RState} {r : Fin 3} (hI : InvS st) {q i : w32}
    (hg : (rowOk q && sle 0 i && slt i ((st r).crt q)) = true) : InstB (Pf st) q i := by
  simp only [Bool.and_eq_true] at hg
  obtain ⟨⟨h1, h2⟩, h3⟩ := hg
  obtain ⟨q', rfl⟩ := rowOk_eq h1
  have hc := (hI r).crt q'
  have hP := Pf_le hI q'
  have e2 := toInt_small (x := (st r).crt (rid32 q')) (by omega)
  simp only [sle, slt, decide_eq_true_eq, sint.Z] at h2 h3
  have h2' : 0 ≤ i.toInt := by simpa using h2
  have hi : i.toInt = i.toNat := by
    have := BitVec.toInt_eq_toNat_cond i
    split at this
    · exact this
    · omega
  refine ⟨q', rfl, ?_⟩
  omega

/-- A copy given new recovery bookkeeping (keeping its proposals, if it had bookkeeping). -/
theorem Good.recCopy {st : Fin 3 → RState} {r : Fin 3} {S : RState} (h : Good st r S) {q i : w32}
    {c c' : Copy} (hc : S.inst q i = some c) (hnc : ¬ committedSt c.status)
    (hcm : c'.cmds = c.cmds) (hst : c'.status = c.status) (hl : c'.leader = c.leader)
    (hs : c'.slot = c.slot)
    (hlb : ∃ lb, c'.lb = some lb ∧ LBok lb ∧
      ∀ lb0, c.lb = some lb0 → lb.clientProposals = lb0.clientProposals) :
    Good st r (S.setInst q i c') := by
  obtain ⟨hb, hcok⟩ := h.copy hc
  obtain ⟨hcm0, hpre0, hl0, hs0, hst0, -⟩ := hcok
  obtain ⟨lb, hlb, hLB, hp⟩ := hlb
  refine h.setInst hb ⟨hcm ▸ hcm0, by rw [hst, hcm]; exact hpre0, hl ▸ hl0, hs ▸ hs0, hst ▸ hst0,
    fun lb' h => by rw [hlb] at h; simp only [Option.some.injEq] at h; subst h; exact hLB⟩ ?_ ?_
  · intro hq'
    obtain ⟨o1, o2, o3⟩ := (h.si.ownOK i c (hq' ▸ hc))
    refine ⟨(by rw [hst]; exact o1), (fun h => by rw [hlb] at h; cases h), ?_⟩
    intro lb' h; rw [hlb] at h; simp only [Option.some.injEq] at h; subst h
    cases hcl : c.lb with
    | none => exact absurd (o2 hcl) hnc
    | some lb0 => rw [hp lb0 hcl]; exact o3 lb0 hcl
  · intro c1 h1; rw [hc] at h1; cases h1
    exact ⟨fun _ => Or.inl (by rw [hlb]; simp), fun hx => absurd (Or.inr hx) hnc⟩

theorem stepRecover_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (q i : w32)
    (hg : (rowOk q && sle 0 i && slt i ((st r).crt q)) = true) :
    Ok (stepRecover (st r) q i) (Post st r) := by
  have hid := (hI r).id
  have hb : InstB (Pf st) q i := recover_instB hI hg
  have e1 : ¬ (St.NONE = St.ACCEPTED) := by decide
  have e2 : sge St.NONE St.PREACCEPTED = false := by decide
  cases hc : (st r).inst q i with
  | none =>
    tsimp [stepRecover, hg, hb.inBox hI, hc, setInst_id, hid, e1, e2]
    split
    · rename_i outs heq
      refine Ok.ret (Good.post (Good.newCopy (Good.refl hI) hb hc ?_)
        (OkO.of_eq (prepare_out (by simp [hid]) hb (by simp) _) heq))
      refine ⟨rfl, fun h => by exfalso; simp only at h; revert h; decide, rfl, rfl,
        stOk_of (by simp only; decide), ?_⟩
      intro lb h; simp only [Option.some.injEq] at h; subst h
      exact ⟨by simp, by simp⟩
    · rename_i hx
      exact (OkO.not_none (prepare_out (st := st) (r := r) (by simp [hid]) hb (by simp) _) hx).elim
  | some c =>
    tsimp [stepRecover, hg, hb.inBox hI, hc, setInst_id, hid]
    obtain ⟨hcm0, hpre0, -, -, hst0, hlbok⟩ := ((hI r).inst _ _ c hc).2
    split
    · exact Ok.ret ((Good.refl hI).post (by simp))
    · rename_i hnc0
      have hnc : ¬ committedSt c.status := hnc0
      split
      · exact Ok.ret ((Good.refl hI).post (by simp))
      · have hG : ∀ c' : Copy, c'.cmds = c.cmds → c'.status = c.status → c'.leader = c.leader →
            c'.slot = c.slot → (∃ lb, c'.lb = some lb ∧ LBok lb ∧
              ∀ lb0, c.lb = some lb0 → lb.clientProposals = lb0.clientProposals) →
            Good st r ((st r).setInst q i c') :=
          fun c' a b d e f => (Good.refl hI).recCopy hc hnc a b d e f
        split
        · rename_i outs heq
          refine Ok.ret (Good.post (hG _ rfl rfl rfl rfl ?_)
            (OkO.of_eq (prepare_out (by simp [hid]) hb (by simp) _) heq))
          refine ⟨_, rfl, ⟨?_, ?_⟩, ?_⟩
          · intro p hp
            simp only at hp
            split at hp
            · rename_i lb0 hlb0; exact (hlbok lb0 hlb0).1 p hp
            · simp at hp
          · intro ir hir
            simp only at hir
            split at hir
            · rename_i hacc
              simp only [Option.some.injEq] at hir; subst hir
              refine ⟨Or.inr (Or.inr hacc), hcm0, fun h => absurd hacc h, fun h => ?_⟩
              exact absurd rfl h
            · rename_i hnacc
              split at hir
              · rename_i hge
                simp only [Option.some.injEq] at hir; subst hir
                have hpe : c.status = St.PREACCEPTED ∨ c.status = St.PREACCEPTED_EQ := by
                  rcases hst0 with h | h | h | h | h | h
                  · rw [h] at hge; exact absurd hge (by decide)
                  · exact Or.inl h
                  · exact Or.inr h
                  · exact absurd h hnacc
                  · exact absurd (Or.inl h) hnc
                  · exact absurd (Or.inr h) hnc
                refine ⟨Or.imp_right Or.inl hpe, hcm0, fun _ => hpre0 hpe, fun h => ?_⟩
                simp only at h ⊢
                split at h
                · rename_i hh; exact hh.1
                · exact absurd rfl h
              · simp at hir
          · intro lb0 hlb0; simp [hlb0]
        · rename_i hx
          exact (OkO.not_none (prepare_out (st := st) (r := r) (by simp [hid]) hb (by simp) _) hx).elim

/-- A copy with bookkeeping replaced by any copy (of the instance, of the system's shape) with
bookkeeping of the same proposals. -/
theorem Good.setLb2 {st : Fin 3 → RState} {r : Fin 3} {S : RState} (h : Good st r S) {q i : w32}
    {c c' : Copy} (hc : S.inst q i = some c) {lb0 : LB} (hlb0 : c.lb = some lb0)
    (hne : c.status ≠ St.EXECUTED) (hcm : cmdsOk c'.cmds = true)
    (hpre : (c'.status = St.PREACCEPTED ∨ c'.status = St.PREACCEPTED_EQ) → c'.cmds ≠ [])
    (hl : c'.leader = q) (hs : c'.slot = i) (hst : stOk c'.status)
    (hnn : c'.status ≠ St.NONE ∨ c'.status = c.status)
    (hlb : ∃ lb, c'.lb = some lb ∧ LBok lb ∧ lb.clientProposals = lb0.clientProposals) :
    Good st r (S.setInst q i c') := by
  obtain ⟨hb, -⟩ := h.copy hc
  obtain ⟨lb, hlb, hLB, hp⟩ := hlb
  refine h.setInst hb ⟨hcm, hpre, hl, hs, hst,
    fun lb' h => by rw [hlb] at h; simp only [Option.some.injEq] at h; subst h; exact hLB⟩ ?_ ?_
  · intro hq'
    obtain ⟨o1, -, o3⟩ := (h.si.ownOK i c (hq' ▸ hc))
    refine ⟨?_, (fun h => by rw [hlb] at h; cases h), ?_⟩
    · rcases hnn with h | h
      · exact h
      · rw [h]; exact o1
    · intro lb' h; rw [hlb] at h; simp only [Option.some.injEq] at h; subst h; rw [hp]
      exact o3 lb0 hlb0
  · intro c1 h1; rw [hc] at h1; cases h1
    exact ⟨fun _ => Or.inl (by rw [hlb]; simp), fun hx => absurd hx hne⟩

theorem NHALF_half : ((NHALF + 1) / 2 : w64) = NHALF := by decide

theorem ne_zero_of_sge {x : w64} (h : sge x NHALF = true) : x ≠ 0 := by
  intro hx; subst hx; revert h; decide

theorem riAcc_ok {cmds : List Cmd} (hcm : cmdsOk cmds = true) (x : RecoveryInstance)
    (hs : x.status = St.ACCEPTED) (hc : x.cmds = cmds) (hn : x.preAcceptCount = 0) : RIok x :=
  ⟨Or.inr (Or.inr hs), hc ▸ hcm, fun h => absurd hs h, fun h => absurd hn h⟩

theorem setInst_inst_self (s : RState) (q i : w32) (c : Copy) : (s.setInst q i c).inst q i = some c := by
  simp

theorem tpa_contra (ir : RecoveryInstance) (hok : RIok ir)
    (h1 : ¬(ir.status = St.ACCEPTED ∨ (!ir.leaderResponded) = true ∧
      sge ir.preAcceptCount NHALF = true ∧ ir.status = St.PREACCEPTED_EQ))
    (h2 : (!ir.leaderResponded) = true ∧ sge ir.preAcceptCount ((NHALF + 1) / 2) = true) : False := by
  rw [NHALF_half] at h2
  exact h1 (Or.inr ⟨h2.1, h2.2, hok.2.2.2 (ne_zero_of_sge h2.2)⟩)

/-- The restart of phase 1 by a recovery (G24's last case): the candidate's command. -/
theorem restart_ok {st : Fin 3 → RState} {r : Fin 3} (hI : InvS st) {S1 : RState}
    (hS1 : Good st r S1) (hid : S1.id = rid32 r) {q i : w32} {q' : Fin 3} (hq : q = rid32 q')
    (hb : InstB (Pf st) q i) {c1 : Copy} (hc1 : S1.inst q i = some c1)
    (hne1 : c1.status ≠ St.EXECUTED) {props : List Proposal}
    (hlbx : ∃ lb1, c1.lb = some lb1 ∧ LBok lb1 ∧ props = lb1.clientProposals)
    {cmds : List Cmd} (hcm : cmdsOk cmds = true) (hne : cmds ≠ []) (b : w32) :
    Ok (startPhase1 S1 q i b props cmds) (Post st r) := by
  obtain ⟨lb1, hlb1, hLB1, hp⟩ := hlbx
  refine startPhase1_ok (Pf_le hI) hid (confOk hI hS1.si) hq hb b props hcm hne ?_
  intro c' h1 h2 h3 h4 h5
  obtain ⟨lb', hlb', hp', hri'⟩ := h5
  refine hS1.setLb2 hc1 hlb1 hne1 (h1 ▸ hcm) (fun _ => h1 ▸ hne) h4 h3
    (stOk_of (by rw [h2]; decide)) (Or.inl (by rw [h2]; decide)) ⟨lb', hlb', ⟨?_, ?_⟩, ?_⟩
  · rw [hp', hp]; exact hLB1.1
  · intro ir' h; rw [hri'] at h; cases h
  · rw [hp', hp]

theorem riM_ok {mst : w8} {mcmds : List Cmd}
    (hP : mst = St.PREACCEPTED ∨ mst = St.PREACCEPTED_EQ) (hcm : cmdsOk mcmds = true)
    (hne : mcmds ≠ []) (x : RecoveryInstance) (hs : x.status = mst) (hc : x.cmds = mcmds)
    (hcount : x.preAcceptCount ≠ 0 → mst = St.PREACCEPTED_EQ) : RIok x := by
  refine ⟨?_, hc ▸ hcm, fun _ => hc ▸ hne, fun h => hs ▸ hcount h⟩
  rw [hs]; rcases hP with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem cnt_ok (st : w8) (a b : Bool) :
    (if (st == St.PREACCEPTED_EQ && a && b) = true then (1 : w64) else 0) ≠ 0 →
      st = St.PREACCEPTED_EQ := by
  intro h
  split at h
  · rename_i hh; simp only [Bool.and_eq_true, beq_iff_eq] at hh; exact hh.1.1
  · exact absurd rfl h

theorem riSame_ok (ri : RecoveryInstance) (hR : RIok ri) (x : RecoveryInstance)
    (hs : x.status = ri.status) (hc : x.cmds = ri.cmds) (hn : x.preAcceptCount = ri.preAcceptCount) :
    RIok x := by
  obtain ⟨h1, h2, h3, h4⟩ := hR
  exact ⟨hs ▸ h1, hc ▸ h2, fun h => hc ▸ h3 (hs ▸ h), fun h => hs ▸ h4 (hn ▸ h)⟩

theorem and4_last {a b c d : Bool} (h : (a && b && c && d) = true) : d = true := by
  simp only [Bool.and_eq_true] at h; exact h.2

theorem riInc_ok (ri : RecoveryInstance) (hR : RIok ri) (hpos : sgt ri.preAcceptCount 0 = true)
    (x : RecoveryInstance) (hs : x.status = ri.status) (hc : x.cmds = ri.cmds) : RIok x := by
  have hne : ri.preAcceptCount ≠ 0 := by intro h; rw [h] at hpos; revert hpos; decide
  have hEQ := hR.2.2.2 hne
  obtain ⟨h1, h2, h3, -⟩ := hR
  exact ⟨hs ▸ h1, hc ▸ h2, fun h => hc ▸ h3 (hs ▸ h), fun _ => hs ▸ hEQ⟩

set_option hygiene false in
/-- A recovery candidate's shape, at a prepare-reply leaf. -/
macro "riclose" : tactic => `(tactic| first
  | exact hR0
  | (intro ir h; simp at h; done)
  | (intro ir h; simp only [Option.some.injEq] at h; subst h
     first
       | exact riAcc_ok hmcm _ rfl rfl rfl
       | exact hR0 _ rfl
       | exact hR0 _ hri
       | exact riM_ok hP hmcm (hmpre hP) _ rfl rfl (cnt_ok _ _ _)
       | (refine riM_ok hP hmcm (hmpre hP) _ rfl rfl ?_; intro _; simp_all)
       | exact riInc_ok _ (hR0 _ (by assumption)) (by assumption) _ rfl rfl
       | (refine riInc_ok _ (hR0 _ hri) ?_ _ rfl rfl; exact and4_last (by assumption))
       | exact riSame_ok _ (hR0 _ hri) _ rfl rfl rfl))

set_option hygiene false in
/-- A prepare-reply leaf storing bookkeeping on the copy. -/
macro "prlb" : tactic => `(tactic|
  (refine Ok.ret (Good.post (Good.setLb2 (Good.refl hI) hc hlb0 hne ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by simp))
   all_goals first
     | exact hcm0
     | exact hpre0
     | exact hl0
     | exact hs0
     | exact hst0
     | exact Or.inr rfl
     | (refine ⟨_, rfl, ⟨hP0, ?_⟩, rfl⟩; riclose)))

set_option hygiene false in
/-- A prepare-reply leaf sending an Accept for the copy (the `some` branch of its match). -/
macro "pracc" : tactic => `(tactic|
  (refine Ok.ret (Good.post (Good.setLb2 (Good.refl hI) hc hlb0 hne ?_ ?_ ?_ ?_ ?_ ?_ ?_)
     (OkO.of_eq (accept_out ?_ hb ?_ _ ?_ _ _ _) (by assumption)))
   all_goals first
     | (simpa using hid)
     | (simp; done)
     | exact hmcm
     | exact hcm0
     | rfl
     | exact stOk_of (by simp only; decide)
     | exact Or.inl (by simp only; decide)
     | (intro h; exfalso; simp only at h; revert h; decide)
     | (refine ⟨_, rfl, ⟨hP0, ?_⟩, rfl⟩; riclose)
     | (simp only; exact hl0.symm ▸ rfl)
     | (simp only; exact hmcm)
     | (simp only; exact hs0)
     | (simp only; exact hl0)
     | exact (hR0 _ (by assumption)).2.1
     | (simp only; exact (hR0 _ (by assumption)).2.1)))

set_option hygiene false in
/-- The `none` branch of a prepare-reply leaf's `bcastAccept` match. -/
macro "praccnone" : tactic => `(tactic|
  (exfalso
   refine OkO.not_none (accept_out (st := st) (r := r) ?_ hb ?_ _ ?_ _ _ _) (by assumption)
   all_goals first
     | (simpa using hid)
     | (simp; done)
     | exact hmcm
     | exact hcm0
     | rfl
     | assumption
     | exact (hR0 _ (by assumption)).2.1))

set_option hygiene false in
/-- The prepare-reply handler's leaves. -/
macro "prclose" : tactic => `(tactic|
  (repeat' split
   all_goals first
     | exact Ok.ret ((Good.refl hI).post (by simp))
     | prlb
     | pracc
     | praccnone
     | (exfalso; exact tpa_contra _ (hR0 _ (by assumption)) (by assumption) (by assumption))
     | (exfalso; exact absurd (by assumption : sge (0 : w64) ((NHALF + 1) / 2) = true) (by decide))
     | (exfalso; exact tpa_contra { ri with preAcceptCount := ri.preAcceptCount + 1 }
         (riInc_ok _ (hR0 _ hri) (and4_last (by assumption)) _ rfl rfl) (by assumption) (by assumption))
     | (refine restart_ok hI (Good.setLb2 (Good.refl hI) hc hlb0 hne ?_ ?_ ?_ ?_ ?_ ?_ ?_)
         ?_ hq' hb (setInst_inst_self _ _ _ _) ?_ ?_ ?_ ?_ _
        all_goals first
          | (simpa using hid)
          | exact setInst_inst_self _ _ _ _
          | rfl
          | exact hcm0
          | exact hpre0
          | exact hl0
          | exact hs0
          | exact hst0
          | exact Or.inr rfl
          | exact ⟨_, rfl, ⟨hP0, hR0⟩, rfl⟩
          | (refine ⟨_, rfl, ⟨hP0, ?_⟩, rfl⟩; riclose)
          | exact hne
          | exact hmcm
          | exact hmpre hP
          | exact (hR0 _ (by assumption)).2.1
          | exact (hR0 _ (by assumption)).2.2.1 (fun h => (by assumption : ¬ _) (Or.inl h))
          | (intro h; apply (by assumption : ¬ _); exact Or.inl h)
          | (simp only; intro h; apply (by assumption : ¬ _); exact Or.inl h))
     | (exfalso; simp_all; done)))

/-- `tsimp` deciding closed propositions. -/
syntax "tsimpd" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| tsimpd $[[$xs,*]]? $[$loc]?) => do
    let xs := xs.map (·.getElems) |>.getD #[]
    `(tactic| simp (config := {maxSteps := 4000000, decide := true}) only [ne_eq, not_true_eq_false,
      not_false_eq_true, ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true,
      Bool.not_false, never_bind, dead_bind, disabled_bind, pure_bind', map_never, map_dead,
      Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or,
      Bool.or_true, Bool.true_or, if_true, if_false, true_or, or_true, false_or, or_false, true_and,
      and_true, false_and, and_false, $xs,*] $[$loc]?)

set_option maxHeartbeats 4000000 in
/-- `handlePrepareReply` for a reply reporting a PREACCEPTED(_EQ) copy, at a recovering copy. -/
theorem pr_pre (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (m : PrepareReplyM)
    (hb : InstB (Pf st) m.replica m.inst) (c : Copy) (hc : (st r).inst m.replica m.inst = some c)
    (hmcm : cmdsOk m.cmds = true)
    (hmpre : m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ → m.cmds ≠ [])
    (q' : Fin 3) (hq' : m.replica = rid32 q') (hid : (st r).id = rid32 r)
    (f1 : sgt (0 : w64) 0 = false) (f2 : sgt (1 : w64) 0 = true) (f3 : ((0 : w64) == 0) = true)
    (hA : ¬ m.status = St.ACCEPTED) (hC : ¬ (m.status = St.COMMITTED ∨ m.status = St.EXECUTED))
    (hP : m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ)
    (hcm0 : cmdsOk c.cmds = true)
    (hpre0 : (c.status = St.PREACCEPTED ∨ c.status = St.PREACCEPTED_EQ) → c.cmds ≠ [])
    (hl0 : c.leader = m.replica) (hs0 : c.slot = m.inst) (hst0 : stOk c.status)
    (lb0 : LB) (hlb0 : c.lb = some lb0) (hR0 : ∀ ir, lb0.recoveryInst = some ir → RIok ir)
    (hP0 : ∀ p ∈ lb0.clientProposals, p.cmd.ok = true) (hprep : lb0.preparing = true)
    (hnc0 : ¬ (c.status = St.COMMITTED ∨ c.status = St.EXECUTED))
    (hne : c.status ≠ St.EXECUTED) :
    Ok (stepPrepareReply (st r) m) (Post st r) := by
  have f4 : sge (1 : w64) NHALF = true := by decide
  have f5 : sge (1 : w64) ((NHALF + 1) / 2) = true := by decide
  by_cases hok : m.ok = FALSE
  all_goals by_cases hbal : m.ballot = c.ballot
  all_goals rcases hri : lb0.recoveryInst with _ | ri
  all_goals by_cases hacc : m.acceptorId = m.replica
  all_goals by_cases hslt : slt (lb0.prepareOKs + 1) NHALF = true
  all_goals tsimpd [stepPrepareReply, hb.inBox hI, hc, hmcm, setInst_id, hid, hA, hC, hP,
    riOf, hlb0, hprep, hnc0, hok, hbal, hri, hacc, hslt]
  all_goals prclose

theorem stepPrepareReply_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st)
    (m : PrepareReplyM) (hm : MInv (Pf st) st r (.prepareReply m)) :
    Ok (stepPrepareReply (st r) m) (Post st r) := by
  simp only [MInv] at hm
  obtain ⟨hb, ⟨c, hc, hlbc⟩, hmcm, hmpre⟩ := hm
  obtain ⟨q', hq', -⟩ := id hb
  have hcok := ((hI r).inst _ _ c hc).2
  have hid := (hI r).id
  have f1 : sgt (0 : w64) 0 = false := by decide
  have f2 : sgt (1 : w64) 0 = true := by decide
  have f3 : ((0 : w64) == 0) = true := by decide
  by_cases hA : m.status = St.ACCEPTED
  · have g1 : ¬ (m.status = St.COMMITTED ∨ m.status = St.EXECUTED) := by rw [hA]; decide
    have g2 : ¬ (m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ) := by rw [hA]; decide
    tsimpd [stepPrepareReply, hb.inBox hI, hc, hmcm, setInst_id, hid, hA, g1, g2, riOf]
    obtain ⟨hcm0, hpre0, hl0, hs0, hst0, hlbok⟩ := hcok
    split
    · rename_i lb0 hlb0
      have hR0 := (hlbok lb0 hlb0).2
      have hP0 := (hlbok lb0 hlb0).1
      split
      · exact Ok.ret ((Good.refl hI).post (by simp))
      · split
        · exact Ok.ret ((Good.refl hI).post (by simp))
        · rename_i hnc0
          have hne : c.status ≠ St.EXECUTED := fun h => hnc0 (Or.inr h)
          prclose
    · exact Ok.ret ((Good.refl hI).post (by simp))
  · by_cases hC : m.status = St.COMMITTED ∨ m.status = St.EXECUTED
    · obtain ⟨hcm0, hpre0, hl0, hs0, hst0, hlbok⟩ := hcok
      tsimpd [stepPrepareReply, hb.inBox hI, hc, hmcm, setInst_id, hid, hA, hC]
      split
      · rename_i lb0 hlb0
        split
        · exact Ok.ret ((Good.refl hI).post (by simp))
        · split
          · exact Ok.ret ((Good.refl hI).post (by simp))
          · rename_i hnc0
            have hne : c.status ≠ St.EXECUTED := fun h => hnc0 (Or.inr h)
            have hR0 := (hlbok lb0 hlb0).2
            have hP0 := (hlbok lb0 hlb0).1
            repeat' split
            all_goals first
              | exact Ok.ret ((Good.refl hI).post (by simp))
              | prlb
              | (refine Ok.ret (Good.post ((Good.refl hI).commitCopy hc hne hmcm (Or.inr rfl)
                    ?_ ?_ ?_ ?_ ?_) (OkO.of_eq (commit_out ?_ hb hmcm _ _ _) (by assumption)))
                 all_goals first
                   | (simpa using hid)
                   | rfl
                   | (simp only; exact hl0.symm)
                   | (simp only; exact hs0.symm))
              | (exfalso
                 refine OkO.not_none (commit_out (st := st) (r := r) ?_ hb hmcm _ _ _) (by assumption)
                 simpa using hid)
      · exact Ok.ret ((Good.refl hI).post (by simp))
    · by_cases hP : m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ
      · obtain ⟨hcm0, hpre0, hl0, hs0, hst0, hlbok⟩ := hcok
        cases hlb0 : c.lb with
        | none =>
          tsimpd [stepPrepareReply, hb.inBox hI, hc, hmcm, hlb0]
          exact Ok.ret ((Good.refl hI).post (by simp))
        | some lb0 =>
          have hR0 := (hlbok lb0 hlb0).2
          have hP0 := (hlbok lb0 hlb0).1
          by_cases hprep : lb0.preparing = true
          · by_cases hnc0 : c.status = St.COMMITTED ∨ c.status = St.EXECUTED
            · tsimpd [stepPrepareReply, hb.inBox hI, hc, hmcm, hlb0, hprep, hnc0]
              exact Ok.ret ((Good.refl hI).post (by simp))
            · have hne : c.status ≠ St.EXECUTED := fun h => hnc0 (Or.inr h)
              exact pr_pre st r hI m hb c hc hmcm hmpre q' hq' hid f1 f2 f3 hA hC hP hcm0 hpre0 hl0
                hs0 hst0 lb0 hlb0 hR0 hP0 hprep hnc0 hne
          · tsimpd [stepPrepareReply, hb.inBox hI, hc, hmcm, hlb0, hprep]
            exact Ok.ret ((Good.refl hI).post (by simp))
      · obtain ⟨hcm0, hpre0, hl0, hs0, hst0, hlbok⟩ := hcok
        tsimpd [stepPrepareReply, hb.inBox hI, hc, hmcm, setInst_id, hid, hA, hC, hP]
        split
        · rename_i lb0 hlb0
          split
          · exact Ok.ret ((Good.refl hI).post (by simp))
          · split
            · exact Ok.ret ((Good.refl hI).post (by simp))
            · rename_i hnc0
              have hne : c.status ≠ St.EXECUTED := fun h => hnc0 (Or.inr h)
              have hR0 := (hlbok lb0 hlb0).2
              have hP0 := (hlbok lb0 hlb0).1
              prclose
        · exact Ok.ret ((Good.refl hI).post (by simp))

end Perennial.gryff.pure.tot
