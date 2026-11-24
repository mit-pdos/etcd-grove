/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureP/PropQ.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit P: `ProposeChan`'s length (H2b-R3). A replica's re-proposals are conserved: the proposals in
`ProposeChan` plus those in its copies' bookkeeping number at most its client requests (`nReqs`).
Every step either moves proposals between a copy's bookkeeping and `ProposeChan` (`leaderCommit`,
`handleCommit`'s no-op), drops them, keeps them, or (`handlePropose`) adds the request's own
proposal to a new copy's batch. Structural (per replica, any state reached along its run).

The copies' proposals are summed over a support list `L` (no duplicates, every copy with proposals
in it): `SumOn L s`; `Q s` is the conservation; `R s t` its preservation from `s` to `t`.
-/
module

public import Dsverify.Proof.gryff.PureA.Exec

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureP

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.pureA

/-- The number of proposals in a copy's bookkeeping. -/
def pl : Option Copy → Nat
  | some c => match c.lb with
    | some lb => lb.clientProposals.length
    | none => 0
  | none => 0

def SumOn (L : List (w32 × w32)) (s : RState) : Nat := (L.map fun x => pl (s.inst x.1 x.2)).sum

/-- `L` lists every copy with proposals, once. -/
def CovL (L : List (w32 × w32)) (s : RState) : Prop :=
  L.Nodup ∧ ∀ x : w32 × w32, x ∉ L → pl (s.inst x.1 x.2) = 0

/-- The conservation. -/
def Q (s : RState) : Prop := ∃ L, CovL L s ∧ s.proposeQ.length + SumOn L s ≤ s.nReqs

/-- Its preservation. -/
def R (s t : RState) : Prop :=
  ∀ L, CovL L s → ∃ L', CovL L' t ∧
    t.proposeQ.length + SumOn L' t + s.nReqs ≤ s.proposeQ.length + SumOn L s + t.nReqs

theorem R.Q {s t : RState} (h : R s t) (hq : Q s) : Q t := by
  obtain ⟨L, hc, hl⟩ := hq
  obtain ⟨L', hc', hl'⟩ := h L hc
  exact ⟨L', hc', by omega⟩

theorem R_refl (s : RState) : R s s := fun L h => ⟨L, h, Nat.le_refl _⟩

theorem R_trans {a b c : RState} (h1 : R a b) (h2 : R b c) : R a c := by
  intro L h
  obtain ⟨L1, hc1, h1'⟩ := h1 L h
  obtain ⟨L2, hc2, h2'⟩ := h2 L1 hc1
  exact ⟨L2, hc2, by omega⟩

/-! ## Sums under an update -/

theorem sum_agree {L : List (w32 × w32)} {f g : w32 × w32 → Nat} (h : ∀ x ∈ L, f x = g x) :
    (L.map f).sum = (L.map g).sum := by
  rw [List.map_congr_left h]

theorem sum_update {L : List (w32 × w32)} (hn : L.Nodup) {a : w32 × w32} (ha : a ∈ L)
    {f g : w32 × w32 → Nat} (h : ∀ x, x ≠ a → f x = g x) :
    (L.map g).sum + f a = (L.map f).sum + g a := by
  induction L with
  | nil => cases ha
  | cons y L ih =>
    obtain ⟨hy, hn⟩ := List.nodup_cons.1 hn
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 ha with rfl | ha
    · have : (L.map f).sum = (L.map g).sum := sum_agree fun x hx => h x (fun e => hy (e ▸ hx))
      omega
    · have := ih hn ha
      have e : f y = g y := h y (fun e => hy (e ▸ ha))
      omega

theorem setInst_sum {t : RState} {L : List (w32 × w32)} (hc : CovL L t) (q i : w32) (c : Copy) :
    ∃ L', CovL L' (t.setInst q i c) ∧
      SumOn L' (t.setInst q i c) + pl (t.inst q i) = SumOn L t + pl (some c) := by
  have hf : ∀ x : w32 × w32, x ≠ (q, i) →
      pl ((t.setInst q i c).inst x.1 x.2) = pl (t.inst x.1 x.2) := by
    intro x hx
    rw [setInst_inst, if_neg (fun e => hx (Prod.ext e.1 e.2))]
  have hnew : pl ((t.setInst q i c).inst q i) = pl (some c) := by rw [setInst_inst, if_pos ⟨rfl, rfl⟩]
  by_cases ha : (q, i) ∈ L
  · refine ⟨L, ⟨hc.1, fun x hx => ?_⟩, ?_⟩
    · rw [hf x (fun e => hx (e ▸ ha))]; exact hc.2 x hx
    · unfold SumOn
      have := sum_update hc.1 ha (f := fun x => pl (t.inst x.1 x.2))
        (g := fun x => pl ((t.setInst q i c).inst x.1 x.2)) (fun x hx => (hf x hx).symm)
      simp only at this
      rw [hnew] at this; exact this
  · refine ⟨(q, i) :: L, ⟨List.nodup_cons.2 ⟨ha, hc.1⟩, fun x hx => ?_⟩, ?_⟩
    · have hx1 : x ≠ (q, i) := fun e => hx (e ▸ List.mem_cons_self)
      rw [hf x hx1]; exact hc.2 x (fun h => hx (List.mem_cons_of_mem _ h))
    · have h0 : pl (t.inst q i) = 0 := hc.2 (q, i) ha
      unfold SumOn
      simp only [List.map_cons, List.sum_cons]
      rw [hnew, h0, sum_agree (g := fun x => pl (t.inst x.1 x.2))
        (fun x hx => hf x (fun e => ha (e ▸ hx)))]
      omega

/-! ## Combinators -/

theorem R_frame {s t t' : RState} (h : R s t) (e1 : t'.inst = t.inst)
    (e2 : t'.proposeQ.length ≤ t.proposeQ.length) (e3 : t.nReqs ≤ t'.nReqs) : R s t' := by
  intro L hc
  obtain ⟨L1, hc1, h1⟩ := h L hc
  have es : SumOn L1 t' = SumOn L1 t := by unfold SumOn; rw [e1]
  refine ⟨L1, ⟨hc1.1, fun x hx => by rw [e1]; exact hc1.2 x hx⟩, ?_⟩
  omega

theorem R_setInst {s t : RState} (h : R s t) {q i : w32} {c : Copy}
    (hc : pl (some c) ≤ pl (t.inst q i)) : R s (t.setInst q i c) := by
  intro L hL
  obtain ⟨L1, hc1, h1⟩ := h L hL
  obtain ⟨L2, hc2, h2⟩ := setInst_sum hc1 q i c
  refine ⟨L2, hc2, ?_⟩
  have : (t.setInst q i c).proposeQ = t.proposeQ := rfl
  have : (t.setInst q i c).nReqs = t.nReqs := rfl
  simp only [*] at *
  omega

/-- A move of a copy's proposals to `ProposeChan` (its bookkeeping dropped). -/
theorem R_move {s t : RState} (h : R s t) {q i : w32} {c : Copy} {X : List Proposal}
    (hx : X.length ≤ pl (t.inst q i)) (hc : pl (some c) = 0) :
    R s ({ t with proposeQ := t.proposeQ ++ X }.setInst q i c) := by
  intro L hL
  obtain ⟨L1, hc1, h1⟩ := h L hL
  have hc1' : CovL L1 { t with proposeQ := t.proposeQ ++ X } := hc1
  obtain ⟨L2, hc2, h2⟩ := setInst_sum hc1' q i c
  refine ⟨L2, hc2, ?_⟩
  have e1 : SumOn L1 { t with proposeQ := t.proposeQ ++ X } = SumOn L1 t := rfl
  have e2 : ({ t with proposeQ := t.proposeQ ++ X }.setInst q i c).proposeQ.length =
      t.proposeQ.length + X.length := by simp [RState.setInst]
  have e3 : ({ t with proposeQ := t.proposeQ ++ X }.setInst q i c).nReqs = t.nReqs := rfl
  have e4 : ({ t with proposeQ := t.proposeQ ++ X }).inst q i = t.inst q i := rfl
  rw [e1, e4, hc] at h2
  rw [e2, e3]
  omega

theorem updateCommitted_pq {s s' : RState} {q : w32} (h : updateCommitted s q = some s') :
    s'.proposeQ = s.proposeQ ∧ s'.nReqs = s.nReqs := by
  unfold updateCommitted at h; opeel h
  all_goals (cases h; exact ⟨rfl, rfl⟩)

theorem updateConflicts_pq (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).proposeQ = s.proposeQ ∧
      (updateConflicts s cmds q i sq).nReqs = s.nReqs := by
  unfold updateConflicts
  apply forIn_id_invA (P := fun x : RState => x.proposeQ = s.proposeQ ∧ x.nReqs = s.nReqs) _ _ _
    ⟨rfl, rfl⟩
  intro a b hb
  simpa using hb

theorem R_updCommitted {s t t' : RState} {q : w32} (h : R s t) (hu : updateCommitted t q = some t') :
    R s t' :=
  R_frame h (updateCommitted_inst hu).1 (by rw [(updateCommitted_pq hu).1]; exact Nat.le_refl _) (by rw [(updateCommitted_pq hu).2]; exact Nat.le_refl _)
theorem R_updConf {s t : RState} (h : R s t) (cmds : List Cmd) (q i sq : w32) :
    R s (updateConflicts t cmds q i sq) :=
  R_frame h (updateConflicts_inst _ _ _ _ _).1 (by rw [(updateConflicts_pq _ _ _ _ _).1]; exact Nat.le_refl _)
    (by rw [(updateConflicts_pq _ _ _ _ _).2]; exact Nat.le_refl _)
theorem R_setCrt {s t : RState} (h : R s t) (q x : w32) : R s (t.setCrt q x) :=
  R_frame h rfl (Nat.le_refl _) (Nat.le_refl _)
theorem R_prevValTag {s t : RState} (h : R s t) (x : Option ValTag) :
    R s { t with prevValTag := x } := R_frame h rfl (Nat.le_refl _) (Nat.le_refl _)

theorem pl_some (c : Copy) : pl (some c) = match c.lb with
    | some lb => lb.clientProposals.length
    | none => 0 := rfl

open Lean Elab Tactic Meta in
/-- Close `pl (some c') ≤ pl (s.inst q i)` by rewriting with some hypothesis `s.inst q i = some c`. -/
elab "r_inst" : tactic => withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, _) := ty.eq? | continue
    unless lhs.isAppOf ``RState.inst do continue
    let st ← saveState
    try
      let h ← Term.exprToSyntax d.toExpr
      evalTactic (← `(tactic| (rw [$h:term]; simp only [pl]; done)))
      return
    catch _ => st.restore
  throwError "r_inst failed"

macro "r_side" : tactic => `(tactic| (
  try simp only [setCrt_inst', setInst_inst, (updateConflicts_inst _ _ _ _ _).1, if_pos, and_self,
    ↓reduceIte]
  first
    | (simp only [pl]; done)
    | (simp only [pl]; omega)
    | r_inst
    | (simp_all [pl]; done)))

macro "r_fin" : tactic => `(tactic| (
  repeat (first
    | exact R_refl _
    | (apply R_updCommitted ?_ ‹updateCommitted _ _ = some _›)
    | apply R_updConf
    | with_reducible apply R_move
    | apply R_setInst
    | apply R_prevValTag
    | apply R_setCrt)
  all_goals r_side))

set_option maxRecDepth 20000

theorem stepCommit_R {s s' : RState} {m : ECommitM} {o : List Out}
    (h : stepCommit s m = .ok (s', o)) : R s s' := by
  unfold stepCommit at h; peel h
  all_goals (cases h; r_fin)

theorem leaderCommit_R {s s' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (h : leaderCommit s q i c lb = .ok (s', o))
    (hn : lb.clientProposals.length ≤ pl (s.inst q i)) : R s s' := by
  unfold leaderCommit at h; peel h
  all_goals (cases h)
  · refine R_move (R_updCommitted (R_setInst (R_refl _) ?_) ‹_›) ?_ rfl
    · simpa [pl] using hn
    · rw [(updateCommitted_inst ‹_›).1, setInst_inst, if_pos ⟨rfl, rfl⟩]; simp [pl]
  · refine R_updCommitted (R_setInst (R_refl _) ?_) ‹_›
    simpa [pl] using hn

theorem startPhase1_R {s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 s q i b ps cs = .ok (s', o))
    (hn : ps.length ≤ pl (s.inst q i)) : R s s' := by
  unfold startPhase1 at h; peel h
  all_goals (cases h; refine R_updConf (R_setInst (R_refl _) ?_) _ _ _ _; simpa [pl] using hn)

macro "r_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (first
    | (cases $h:ident; r_fin; done)
    | (refine R_trans ?_ (leaderCommit_R $h:ident ?_); r_fin; done)
    | (refine R_trans ?_ (startPhase1_R $h:ident ?_); r_fin; done)
    | skip)))

set_option maxRecDepth 200000 in
theorem stepPreAccept_R {s s' : RState} {m : PreAcceptM} {o : List Out}
    (h : stepPreAccept s m = .ok (s', o)) : R s s' := by
  unfold stepPreAccept at h; r_close h
theorem stepAccept_R {s s' : RState} {m : EAcceptM} {o : List Out}
    (h : stepAccept s m = .ok (s', o)) : R s s' := by
  unfold stepAccept at h; r_close h
theorem stepPreAcceptReply_R {s s' : RState} {m : PreAcceptReplyM} {o : List Out}
    (h : stepPreAcceptReply s m = .ok (s', o)) : R s s' := by
  unfold stepPreAcceptReply at h; r_close h
theorem stepPreAcceptOK_R {s s' : RState} {m : PreAcceptOKM} {o : List Out}
    (h : stepPreAcceptOK s m = .ok (s', o)) : R s s' := by
  unfold stepPreAcceptOK at h; r_close h
theorem stepAcceptReply_R {s s' : RState} {m : AcceptReplyM} {o : List Out}
    (h : stepAcceptReply s m = .ok (s', o)) : R s s' := by
  unfold stepAcceptReply at h; r_close h
theorem stepPrepare_R {s s' : RState} {m : PrepareM} {o : List Out}
    (h : stepPrepare s m = .ok (s', o)) : R s s' := by
  unfold stepPrepare at h; r_close h
theorem stepPrepareReply_R {s s' : RState} {m : PrepareReplyM} {o : List Out}
    (h : stepPrepareReply s m = .ok (s', o)) : R s s' := by
  unfold stepPrepareReply at h; r_close h
theorem handleExecuted_R {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) : R s s' := by
  unfold handleExecuted at h; r_close h
theorem stepRecover_R {s s' : RState} {q i : w32} {o : List Out}
    (h : stepRecover s q i = .ok (s', o)) : R s s' := by
  unfold stepRecover at h; r_close h
theorem stepExec_R {s s' : RState} {q i : w32} {o : List Out}
    (h : stepExec s q i = .ok (s', o)) : R s s' := by
  unfold stepExec at h; r_close h

/-! ## `handlePropose`: one proposal more, one request more -/

theorem SumOn_updConf (L : List (w32 × w32)) (t : RState) (cmds : List Cmd) (q i sq : w32) :
    SumOn L (updateConflicts t cmds q i sq) = SumOn L t := by
  unfold SumOn; rw [(updateConflicts_inst _ _ _ _ _).1]

theorem startPhase1_le {s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 s q i b ps cs = .ok (s', o)) :
    s'.proposeQ = s.proposeQ ∧ s'.nReqs = s.nReqs ∧
      ∀ L, CovL L s → ∃ L', CovL L' s' ∧ SumOn L' s' ≤ SumOn L s + ps.length := by
  unfold startPhase1 at h; peel h
  all_goals (
    cases h
    refine ⟨(updateConflicts_pq _ _ _ _ _).1, (updateConflicts_pq _ _ _ _ _).2, fun L hL => ?_⟩
    obtain ⟨L', hc', he⟩ := setInst_sum hL q i _
    refine ⟨L', ⟨hc'.1, fun x hx => ?_⟩, ?_⟩
    · rw [(updateConflicts_inst _ _ _ _ _).1]; exact hc'.2 x hx
    · rw [SumOn_updConf]; simp only [pl] at he; omega)

theorem handlePropose_le {s s' : RState} {p : Proposal} {o : List Out}
    (h : handlePropose s p = .ok (s', o)) : s'.nReqs = s.nReqs ∧
      ∀ L, CovL L s → ∃ L', CovL L' s' ∧
        s'.proposeQ.length + SumOn L' s' ≤ s.proposeQ.length + SumOn L s + 1 := by
  obtain ⟨-, -, h⟩ := handlePropose_ok h
  unfold handleProposeBody at h
  obtain ⟨e1, e2, h3⟩ := startPhase1_le h
  refine ⟨e2, fun L hL => ?_⟩
  obtain ⟨L', hc', hle⟩ := h3 L hL
  refine ⟨L', hc', ?_⟩
  rw [e1]
  have es : ∀ x, SumOn L ({ s.setCrt s.id (s.crt s.id + 1) with proposeQ := x }) = SumOn L s :=
    fun _ => rfl
  rw [es] at hle
  simp only [List.length_cons, List.length_take, List.length_drop, RState.setCrt] at hle ⊢
  omega

theorem stepClientRMW_R {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {a b : w64}
    {o : List Out} (h : stepClientRMW s rid cid k d a b = .ok (s', o)) : R s s' := by
  unfold stepClientRMW at h; peel h
  obtain ⟨e, hl⟩ := handlePropose_le h
  intro L hL
  obtain ⟨L', hc', hle⟩ := hl L hL
  refine ⟨L', hc', ?_⟩
  simp only at e hle
  rw [e]
  have : SumOn L { s with nReqs := s.nReqs + 1, used := (cid, rid) :: s.used } = SumOn L s := rfl
  rw [this] at hle
  omega

/-! ## The Gryff handlers: `ProposeChan` and the copies untouched, `nReqs` grows -/

/-- What the Gryff handlers keep. -/
def PF (s t : RState) : Prop := t.inst = s.inst ∧ t.proposeQ = s.proposeQ ∧ s.nReqs ≤ t.nReqs

theorem PF.R {s t : RState} (h : PF s t) : R s t :=
  R_frame (R_refl s) h.1 (by rw [h.2.1]; exact Nat.le_refl _) h.2.2

theorem PF.refl (s : RState) : PF s s := ⟨rfl, rfl, Nat.le_refl _⟩

theorem overwrite_PF (s : RState) (v : w64) (t : model.Tag) : PF s (s.overwrite v t) := by
  unfold RState.overwrite; split <;> exact PF.refl _

theorem shortCircuit_PF {s s' : RState} {n : w32} {v : ValTag} {f : Bool} {o : List Out}
    (h : shortCircuit s n v f = some (s', o)) : PF s s' := by
  unfold shortCircuit at h
  opeel h
  all_goals
    cases h
    refine forIn_opt_invA _ _ _ (fun p : RState × List Out => PF s p.1) (PF.refl s) ?_ _ ‹_›
    intro a b st hb hf
    opeel hf
    all_goals (cases hf; exact hb)

theorem shortCircuit_ite_PF {s s' : RState} {c : Prop} [Decidable c] {n : w32} {v : ValTag}
    {f : Bool} {o : List Out}
    (h : (if c then shortCircuit s n v f else some (s, [])) = some (s', o)) : PF s s' := by
  split at h
  · exact shortCircuit_PF h
  · cases h; exact PF.refl _

theorem PF.trans {a b c : RState} (h1 : PF a b) (h2 : PF b c) : PF a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, Nat.le_trans h1.2.2 h2.2.2⟩

macro "pf_fin" : tactic => `(tactic| (
  repeat (first
    | with_reducible exact PF.refl _
    | with_reducible refine PF.trans ?_ (overwrite_PF _ _ _)
    | refine PF.trans ?_ (shortCircuit_PF ‹shortCircuit _ _ _ _ = some _›)
    | refine PF.trans ?_ (shortCircuit_ite_PF ‹(if _ then shortCircuit _ _ _ _ else some _) = some _›))
  all_goals (first
    | exact PF.refl _
    | (refine ⟨rfl, rfl, ?_⟩; simp)
    | (refine ⟨rfl, rfl, ?_⟩; simp; omega)
    | (have hsc := shortCircuit_PF ‹shortCircuit _ _ _ _ = some _›
       exact PF.trans hsc ⟨rfl, rfl, Nat.le_refl _⟩)
    | (have hsc := shortCircuit_ite_PF ‹(if _ then shortCircuit _ _ _ _ else some _) = some _›
       exact PF.trans hsc ⟨rfl, rfl, Nat.le_refl _⟩))))

macro "pf_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (cases $h:ident; pf_fin)))

theorem stepRead1_PF {s s' : RState} {m : Read1ProxiedM} {o : List Out}
    (h : stepRead1 s m = .ok (s', o)) : PF s s' := by
  unfold stepRead1 at h; pf_close h
theorem stepRead2_PF {s s' : RState} {m : Read2ProxiedM} {o : List Out}
    (h : stepRead2 s m = .ok (s', o)) : PF s s' := by
  unfold stepRead2 at h; pf_close h
theorem stepWrite1_PF {s s' : RState} {m : Write1ProxiedM} {o : List Out}
    (h : stepWrite1 s m = .ok (s', o)) : PF s s' := by
  unfold stepWrite1 at h; pf_close h
theorem stepWrite2_PF {s s' : RState} {m : Write2ProxiedM} {o : List Out}
    (h : stepWrite2 s m = .ok (s', o)) : PF s s' := by
  unfold stepWrite2 at h; pf_close h
theorem stepRead1Reply_PF {s s' : RState} {m : Read1ReplyM} {o : List Out}
    (h : stepRead1Reply s m = .ok (s', o)) : PF s s' := by
  unfold stepRead1Reply at h; pf_close h
theorem stepRead2Reply_PF {s s' : RState} {m : Read2ReplyM} {o : List Out}
    (h : stepRead2Reply s m = .ok (s', o)) : PF s s' := by
  unfold stepRead2Reply at h; pf_close h
theorem stepWrite1Reply_PF {s s' : RState} {m : Write1ReplyM} {o : List Out}
    (h : stepWrite1Reply s m = .ok (s', o)) : PF s s' := by
  unfold stepWrite1Reply at h; pf_close h
theorem stepWrite2Reply_PF {s s' : RState} {m : Write2ReplyM} {o : List Out}
    (h : stepWrite2Reply s m = .ok (s', o)) : PF s s' := by
  unfold stepWrite2Reply at h; pf_close h
theorem stepClientWrite_PF {s s' : RState} {rid cid : w32} {k v : w64} {d : Dep} {o : List Out}
    (h : stepClientWrite s rid cid k v d = .ok (s', o)) : PF s s' := by
  unfold stepClientWrite at h; pf_close h
theorem stepClientRead_PF {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {o : List Out}
    (h : stepClientRead s rid cid k d = .ok (s', o)) : PF s s' := by
  unfold stepClientRead at h
  peel h
  cases h
  have hx := ‹forIn _ _ _ = Except.ok s'›
  refine forIn_exc_invA _ _ _ (fun x : RState => PF s x) ?_ ?_ _ hx
  · exact ⟨rfl, rfl, by simp⟩
  intro a b st hb hf
  peel hf
  all_goals (cases hf; exact hb)

theorem stepExecuteOverwrite_R {s s' : RState} {m : ExecuteOverwriteM} {o : List Out}
    (h : stepExecuteOverwrite s m = .ok (s', o)) : R s s' := by
  have hs : R s (s.overwrite m.v m.t) := (overwrite_PF s m.v m.t).R
  unfold stepExecuteOverwrite at h; peel h
  · exact R_trans hs (handleExecuted_R h)
  · cases h; exact hs

/-- **Every step** keeps the conservation. -/
theorem step_R {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) : R s s' := by
  cases e with
  | read => exact (stepClientRead_PF h).R
  | write => exact (stepClientWrite_PF h).R
  | rmw => exact stepClientRMW_R h
  | forceWrite => cases h; exact R_refl _
  | recover => exact stepRecover_R h
  | exec => exact stepExec_R h
  | msg m =>
    cases m with
    | read1 => exact (stepRead1_PF h).R
    | read2 => exact (stepRead2_PF h).R
    | write1 => exact (stepWrite1_PF h).R
    | write2 => exact (stepWrite2_PF h).R
    | read1Reply => exact (stepRead1Reply_PF h).R
    | read2Reply => exact (stepRead2Reply_PF h).R
    | write1Reply => exact (stepWrite1Reply_PF h).R
    | write2Reply => exact (stepWrite2Reply_PF h).R
    | prepare => exact stepPrepare_R h
    | preAccept => exact stepPreAccept_R h
    | accept => exact stepAccept_R h
    | commit => exact stepCommit_R h
    | prepareReply => exact stepPrepareReply_R h
    | preAcceptReply => exact stepPreAcceptReply_R h
    | preAcceptOK => exact stepPreAcceptOK_R h
    | acceptReply => exact stepAcceptReply_R h
    | executed => exact handleExecuted_R h
    | executeOverwrite => exact stepExecuteOverwrite_R h

theorem Q_init (r : Nat) : Q (RState.init r) :=
  ⟨[], ⟨List.nodup_nil, fun _ _ => rfl⟩, by simp [SumOn, RState.init]⟩

/-- Along a replica's run, the conservation holds; so `ProposeChan` is at most `nReqs` long. -/
theorem runP_Q {r : Fin 3} {es : List Ev} {s : RState} {o : List Out}
    (h : kahn.runP gNet r es = some (s, o)) : Q s := by
  induction es using snoc_ind generalizing s o with
  | h0 => cases h; exact Q_init r.val
  | hs es e ih =>
    obtain ⟨s1, o1, o2, h1, h2, -⟩ := kahn.runFrom_append_inv h
    have h2' : gNet.step r s1 e = some (s, o2) := (kahn.runFrom_single r s1 e).symm.trans h2
    exact (step_R (gstep_ok h2')).Q (ih h1)

theorem Q.len {s : RState} (h : Q s) : s.proposeQ.length ≤ s.nReqs := by
  obtain ⟨L, -, h⟩ := h; omega

end Perennial.gryff.pureP
