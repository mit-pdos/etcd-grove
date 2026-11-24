/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/StepRecover.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1, internal (A1a): the step case `inv_recover` of `inv_step` (`Inv.lean`):
`startRecoveryForInstance` (`stepRecover`). The recoverer `a` takes a fresh ballot of its own above
its copy's (`makeBallot_own`), keeps its copy's value with new bookkeeping (preparing, candidate
`recRI` from its own copy) and sends a Prepare to each peer. The history is unchanged; only `a`'s
ballot for the instance grows (`BalLe`). The candidate's facts (`RIOk`): `riOk_rec`; the Prepares'
multiplicities: no Prepare nor OK reply at the fresh ballot was in flight (`MsgOk`'s freshness).
-/
module

public import Dsverify.Proof.gryff.PureA.StepHelp

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn

/-! ## The step, restated -/

def dfltCopy (q i : w32) : Copy :=
  { cmds := [], ballot := 0, status := St.NONE, seq := 0, deps := nildeps, base := vt0, lb := none,
    slot := i, leader := q, vbal := -1 }

def recRI (c : Copy) (sid q : w32) : Option RecoveryInstance :=
  if c.status = St.ACCEPTED then
    some { cmds := c.cmds, status := c.status, seq := c.seq, deps := c.deps, base := c.base,
           preAcceptCount := 0, leaderResponded := false, vbal := c.vbal }
  else if sge c.status St.PREACCEPTED then
    let count : w64 :=
      if c.status = St.PREACCEPTED_EQ ∧ c.vbal = 0 ∧ sid ≠ q then 1 else 0
    some { cmds := c.cmds, status := c.status, seq := c.seq, deps := c.deps, base := c.base,
           preAcceptCount := count, leaderResponded := (sid == q), vbal := c.vbal }
  else none

def recLB (c : Copy) (sid q : w32) : LB :=
  { clientProposals := match c.lb with
      | some lb => lb.clientProposals
      | none => [],
    maxRecvBallot := -1, prepareOKs := 0, allEqual := false, preAcceptOKs := 0, acceptOKs := 0,
    nacks := 0, originalDeps := nildeps, committedDeps := [], recoveryInst := recRI c sid q,
    preparing := true, numReplicasExecuted := 0, repliedClient := false }

def recCopy (c : Copy) (sid q : w32) : Copy :=
  { c with lb := some (recLB c sid q), ballot := makeBallotLargerThan sid c.ballot }

def cpick (s : RState) (q i : w32) : Copy :=
  match s.inst q i with
  | some c => c
  | none => dfltCopy q i

def stepRecover' (s : RState) (q i : w32) : StepRes := do
  if !(rowOk q && sle 0 i && slt i (s.crt q)) then disabled
  if !inBox q i then dead
  if let some c := s.inst q i then
    if c.status = St.COMMITTED ∨ c.status = St.EXECUTED then
      return (s, [])
  if let some c := s.inst q i then
    if sge (c.ballot.sshiftRight 4) maxBallotHi then
      return (s, [])
  let c := recCopy (cpick s q i) s.id q
  let s := s.setInst q i c
  let some outs := bcastPrepare s q i c.ballot | dead
  return (s, outs)

theorem stepRecover_eq (s : RState) (q i : w32) : stepRecover s q i = stepRecover' s q i := rfl

theorem stepRecover_cases {s s' : RState} {q i : w32} {o : List Out}
    (h : stepRecover s q i = .ok (s', o)) :
    (s' = s ∧ o = []) ∨
    ∃ c0, (s.inst q i = some c0 ∨ (s.inst q i = none ∧ c0 = dfltCopy q i)) ∧
      rowOk q = true ∧ 0 ≤ sint.Z i ∧ sint.Z i < sint.Z (s.crt q) ∧
      ¬ isCommitted c0.status ∧ ¬ sge (c0.ballot.sshiftRight 4) maxBallotHi = true ∧
      s' = s.setInst q i (recCopy c0 s.id q) ∧
      bcastPrepare (s.setInst q i (recCopy c0 s.id q)) q i (recCopy c0 s.id q).ballot = some o := by
  rw [stepRecover_eq] at h
  unfold stepRecover' at h; peel h
  all_goals (first
    | (left; cases h; exact ⟨rfl, rfl⟩)
    | skip)
  all_goals (
    right
    cases h
    have hg := ‹¬(!(rowOk q && sle 0 i && slt i (s.crt q))) = true›
    have hg' : (rowOk q = true ∧ sle 0 i = true) ∧ slt i (s.crt q) = true := by simpa using hg
    simp only [sle, slt, decide_eq_true_eq] at hg')
  · rename_i _ c0 hc hcm hsg _ hb
    have e : cpick s q i = c0 := by simp only [cpick, hc]
    rw [e] at hb ⊢
    exact ⟨c0, Or.inl hc, hg'.1.1, hg'.1.2, hg'.2, hcm, hsg, rfl, hb⟩
  · rename_i _ hn _ hb
    have hn' : s.inst q i = none := by
      cases e : s.inst q i with
      | none => rfl
      | some c => exact (hn c e).elim
    have e : cpick s q i = dfltCopy q i := by simp only [cpick, hn']
    rw [e] at hb ⊢
    refine ⟨_, Or.inr ⟨hn', rfl⟩, hg'.1.1, hg'.1.2, hg'.2, ?_, ?_, rfl, hb⟩
    · simp [dfltCopy, isCommitted]; decide
    · simp only [dfltCopy]; decide

/-! ## The candidate -/

section recs
variable {sid q : w32} {c : Copy}

theorem recRI_acc (h : c.status = St.ACCEPTED) :
    recRI c sid q = some
      { cmds := c.cmds, status := c.status, seq := c.seq, deps := c.deps,
        base := c.base, preAcceptCount := 0, leaderResponded := false, vbal := c.vbal } := by
  simp only [recRI, if_pos h]

theorem recRI_pre (h : isPre c.status) :
    recRI c sid q = some
      { cmds := c.cmds, status := c.status, seq := c.seq, deps := c.deps,
        base := c.base,
        preAcceptCount := if c.status = St.PREACCEPTED_EQ ∧ c.vbal = 0 ∧ sid ≠ q then 1 else 0,
        leaderResponded := (sid == q), vbal := c.vbal } := by
  have h1 : c.status ≠ St.ACCEPTED := by rcases h with h | h <;> rw [h] <;> decide
  have h2 : sge c.status St.PREACCEPTED = true := by rcases h with h | h <;> rw [h] <;> decide
  simp only [recRI, if_neg h1, if_pos h2]

theorem recRI_none (h : c.status = St.NONE) : recRI c sid q = none := by
  have h1 : c.status ≠ St.ACCEPTED := by rw [h]; decide
  have h2 : ¬ sge c.status St.PREACCEPTED = true := by rw [h]; decide
  simp only [recRI, if_neg h1, if_neg h2]

end recs

theorem cnt_cases (p : Prop) [Decidable p] :
    sint.Z (if p then (1 : w64) else 0) = (if p then 1 else 0) := by
  split <;> decide

/-- The recoverer's candidate from its own copy `c0` (before the step: `CopyOk`), at its fresh
ballot `nb` above the copy's. -/
theorem riOk_rec {c : Cfg gNet} {G : GG} {q i : w32} {a : Fin 3} {c0 : Copy}
    {bal bal' : Fin 3 → Option Int} {nb : Int}
    (hok : CopyOk c G q i a c0) (hA : AInv (G q i) bal (rowOf q)) (hnc : ¬ isCommitted c0.status)
    (hlt : sint.Z c0.ballot < nb) (hbal' : bal' a = some nb) (hq : q = rid32 (rowOf q))
    (hlead : a = rowOf q → c0.status ≠ St.NONE ∧ ∀ v, ¬ (G q i).fast v) (hnb : 0 < nb) :
    RIOk (G q i) bal' (rowOf q) nb a (recRI c0 (rid32 a) q) := by
  have hvb := hok.vbalLe
  have hne : a ≠ rowOf q → rid32 a ≠ q := fun h e => h (rid32_inj (e.trans hq))
  have heq : (rid32 a == q) = true → a = rowOf q := fun e => rid32_inj ((beq_iff_eq.1 e).trans hq)
  rcases hok.stOk with e | e | e | e
  · -- NONE: no candidate
    rw [recRI_none e]
    have nv := hok.noVotes (Or.inl e)
    refine ⟨⟨⟨nb, hbal', Int.le_refl _⟩, fun b' u _ h => absurd h (nv b' u), fun ha he => ?_,
      fun ha => absurd e (hlead ha).1⟩, ⟨fun r h => (by cases h), fun r h => (by cases h),
      fun r h => (by cases h), fun r h => (by cases h), fun r h => (by cases h)⟩, fun r h => (by cases h)⟩
    rcases hok.eqTrack ha he with h | h | ⟨h, _⟩ | h
    · rw [e] at h; exact absurd h (by decide)
    · exact absurd h hnc
    · rw [e] at h; exact absurd h (by decide)
    · right; obtain ⟨b', h1, h2, h3⟩ := h; exact ⟨b', h1, by omega, h3⟩
  · -- PREACCEPTED*: the copy, counted if unchanged at ballot 0 and not the leader's
    rw [recRI_pre e]
    have nv := hok.noVotes (Or.inr e)
    have hst : c0.status ≠ St.ACCEPTED := by rcases e with e | e <;> rw [e] <;> decide
    have hc01 : ∀ x : Prop, [Decidable x] → 0 ≤ sint.Z (if x then (1 : w64) else 0) ∧
        sint.Z (if x then (1 : w64) else 0) ≤ 1 := fun x _ => by
      rw [cnt_cases]; split <;> omega
    refine ⟨⟨⟨nb, hbal', Int.le_refl _⟩, fun b' u _ h => absurd h (nv b' u), fun ha he => ?_,
      fun ha => ⟨_, rfl, Or.inr ?_⟩⟩,
      ⟨fun r hr hs => ?_, fun r hr => ?_, fun r hr h1 => ?_, fun r hr hl => ?_, fun r hr => ?_⟩,
      fun r hr => ?_⟩
    · rcases hok.eqTrack ha he with h | h | ⟨h1, h2⟩ | h
      · exact absurd h hst
      · exact absurd h hnc
      · left; refine ⟨_, rfl, Or.inr ?_⟩
        simp only; rw [cnt_cases, if_pos ⟨h1, h2, hne ha⟩]; decide
      · right; obtain ⟨b', h1, h2, h3⟩ := h; exact ⟨b', h1, by omega, h3⟩
    · simp only [beq_iff_eq]; rw [ha]; exact hq.symm
    · cases hr; exact absurd hs hst
    · cases hr; have := hc01 (c0.status = St.PREACCEPTED_EQ ∧ c0.vbal = 0 ∧ rid32 a ≠ q)
      simp only; exact ⟨this.1, by omega⟩
    · cases hr
      simp only at h1
      rw [cnt_cases] at h1
      split at h1
      · rename_i hx
        exact ⟨hx.1, hx.2.1, hok.eqCre hx.1 hx.2.1 (fun e => hx.2.2 (by rw [e]; exact hq.symm))⟩
      · omega
    · cases hr
      have ha := heq hl
      subst ha
      exact ⟨⟨nb, hbal', hnb⟩, (hlead rfl).2⟩
    · cases hr; rcases e with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
    · cases hr; exact (hc01 (c0.status = St.PREACCEPTED_EQ ∧ c0.vbal = 0 ∧ rid32 a ≠ q)).2
  · -- ACCEPTED: the copy's vote
    rw [recRI_acc e]
    obtain ⟨hv1, hv2⟩ := hok.accVote e
    have hp := hA.acc_prop _ _ _ hv1
    refine ⟨⟨⟨nb, hbal', Int.le_refl _⟩, fun b' u _ h => ⟨_, rfl, e, hv2 b' u h⟩,
      fun _ _ => Or.inl ⟨_, rfl, Or.inl e⟩, fun _ => ⟨_, rfl, Or.inl e⟩⟩,
      ⟨fun r hr _ => ?_, fun r hr => ?_, fun r hr h1 => ?_, fun r hr hl => ?_,
       fun r hr => ?_⟩, fun r hr => ?_⟩
    · cases hr; exact ⟨hp, hA.prop_nonneg _ _ hp, by simp only; omega⟩
    · cases hr; simp only; decide
    · cases hr; simp only at h1; exact absurd h1 (by decide)
    · cases hr; cases hl
    · cases hr; exact Or.inr (Or.inr e)
    · cases hr; simp only; decide
  · exact absurd e hnc

theorem recCopy_ballot (c : Copy) (sid q : w32) :
    (recCopy c sid q).ballot = makeBallotLargerThan sid c.ballot := rfl

/-- The default copy's facts (no copy: `noCopy`). -/
theorem copyOk_dflt {c : Cfg gNet} {G : GG} {q i : w32} {a : Fin 3}
    (hn : (∀ b u, ¬ (G q i).acc a b u) ∧ ¬ (G q i).eq a) : CopyOk c G q i a (dfltCopy q i) where
  nonneg := by simp only [dfltCopy]; decide
  ballotForm := Or.inl rfl
  vbalLe := by simp only [dfltCopy]; decide
  stOk := Or.inl rfl
  noVotes _ := hn.1
  accVote h := absurd h (by simp only [dfltCopy]; decide)
  committed h := absurd h (by simp only [dfltCopy, isCommitted]; decide)
  rstVbal h := absurd h (by simp only [dfltCopy, isPre]; decide)
  eqCre h := absurd h (by simp only [dfltCopy]; decide)
  leader0 _ _ h := absurd h (by simp only [dfltCopy]; decide)
  ownFresh _ h := absurd (own_pos h) (by simp only [dfltCopy]; decide)
  preparing _ h := by cases h
  eqTrack _ h := absurd h hn.2

/-! ## The main case -/

theorem countP_app1 {l : List Msg} {p : Msg → Bool} {x : Msg} :
    (l ++ [x]).countP p = l.countP p + (if p x then 1 else 0) := by
  rw [List.countP_append]; simp [List.countP_cons]

set_option maxHeartbeats 1000000 in
theorem recover_main {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {q i : w32} {o : List Out} {c0 : Copy}
    (I : CInv c G)
    (hp : Post c a (.recover q i) ((c.st a).setInst q i (recCopy c0 (c.st a).id q)) o c1)
    (hc0 : (c.st a).inst q i = some c0 ∨ ((c.st a).inst q i = none ∧ c0 = dfltCopy q i))
    (hrow : rowOk q = true) (hi0 : 0 ≤ sint.Z i) (hi1 : sint.Z i < sint.Z ((c.st a).crt q))
    (hnc : ¬ isCommitted c0.status) (hsg : ¬ sge (c0.ballot.sshiftRight 4) maxBallotHi = true)
    (hb : bcastPrepare ((c.st a).setInst q i (recCopy c0 (c.st a).id q)) q i
      (recCopy c0 (c.st a).id q).ballot = some o) :
    StepInv c c1 G := by
  have hid : (c.st a).id = rid32 a := I.ids a
  rw [hid] at hp hb
  -- names
  generalize hnc' : recCopy c0 (rid32 a) q = nc at hp hb
  have hq : q = rid32 (rowOf q) := (rid32_rowOf hrow).symm
  have I0 := I.inst q i
  have hok : CopyOk c G q i a c0 := by
    rcases hc0 with h | ⟨h, rfl⟩
    · exact I0.copies a c0 h
    · exact copyOk_dflt (I0.noCopy a h)
  have hbold : ∀ B, balOf c q i a = some B → B = sint.Z c0.ballot := by
    intro B hB
    simp only [balOf, cpOf] at hB
    rcases hc0 with h | ⟨h, -⟩ <;> rw [h] at hB <;> cases hB; rfl
  obtain ⟨hown, hlt⟩ := makeBallot_own (a := a) hok.nonneg hsg
  rw [← recCopy_ballot c0 (rid32 a) q, hnc'] at hown hlt
  have hnb : 0 < sint.Z nc.ballot := own_pos hown
  have hncst : nc.status = c0.status := by rw [← hnc']; rfl
  have hncvb : nc.vbal = c0.vbal := by rw [← hnc']; rfl
  have hncva : nc.valA = c0.valA := by rw [← hnc']; rfl
  have hnclb : nc.lb = some (recLB c0 (rid32 a) q) := by rw [← hnc']; rfl
  -- the configuration after
  have hst1 : ∀ x : Fin 3, c1.st x = if x = a then (c.st a).setInst q i nc else c.st x := fun x => by
    rw [hp.1]
  have hcp1 : ∀ (x : Fin 3) q' j, cpOf c1 x q' j =
      if x = a ∧ q' = q ∧ j = i then some nc else cpOf c x q' j := fun x q' j => by
    show (c1.st x).inst q' j = _
    rw [hst1 x]
    by_cases hx : x = a
    · subst hx; simp [cpOf, RState.setInst]
    · simp [hx, cpOf]
  have hcrt : ∀ (x : Fin 3) p, (c1.st x).crt p = (c.st x).crt p := fun x p => by
    rw [hst1 x]
    by_cases hx : x = a
    · subst hx; simp [RState.crt, RState.setInst]
    · simp [hx]
  have hcrtI : ∀ x : Fin 3, (c1.st x).crtInstance = (c.st x).crtInstance := fun x => by
    rw [hst1 x]
    by_cases hx : x = a
    · subst hx; simp [RState.setInst]
    · simp [hx]
  have hid1 : ∀ x : Fin 3, (c1.st x).id = (c.st x).id := fun x => by
    rw [hst1 x]
    by_cases hx : x = a
    · subst hx; simp [RState.setInst]
    · simp [hx]
  let pm : PrepareM := { leaderId := (c.st a).id, replica := q, inst := i, ballot := nc.ballot }
  have hsent : ∀ d : Fin 3, sentTo gNet d o = if d = a then [] else [Msg.prepare pm] :=
    bcast_sentTo (s := (c.st a).setInst q i nc) (by simp only [RState.setInst]; exact hid) (by exact hb)
  have hinf0 : ∀ d : Fin 3, c1.inflight d =
      c.inflight d ++ (if d = a then ([] : List gNet.M) else [Msg.prepare pm]) :=
    fun d => by
      rw [hp.2]
      show (if d = a then consume (gNet.recv (Ev.recover q i)) (c.inflight d) else c.inflight d) ++
        sentTo gNet d o = _
      rw [hsent d]
      have : consume (gNet.recv (Ev.recover q i)) (c.inflight d) = c.inflight d := rfl
      rw [this, ite_self]; rfl
  have hinf : ∀ d : Fin 3, c1.inflight d =
      @HAppend.hAppend (List Msg) (List Msg) (List Msg) _ (c.inflight d)
        (if d = a then [] else [Msg.prepare pm]) :=
    fun d => hinf0 d
  -- the leader's copy (`leaderHas`); if `a` is the leader, it is `c0`
  have hLcrt : sint.Z i < sint.Z ((c.st (rowOf q)).crt q) := by
    have := I.crtOwn a (rowOf q); rw [← hq] at this; omega
  obtain ⟨cpL, hcpL, hcpLn⟩ := I.leaderHas (rowOf q) i hi0 (by rw [← hq]; exact hLcrt)
  rw [← hq] at hcpL
  have hc0L : a = rowOf q → cpOf c a q i = some c0 := fun e => by
    rcases hc0 with h | ⟨h, -⟩
    · exact h
    · rw [e] at h; simp only [cpOf] at hcpL; rw [h] at hcpL; cases hcpL
  have hlead : a = rowOf q → c0.status ≠ St.NONE ∧ ∀ v, ¬ (G q i).fast v := fun e => by
    have h1 := hc0L e
    rw [e] at h1; rw [h1] at hcpL; cases hcpL
    refine ⟨hcpLn, fun v hv => ?_⟩
    obtain ⟨cp, hcp, hcm⟩ := I0.fastL v hv
    rw [h1] at hcp; cases hcp; exact hnc hcm
  -- ballots
  have hbal1 : ∀ (x : Fin 3) q' j, balOf c1 q' j x =
      if x = a ∧ q' = q ∧ j = i then some (sint.Z nc.ballot) else balOf c q' j x := by
    intro x q' j; simp only [balOf, hcp1]; split <;> rfl
  have hBL : ∀ q' j, BalLe (balOf c q' j) (balOf c1 q' j) := by
    intro q' j x B hB
    rw [hbal1]; split
    · rename_i e; obtain ⟨rfl, rfl, rfl⟩ := e
      exact ⟨_, rfl, by rw [hbold B hB]; omega⟩
    · exact ⟨B, hB, Int.le_refl _⟩
  have hbalA : balOf c1 q i a = some (sint.Z nc.ballot) := by
    rw [hbal1, if_pos ⟨rfl, rfl, rfl⟩]
  -- the old copies stay, with their status
  have stat1 : ∀ (x : Fin 3) q' j cp, cpOf c x q' j = some cp →
      ∃ cp', cpOf c1 x q' j = some cp' ∧ cp'.status = cp.status := by
    intro x q' j cp hc
    rw [hcp1]; split
    · rename_i e; obtain ⟨rfl, rfl, rfl⟩ := e
      refine ⟨nc, rfl, ?_⟩
      simp only [cpOf] at hc
      rcases hc0 with h | ⟨h, -⟩
      · rw [h] at hc; cases hc; exact hncst
      · rw [h] at hc; cases hc
    · exact ⟨cp, hc, rfl⟩
  -- no Prepare nor OK reply at the fresh ballot was in flight
  have noPrep : ∀ (Y : Fin 3) m, m ∈ c.inflight Y → isPrepareAt q i nc.ballot m = false := by
    intro Y m hm
    cases m with
    | prepare x =>
      cases e : isPrepareAt q i nc.ballot (.prepare x)
      · rfl
      simp only [isPrepareAt, Bool.and_eq_true, beq_iff_eq] at e
      obtain ⟨⟨e1, e2⟩, e3⟩ := e
      obtain ⟨-, R', hown', -, -, B, hB, hle⟩ := I.msgs Y _ hm
      rw [e1, e2] at hB; rw [e3] at hown' hle
      have := own_uniq hown' hown; subst this
      have := hbold B hB; omega
    | _ => rfl
  have noOK : ∀ (Y : Fin 3) m, m ∈ c.inflight a → isOKReplyAt q i nc.ballot Y m = false := by
    intro Y m hm
    cases m with
    | prepareReply x =>
      cases e : isOKReplyAt q i nc.ballot Y (.prepareReply x)
      · rfl
      simp only [isOKReplyAt, Bool.and_eq_true, beq_iff_eq] at e
      obtain ⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, -⟩ := e
      obtain ⟨⟨B, hB, hle⟩, -⟩ := (I.msgs a _ hm).2.1 e4
      rw [e1, e2] at hB; rw [e3] at hle
      have := hbold B hB; omega
    | _ => rfl
  have cntEq : ∀ (Y : Fin 3) (p : Msg → Bool), p (Msg.prepare pm) = false →
      (c1.inflight Y).countP p = (c.inflight Y).countP p := by
    intro Y p hp0
    rw [hinf Y]; exact countP_app_ite hp0
  -- the recoverer's new copy
  have hfresh : ¬ (G q i).rst (sint.Z nc.ballot) ∧ ∀ u, ¬ (G q i).prop (sint.Z nc.ballot) u := by
    have k : ((G q i).rst (sint.Z nc.ballot) ∨ ∃ u, (G q i).prop (sint.Z nc.ballot) u) → False := by
      intro hx
      obtain ⟨B, hB, hle⟩ := I0.ownMono _ a hown hx
      have := hbold B hB; omega
    exact ⟨fun h => k (Or.inl h), fun u h => k (Or.inr ⟨u, h⟩)⟩
  have newOk : CopyOk c1 G q i a nc :=
    { nonneg := Int.le_of_lt hnb
      ballotForm := Or.inr ⟨a, hown⟩
      vbalLe := by rw [hncvb]; have := hok.vbalLe; omega
      stOk := by rw [hncst]; exact hok.stOk
      noVotes := fun h => hok.noVotes (by rw [← hncst]; exact h)
      accVote := fun h => by rw [hncvb, hncva]; exact hok.accVote (by rw [← hncst]; exact h)
      committed := fun h => absurd (by rw [← hncst]; exact h) hnc
      rstVbal := fun h hv => by
        rw [hncvb] at hv ⊢; exact hok.rstVbal (by rw [← hncst]; exact h) hv
      eqCre := fun h hv ha => by
        rw [hncva]; rw [hncvb] at hv; exact hok.eqCre (by rw [← hncst]; exact h) hv ha
      leader0 := fun _ h0 _ => by rw [h0] at hnb; exact absurd hnb (by decide)
      ownFresh := fun _ _ => hfresh.2
      preparing := fun lb hlb _ _ _ => by
        rw [hnclb] at hlb; cases hlb
        exact ⟨riOk_rec hok I0.ainv hnc hlt hbalA hq hlead hnb, hfresh.1, hfresh.2,
          by simp [recLB], by simp [recLB]⟩
      eqTrack := fun ha he => by
        rw [hncst, hncvb]
        rcases hok.eqTrack ha he with h | h | h | ⟨b', h1, h2, h3⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr ⟨b', h1, by omega, h3⟩)) }
  refine ⟨G, { ids := ?_, inst := ?_, msgs := ?_, crtOwn := ?_, copyBelow := ?_,
               msgBelow := ?_, crtLen := ?_, leaderHas := ?_, prepMult := ?_ },
    fun q' j => evolve_bal (I.inst q' j).ainv (hBL q' j)⟩
  · intro x; rw [hid1 x]; exact I.ids x
  · intro q' j
    have Ij := I.inst q' j
    refine { ainv := ainv_bal Ij.ainv (hBL q' j), copies := ?_, noCopy := ?_, fastL := ?_,
             leaderCopy := ?_, ownMono := ?_, fresh := ?_ }
    · intro x cp hc
      rw [hcp1] at hc; split at hc
      · rename_i e; obtain ⟨e1, e2, e3⟩ := e; subst x; subst q'; subst j; cases hc
        exact newOk
      · exact copyOk_bal (hBL q' j) (Ij.copies x cp hc)
    · intro x hc
      rw [hcp1] at hc; split at hc
      · cases hc
      · exact Ij.noCopy x hc
    · intro v hv
      obtain ⟨cp, hcp, hcm⟩ := Ij.fastL v hv
      obtain ⟨cp', h1, h2⟩ := stat1 _ _ _ cp hcp
      exact ⟨cp', h1, by rw [h2]; exact hcm⟩
    · intro ⟨x, cp, hc⟩
      have hold : ∃ x cp, cpOf c x q' j = some cp := by
        rw [hcp1] at hc; split at hc
        · rename_i e; obtain ⟨rfl, rfl, rfl⟩ := e; exact ⟨_, _, hcpL⟩
        · exact ⟨x, cp, hc⟩
      obtain ⟨cp, hcp, hn⟩ := Ij.leaderCopy hold
      obtain ⟨cp', h1, h2⟩ := stat1 _ _ _ cp hcp
      exact ⟨cp', h1, by rw [h2]; exact hn⟩
    · intro b R hR hp'
      exact (hBL q' j).ge (Ij.ownMono b R hR hp')
    · intro hn
      refine Ij.fresh fun x => ?_
      have := hn x
      rw [hcp1] at this; split at this
      · cases this
      · exact this
  · intro d m hm
    rw [hinf d] at hm
    rcases List.mem_append.1 hm with hm | hm
    · refine msgOk_mono (fun q' j _ => hBL q' j) (fun q' j _ cp' hc => ?_) (fun x hx h1 => ?_)
        (I.msgs d m hm)
      · rw [hcp1 d q' j] at hc; split at hc
        · cases hc; exact Or.inr hnb
        · exact Or.inl hc
      · subst hx
        have e1 : (c1.inflight d).count (Msg.preAccept x : gNet.M) =
            (c1.inflight d).countP (fun y => y == (Msg.preAccept x : gNet.M)) := rfl
        have e2 : (c.inflight d).count (Msg.preAccept x : gNet.M) =
            (c.inflight d).countP (fun y => y == (Msg.preAccept x : gNet.M)) := rfl
        rw [e1, cntEq d _ rfl, ← e2, h1]
    · split at hm
      · cases hm
      · rename_i hda
        have hm' : m = Msg.prepare pm := List.mem_singleton.1 hm
        subst hm'
        refine ⟨hnb, a, hown, hid, Ne.symm hda, _, hbalA, Int.le_refl _⟩
  · intro j q'; rw [hcrt j, hcrt q']; exact I.crtOwn j q'
  · intro x q' j cp hc
    rw [hcrt (rowOf q')]
    rw [hcp1] at hc; split at hc
    · rename_i e; obtain ⟨rfl, rfl, rfl⟩ := e
      exact ⟨hrow, hi0, hLcrt⟩
    · exact I.copyBelow x q' j cp hc
  · intro d m q' j hm hj
    rw [hcrt (rowOf q')]
    rw [hinf d] at hm
    rcases List.mem_append.1 hm with hm | hm
    · exact I.msgBelow d m q' j hm hj
    · split at hm
      · cases hm
      · have hm' : m = Msg.prepare pm := List.mem_singleton.1 hm
        subst hm'
        simp only [msgInst, Option.some.injEq, Prod.mk.injEq] at hj
        obtain ⟨rfl, rfl⟩ := hj
        exact ⟨hrow, hi0, hLcrt⟩
  · intro x; rw [hcrtI x]; exact I.crtLen x
  · intro x j h0 h1
    rw [hcrt x] at h1
    obtain ⟨cp, hc, hn⟩ := I.leaderHas x j h0 h1
    obtain ⟨cp', h1, h2⟩ := stat1 _ _ _ cp hc
    exact ⟨cp', h1, by rw [h2]; exact hn⟩
  · intro R q' i' cp lb hc h1 h2 h3 h4
    rw [hcp1] at hc; split at hc
    · rename_i e; obtain ⟨e1, e2, e3⟩ := e; subst R; subst q'; subst i'; cases hc
      rw [hnclb] at h1; cases h1
      constructor
      · intro Y
        have e1 : (c1.inflight Y).countP (isPrepareAt q i nc.ballot) ≤ 1 := by
          have : (c.inflight Y).countP (isPrepareAt q i nc.ballot) = 0 :=
            List.countP_eq_zero.2 (fun m hm => by rw [noPrep Y m hm]; simp)
          rw [hinf Y]
          exact Nat.le_trans countP_app_ite_le (by rw [this]; exact Nat.le_refl _)
        have e2 : (c1.inflight a).countP (isOKReplyAt q i nc.ballot Y) = 0 := by
          rw [cntEq a _ rfl]
          exact List.countP_eq_zero.2 (fun m hm => by rw [noOK Y m hm]; simp)
        omega
      · intro ho; exfalso; revert ho; simp [recLB]
    · rename_i hne
      obtain ⟨k1, k2⟩ := I.prepMult R q' i' cp lb hc h1 h2 h3 h4
      have hnot : ∀ p, (p = isPrepareAt q' i' cp.ballot ∨ ∃ Y, p = isOKReplyAt q' i' cp.ballot Y) →
          p (Msg.prepare pm) = false := by
        intro p hp'
        rcases hp' with rfl | ⟨Y, rfl⟩
        · cases e : isPrepareAt q' i' cp.ballot (.prepare pm)
          · rfl
          simp only [isPrepareAt, Bool.and_eq_true, beq_iff_eq, pm] at e
          obtain ⟨⟨e1, e2⟩, e3⟩ := e
          rw [← e3] at h4
          have := own_uniq h4 hown
          exact absurd ⟨this, e1.symm, e2.symm⟩ hne
        · rfl
      have hR : ∀ Y, (c1.inflight R).countP (isOKReplyAt q' i' cp.ballot Y) =
          (c.inflight R).countP (isOKReplyAt q' i' cp.ballot Y) :=
        fun Y => cntEq _ _ (hnot _ (Or.inr ⟨Y, rfl⟩))
      refine ⟨fun Y => ?_, fun ho => ?_⟩
      · rw [cntEq _ _ (hnot _ (Or.inl rfl)), hR]; exact k1 Y
      · obtain ⟨k3, k4, k5⟩ := k2 ho
        exact ⟨k3, by rw [cntEq _ _ (hnot _ (Or.inl rfl))]; exact k4, by rw [hR]; exact k5⟩

theorem inv_recover {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {q0 i0 : w32} {s' : RState}
    {o : List Out} (I : CInv c G) (hp : Post c a (.recover q0 i0) s' o c1)
    (h : stepR a (c.st a) (.recover q0 i0) = .ok (s', o)) : StepInv c c1 G := by
  have h' : stepRecover (c.st a) q0 i0 = .ok (s', o) := h
  rcases stepRecover_cases h' with ⟨rfl, rfl⟩ | ⟨c0, hc0, hrow, hi0, hi1, hnc, hsg, rfl, hb⟩
  · exact inv_quiet' I hp ⟨rfl, rfl, rfl⟩ quietO_nil
  · exact recover_main I hp hc0 hrow hi0 hi1 hnc hsg hb

end Perennial.gryff.pureA
