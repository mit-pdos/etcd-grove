/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureT/Total.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A2 (totality): every step from a configuration satisfying the invariant: a message in flight
is handled (`.ok`), a free event of the system's shape is `.ok` or `disabled`; the invariant holds
in every reachable configuration.
-/
module

public import Dsverify.Proof.gryff.PureT.Propose
public import Dsverify.Proof.gryff.Pure.LinDefs

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.tot

open model kahn

/-- **A message's step** from states satisfying the invariant. -/
theorem msg_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (m : Msg)
    (hm : MInv (Pf st) st r m) :
    Ok (stepR r (st r) (.msg m)) (Post st r) := by
  cases m with
  | read1 m => exact stepRead1_ok st r hI m hm
  | read2 m => exact absurd hm id
  | read1Reply m => exact stepRead1Reply_ok st r hI m
  | read2Reply m => exact absurd hm id
  | write1 m => exact stepWrite1_ok st r hI m hm
  | write2 m => exact stepWrite2_ok st r hI m hm
  | write1Reply m => exact stepWrite1Reply_ok st r hI m hm
  | write2Reply m => exact stepWrite2Reply_ok st r hI m hm
  | preAccept m => exact stepPreAccept_ok st r hI m hm
  | preAcceptReply m => exact stepPreAcceptReply_ok st r hI m hm
  | preAcceptOK m => exact stepPreAcceptOK_ok st r hI m hm
  | accept m => exact stepAccept_ok st r hI m hm
  | acceptReply m => exact stepAcceptReply_ok st r hI m hm
  | commit m => exact stepCommit_ok st r hI m hm
  | prepare m => exact stepPrepare_ok st r hI m hm
  | prepareReply m => exact stepPrepareReply_ok st r hI m hm
  | executed m =>
    simp only [MInv] at hm
    exact handleExecuted_ok hI (Good.refl hI) (hI r).id m hm.1 hm.2.1
  | executeOverwrite m => exact stepExecuteOverwrite_ok st r hI m hm

/-- A client request's shape (`Ev.Producible` of `Pure/Totality.lean`, restated). -/
def ReqShape (k : w64) (d : Dep) (cid : w32) : Prop := k = 0 ∧ sint.Z d.key < 0 ∧ 0 ≤ sint.Z cid

theorem ReqShape.guard {k : w64} {d : Dep} {cid : w32} (h : ReqShape k d cid) :
    (k == 0 && slt d.key 0 && sge cid 0) = true := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [h1, slt, sge, sle, h2, h3]

theorem ReqShape.of_guard {k : w64} {d : Dep} {cid : w32}
    (h : (k == 0 && slt d.key 0 && sge cid 0) = true) : ReqShape k d cid := by
  simp only [Bool.and_eq_true, beq_iff_eq, slt, sge, sle, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- A client request's step: `never` off the system's shape, `disabled` off the guard, else
`.ok` (with the postcondition). -/
theorem req_cases (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st)
    (hpq : (st r).proposeQ.length ≤ (st r).nReqs) (e : Ev) {rid cid : w32} {k : w64} {d : Dep}
    (he : e = .read rid cid k d ∨ (∃ v, e = .write rid cid k v d) ∨
      (∃ oldV newV, e = .rmw rid cid k d oldV newV)) :
    (¬ ReqShape k d cid ∧ stepR r (st r) e = .error .never) ∨
    (ReqShape k d cid ∧ ¬ ((st r).nReqs < 24 ∧ (cid, rid) ∉ (st r).used) ∧
      stepR r (st r) e = .error .disabled) ∨
    (ReqShape k d cid ∧ (st r).nReqs < 24 ∧ (cid, rid) ∉ (st r).used ∧
      Ok (stepR r (st r) e) (Post st r)) := by
  by_cases hs : ReqShape k d cid
  · have hg := hs.guard
    by_cases hb : (st r).nReqs < 24 ∧ (cid, rid) ∉ (st r).used
    · right; right
      obtain ⟨h1, h2, h3⟩ := hs
      have hk := h1
      have hd : slt d.key 0 = true := by simpa [slt] using h2
      have hc : sge cid 0 = true := by simpa [sge, sle] using h3
      refine ⟨⟨h1, h2, h3⟩, hb.1, hb.2, ?_⟩
      rcases he with rfl | ⟨v, rfl⟩ | ⟨oldV, newV, rfl⟩
      · exact stepClientRead_ok st r hI rid cid k d hk hd hc hb.1 hb.2
      · exact stepClientWrite_ok st r hI rid cid k v d hk hd hc hb.1 hb.2
      · exact stepClientRMW_ok st r hI rid cid k d oldV newV hk hd hc hb.1 hb.2 hpq
    · right; left
      refine ⟨hs, hb, ?_⟩
      by_cases hn : (st r).nReqs < 24
      · have hu : (cid, rid) ∈ (st r).used := Classical.byContradiction fun h => hb ⟨hn, h⟩
        have hn' : ¬ (24 ≤ (st r).nReqs) := by omega
        rcases he with rfl | ⟨v, rfl⟩ | ⟨oldV, newV, rfl⟩
        · tsimp [stepR, stepClientRead, hg, hn', hu]; rfl
        · tsimp [stepR, stepClientWrite, hg, hn', hu]; rfl
        · tsimp [stepR, stepClientRMW, hg, hn', hu]; rfl
      · have hn' : 24 ≤ (st r).nReqs := by omega
        rcases he with rfl | ⟨v, rfl⟩ | ⟨oldV, newV, rfl⟩
        · tsimp [stepR, stepClientRead, hg, hn']; rfl
        · tsimp [stepR, stepClientWrite, hg, hn']; rfl
        · tsimp [stepR, stepClientRMW, hg, hn']; rfl
  · left
    refine ⟨hs, ?_⟩
    have hg : (k == 0 && slt d.key 0 && sge cid 0) = false := by
      cases h : (k == 0 && slt d.key 0 && sge cid 0)
      · rfl
      · exact absurd (ReqShape.of_guard h) hs
    rcases he with rfl | ⟨v, rfl⟩ | ⟨oldV, newV, rfl⟩
    · tsimp [stepR, stepClientRead, hg]; rfl
    · tsimp [stepR, stepClientWrite, hg]; rfl
    · tsimp [stepR, stepClientRMW, hg]; rfl

theorem recover_cases (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (q i : w32) :
    stepR r (st r) (.recover q i) = .error .disabled ∨ Ok (stepR r (st r) (.recover q i)) (Post st r) := by
  cases hg : (rowOk q && sle 0 i && slt i ((st r).crt q))
  · left; tsimp [stepR, stepRecover, hg]; rfl
  · right; exact stepRecover_ok st r hI q i hg

theorem exec_cases (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (q i : w32) :
    stepR r (st r) (.exec q i) = .error .disabled ∨ Ok (stepR r (st r) (.exec q i)) (Post st r) := by
  cases hb : inBox q i
  · left; tsimp [stepR, stepExec, hb]; rfl
  · cases hc : (st r).inst q i with
    | none => left; tsimp [stepR, stepExec, hb, hc]; rfl
    | some c =>
      by_cases hs : c.status = St.COMMITTED
      · by_cases hg : execGuard (st r) (sint.Z q, sint.Z i)
        · right; exact stepExec_ok st r hI q i c hb hc hs hg
        · left; tsimp [stepR, stepExec, hb, hc, hs, hg]; rfl
      · left; tsimp [stepR, stepExec, hb, hc, hs]; rfl

/-- Any step's postcondition, from the invariant. -/
theorem step_post (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st)
    (hpq : (st r).proposeQ.length ≤ (st r).nReqs) (e : Ev)
    (hm : ∀ m, e.recv = some m → MInv (Pf st) st r m) {res : RState × List Out}
    (h : stepR r (st r) e = .ok res) : Post st r res := by
  cases e with
  | msg m =>
    exact (msg_ok st r hI m (hm m rfl)).post h
  | read rid cid k d =>
    rcases req_cases st r hI hpq (.read rid cid k d) (Or.inl rfl) with ⟨-, h'⟩ | ⟨-, -, h'⟩ | ⟨-, -, -, h'⟩
    · rw [h'] at h; cases h
    · rw [h'] at h; cases h
    · exact h'.post h
  | write rid cid k v d =>
    rcases req_cases st r hI hpq (.write rid cid k v d) (Or.inr (Or.inl ⟨v, rfl⟩)) with
      ⟨-, h'⟩ | ⟨-, -, h'⟩ | ⟨-, -, -, h'⟩
    · rw [h'] at h; cases h
    · rw [h'] at h; cases h
    · exact h'.post h
  | rmw rid cid k d oldV newV =>
    rcases req_cases st r hI hpq (.rmw rid cid k d oldV newV) (Or.inr (Or.inr ⟨oldV, newV, rfl⟩)) with
      ⟨-, h'⟩ | ⟨-, -, h'⟩ | ⟨-, -, -, h'⟩
    · rw [h'] at h; cases h
    · rw [h'] at h; cases h
    · exact h'.post h
  | forceWrite => exact (stepForceWrite_ok st r hI).post h
  | recover q i =>
    rcases recover_cases st r hI q i with h' | h'
    · rw [h'] at h; cases h
    · exact h'.post h
  | exec q i =>
    rcases exec_cases st r hI q i with h' | h'
    · rw [h'] at h; cases h
    · exact h'.post h

theorem grun_snoc {c0 c2 : Cfg gNet} {l : List Label} {i : Fin 3} {e : Ev}
    (h : GRun c0 (l ++ [(i, e)]) c2) : ∃ c1 x, GRun c0 l c1 ∧ GStep c1 i e c2 x := by
  induction l generalizing c0 with
  | nil =>
    cases h with
    | cons hs hr => cases hr; exact ⟨c0, _, GRun.nil c0, hs⟩
  | cons a l ih =>
    cases h with
    | cons hs hr =>
      obtain ⟨c1, x, h1, h2⟩ := ih hr
      exact ⟨c1, x, GRun.cons hs h1, h2⟩

theorem grun_append {c0 c1 c2 : Cfg gNet} {l : List Label} {i : Fin 3} {e : Ev} {x : List Ext}
    (h : GRun c0 l c1) (hs : GStep c1 i e c2 x) : GRun c0 (l ++ [(i, e)]) c2 := by
  induction h with
  | nil c => exact GRun.cons hs (GRun.nil _)
  | cons hs' _ ih => exact GRun.cons hs' (ih hs)

/-- **The invariant holds in every reachable configuration.** -/
theorem inv_reach_n : ∀ (n : Nat) (l : List Label) {c : Cfg gNet}, l.length = n →
    GRun (Cfg.init gNet) l c → InvC c := by
  intro n
  induction n with
  | zero => intro l c hl h; have : l = [] := List.eq_nil_of_length_eq_zero hl; subst this; cases h; exact invC_init
  | succ n ih =>
    intro l c hl h
    have hne : l ≠ [] := by intro h'; subst h'; simp at hl
    have hdl := List.dropLast_concat_getLast hne
    generalize l.getLast hne = x at hdl
    obtain ⟨i, e⟩ := x
    rw [← hdl] at h
    have hlen : (l.dropLast).length = n := by simp [List.length_dropLast, hl]
    obtain ⟨c1, xs, h1, h2⟩ := grun_snoc h
    have ih := fun {c} => ih l.dropLast (c := c) hlen
    have hI := ih h1
    have hpq : (c1.st i).proposeQ.length ≤ (c1.st i).nReqs := by
      obtain ⟨o, ho⟩ := grun_state h1 i
      exact (pureP.runP_Q ho).len
    refine invC_step hI h2 (fun s' o hst => step_post c1.st i hI.1 hpq e ?_ hst)
    intro m hm
    obtain ⟨-, -, -, hrecv, -⟩ := h2
    have hin : m ∈ c1.inflight i := hrecv m hm
    exact hI.2 i m hin

theorem inv_reach {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) : InvC c :=
  inv_reach_n l.length l rfl h

/-! ## Totality -/

theorem total_msg' {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (r : Fin 3)
    (m : Msg) (hm : m ∈ c.inflight r) : ∃ s' o, stepR r (c.st r) (.msg m) = .ok (s', o) := by
  have hI := inv_reach h
  obtain ⟨⟨s', o⟩, he, -⟩ := msg_ok c.st r hI.1 m (hI.2 r m hm)
  exact ⟨s', o, he⟩

theorem total_free' {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (r : Fin 3)
    (e : Ev) (he : e.recv = none)
    (hp : ∀ rid cid k d, (e = .read rid cid k d ∨ (∃ v, e = .write rid cid k v d) ∨
      (∃ oldV newV, e = .rmw rid cid k d oldV newV)) → ReqShape k d cid) :
    (∃ s' o, stepR r (c.st r) e = .ok (s', o)) ∨ stepR r (c.st r) e = .error .disabled := by
  have hI := (inv_reach h).1
  have hpq : (c.st r).proposeQ.length ≤ (c.st r).nReqs := by
    obtain ⟨o, ho⟩ := grun_state h r
    exact (pureP.runP_Q ho).len
  have hok : ∀ {x : StepRes}, Ok x (Post c.st r) → ∃ s' o, x = .ok (s', o) := by
    intro x hx; obtain ⟨⟨s', o⟩, h1, -⟩ := hx; exact ⟨s', o, h1⟩
  have hreq : ∀ rid cid k d, (e = .read rid cid k d ∨ (∃ v, e = .write rid cid k v d) ∨
      (∃ oldV newV, e = .rmw rid cid k d oldV newV)) →
      (∃ s' o, stepR r (c.st r) e = .ok (s', o)) ∨ stepR r (c.st r) e = .error .disabled := by
    intro rid cid k d hk
    rcases req_cases c.st r hI hpq e hk with ⟨hs, -⟩ | ⟨-, -, h'⟩ | ⟨-, -, -, h'⟩
    · exact absurd (hp rid cid k d hk) hs
    · exact Or.inr h'
    · exact Or.inl (hok h')
  cases e with
  | msg m => cases he
  | read rid cid k d => exact hreq rid cid k d (Or.inl rfl)
  | write rid cid k v d => exact hreq rid cid k d (Or.inr (Or.inl ⟨v, rfl⟩))
  | rmw rid cid k d oldV newV => exact hreq rid cid k d (Or.inr (Or.inr ⟨oldV, newV, rfl⟩))
  | forceWrite => exact Or.inl ⟨_, _, rfl⟩
  | recover q i =>
    rcases recover_cases c.st r hI q i with h' | h'
    · exact Or.inr h'
    · exact Or.inl (hok h')
  | exec q i =>
    rcases exec_cases c.st r hI q i with h' | h'
    · exact Or.inr h'
    · exact Or.inl (hok h')

/-! ## Not `disabled` past the guards (any state) -/

theorem bind_ne_dis {α β : Type} {x : Except Fail α} {f : α → Except Fail β}
    (hx : x ≠ .error .disabled) (hf : ∀ a, f a ≠ .error .disabled) : (x >>= f) ≠ .error .disabled := by
  cases x with
  | error e => cases e <;> first | exact absurd rfl hx | (intro h; cases h)
  | ok a => exact hf a

theorem forIn_ne_dis {α β : Type} (l : List α) (init : β) (f : α → β → Except Fail (ForInStep β))
    (hf : ∀ a b, f a b ≠ .error .disabled) : forIn l init f ≠ .error .disabled := by
  induction l generalizing init with
  | nil => intro h; cases h
  | cons a l ih =>
    rw [List.forIn_cons]
    refine bind_ne_dis (hf a init) (fun r => ?_)
    cases r with
    | done b => intro h; cases h
    | yield b => exact ih b

/-- Closes `x ≠ .error .disabled` for a computation without `disabled` (splitting its branches). -/
macro "nodis" : tactic => `(tactic| (repeat' split) <;> (intro h; cases h))

theorem startPhase1_ne_dis (S : RState) (q i b : w32) (ps : List Proposal) (cmds : List Cmd) :
    startPhase1 S q i b ps cmds ≠ .error .disabled := by
  unfold startPhase1
  tsimp []
  nodis

theorem stepReq_ne_disabled' (k : Fin 3) (s : RState) (e : Ev) {cid rid : w32}
    {i : dsverify_lab.harness.RegInput w64} (hr : e.clientReq = some (cid, rid, i))
    (hu : (cid, rid) ∉ s.used) (hb : s.nReqs < 24) : stepR k s e ≠ .error .disabled := by
  have hb' : ¬ (24 ≤ s.nReqs) := by omega
  cases e with
  | read rid' cid' kk d =>
    simp only [Ev.clientReq, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, -⟩ := hr
    tsimp [stepR, stepClientRead, hu, hb']
    split
    · intro h; cases h
    · refine bind_ne_dis (forIn_ne_dis _ _ _ ?_) (fun a => ?_)
      · intro a b; nodis
      · nodis
  | write rid' cid' kk v d =>
    simp only [Ev.clientReq, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, -⟩ := hr
    tsimp [stepR, stepClientWrite, hu, hb']
    nodis
  | rmw rid' cid' kk d oldV newV =>
    simp only [Ev.clientReq, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, -⟩ := hr
    tsimp [stepR, stepClientRMW, hu, hb', handlePropose]
    repeat' split
    all_goals first
      | (intro h; cases h; done)
      | (unfold handleProposeBody; exact startPhase1_ne_dis _ _ _ _ _ _)
  | _ => simp [Ev.clientReq] at hr

theorem stepRecover_ne_disabled' (k : Fin 3) (s : RState) (q i : w32) (hq : rowOk q = true)
    (h0 : 0 ≤ sint.Z i) (hc : sint.Z i < sint.Z (s.crt q)) :
    stepR k s (.recover q i) ≠ .error .disabled := by
  have hg : (rowOk q && sle 0 i && slt i (s.crt q)) = true := by
    simp [hq, sle, slt, h0, hc]
  tsimp [stepR, stepRecover, hg]
  nodis

theorem stepExec_ne_disabled' (k : Fin 3) (s : RState) (q i : w32) (c : Copy)
    (hb : inBox q i = true) (hc : s.inst q i = some c) (hs : c.status = St.COMMITTED)
    (hg : execGuard s (sint.Z q, sint.Z i)) :
    stepR k s (.exec q i) ≠ .error .disabled := by
  tsimp [stepR, stepExec, hb, hc, hs, hg]
  nodis

end Perennial.gryff.pure.tot
