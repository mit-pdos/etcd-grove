/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/StepAcceptReply.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1 (sub-unit A1d), internal: **`handleAcceptReply` keeps the agreement invariant**
(`inv_acceptReply_core`, behind `Inv.lean`'s `inv_acceptReply`).

`stepAcceptReply_shape`: a reply to a copy that is no longer ACCEPTED at the reply's ballot does
nothing; a NACK or a first OK only update the bookkeeping's counters (`inv_lb`: `CInv` reads only
`preparing`, `prepareOKs`, `recoveryInst`); a committing OK goes through `leaderCommit`
(`leaderCommit_shape`: the copy becomes COMMITTED with its value, the G11 re-proposal touches only
`proposeQ` and `lb`, Commits of the value go to the peers). The committed value is chosen: the OK
reply carries a vote `(b, v)` of a peer `Y` and the proposer's own vote `(b, v)` (`MsgOk`); the
proposer's copy is ACCEPTED at ballot `b`, its latest vote is at its vbal `≤ b`, so the vote at `b`
is its vbal's and both are for the one proposal at `b`.
-/
module

public import Dsverify.Proof.gryff.PureA.StepCommit

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.A1d

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA

/-! ## Broadcasts -/

theorem mapM_mem' {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → ∀ y ∈ r, ∃ a ∈ l, f a = some y
  | [], r, h => by simp at h; subst h; simp
  | a :: l, r, h => by
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      simp only [hfa] at h
      cases hl : l.mapM f with
      | none => simp [hl] at h
      | some bs =>
        simp only [hl, pure, Option.some.injEq] at h
        subst h
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨a, by simp, hfa⟩
        · obtain ⟨a', ha', h'⟩ := mapM_mem' hl y hy
          exact ⟨a', by simp [ha'], h'⟩

theorem bcast_mem {s : RState} {msg : Msg} {o : List Out} (h : bcast s msg = some o) :
    ∀ d m', Out.send d m' ∈ o → m' = msg := by
  intro d m' hm
  obtain ⟨q, -, hq⟩ := mapM_mem' h _ hm
  unfold sendPeer at hq; split at hq
  · cases hq
  · unfold sendTo at hq
    obtain ⟨d', -, e⟩ := Option.map_eq_some_iff.1 hq
    cases e; rfl

/-! ## Shapes -/

theorem setInst_over {s t : RState} {q i : w32} {x y : Copy}
    (h : t.inst = (s.setInst q i y).inst) : (t.setInst q i x).inst = (s.setInst q i x).inst := by
  funext q' i'
  simp only [setInst_inst, h]
  split <;> rfl

theorem leaderCommit_shape {s s' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (h : leaderCommit s q i c lb = .ok (s', o)) :
    ∃ cp, s'.inst = (s.setInst q i cp).inst ∧ s'.id = s.id ∧ s'.crtInstance = s.crtInstance ∧
      cp.status = St.COMMITTED ∧ cp.valA = c.valA ∧ cp.ballot = c.ballot ∧ cp.vbal = c.vbal ∧
      ∀ d m', Out.send d m' ∈ o →
        m' = .commit { replica := q, inst := i, cmds := c.cmds, seq := c.seq, deps := c.deps, base := c.base } := by
  unfold leaderCommit at h
  peel h
  · cases h
    obtain ⟨e1, e2, e3⟩ := updateCommitted_inst (by assumption)
    exact ⟨_, setInst_over e1, e2, e3, rfl, rfl, rfl, rfl, bcast_mem (by assumption)⟩
  · cases h
    obtain ⟨e1, e2, e3⟩ := updateCommitted_inst (by assumption)
    exact ⟨_, e1, e2, e3, rfl, rfl, rfl, rfl, bcast_mem (by assumption)⟩

theorem stepAcceptReply_shape {s s' : RState} {m : AcceptReplyM} {o : List Out}
    (h : stepAcceptReply s m = .ok (s', o)) :
    (s' = s ∧ o = []) ∨
    ∃ c lb, s.inst m.replica m.inst = some c ∧ c.ballot = m.ballot ∧ c.lb = some lb ∧
      ((o = [] ∧ ∃ lb', s' = s.setInst m.replica m.inst { c with lb := some lb' } ∧
          lb'.preparing = lb.preparing ∧ lb'.prepareOKs = lb.prepareOKs ∧
          lb'.recoveryInst = lb.recoveryInst ∧ lb'.preAcceptOKs = lb.preAcceptOKs) ∨
       (m.ok ≠ FALSE ∧ c.status = St.ACCEPTED ∧
          ∃ lb'', leaderCommit s m.replica m.inst c lb'' = .ok (s', o))) := by
  unfold stepAcceptReply at h
  cases hc : s.inst m.replica m.inst <;> simp only [hc] at h <;> peel h
  all_goals first
    | (cases h; exact Or.inl ⟨rfl, rfl⟩)
    | (cases h; refine Or.inr ⟨_, ‹LB›, rfl, Decidable.of_not_not (by assumption), (by assumption),
        Or.inl ⟨rfl, _, rfl, rfl, rfl, rfl, rfl⟩⟩; done)
    | exact Or.inr ⟨_, ‹LB›, rfl, Decidable.of_not_not (by assumption), (by assumption),
        Or.inr ⟨(by assumption), Decidable.of_not_not (by assumption), _, (by assumption)⟩⟩

/-! ## A bookkeeping update -/

/-- The copy's bookkeeping changes in fields `CInv` does not read: `CInv` is kept. -/
theorem inv_lb {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {e : Ev} {s' : RState} {o : List Out}
    {q0 i0 : w32} {cp : Copy} {lb lb' : LB} (I : CInv c G)
    (hst : c1.st = fun j => if j = a then s' else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv e) (c.inflight j) else c.inflight j) ++ sentTo gNet j o)
    (hs' : s' = (c.st a).setInst q0 i0 { cp with lb := some lb' })
    (hc : (c.st a).inst q0 i0 = some cp) (hl : cp.lb = some lb)
    (e1 : lb'.preparing = lb.preparing) (e2 : lb'.prepareOKs = lb.prepareOKs)
    (e3 : lb'.recoveryInst = lb.recoveryInst) (e4 : lb'.preAcceptOKs = lb.preAcceptOKs)
    (hbelow : rowOk q0 = true ∧ 0 ≤ sint.Z i0 ∧ sint.Z i0 < sint.Z ((c.st (rowOf q0)).crt q0))
    (hO : o = []) :
    CInv c1 G ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G q i) (balOf c1 q i) := by
  subst hs' hO
  have IO := I.inst q0 i0
  have hcpA : cpOf c1 a q0 i0 = some { cp with lb := some lb' } := by
    rw [cpOf_postA hst]; exact setInst_self _ _ _ _
  have hc' : cpOf c a q0 i0 = some cp := hc
  have hbal : balOf c1 q0 i0 = balOf c q0 i0 := by
    funext j
    by_cases hj : j = a
    · subst hj; rw [balOf_some hcpA, balOf_some hc']
    · simp only [balOf, cpOf_postN hst hj]
  have E0 : Evolve (rowOf q0) (G q0 i0) (balOf c q0 i0) (G q0 i0) (balOf c1 q0 i0) := by
    rw [hbal]; exact Evolve.refl IO.ainv
  have h0 := IO.copies a cp hc'
  have hNew : CopyOk c1 G q0 i0 a { cp with lb := some lb' } :=
    { h0 with
      leader0 := leader0_lb (cp := cp) h0 hl e4
      preparing := fun lb2 hl2 hp hn ho => by
        cases hl2
        rw [e1] at hp
        obtain ⟨k1, k2, k3, k4, k5⟩ := h0.preparing lb hl hp hn ho
        rw [hbal]
        exact ⟨by rw [e3]; exact k1, k2, k3, by rw [e2]; exact k4, by rw [e2]; exact k5⟩ }
  have hI0 : InstOk c1 G q0 i0 :=
    { ainv := by rw [hbal]; exact IO.ainv
      copies := fun j cp'' hc'' => by
        by_cases hj : j = a
        · subst hj; rw [hcpA] at hc''; cases hc''; exact hNew
        · rw [cpOf_postN hst hj] at hc''
          exact copyOk_narrow E0 (Narrow.refl _ _) (IO.copies j cp'' hc'')
      noCopy := fun j hc'' => by
        by_cases hj : j = a
        · subst hj; rw [hcpA] at hc''; cases hc''
        · rw [cpOf_postN hst hj] at hc''; exact IO.noCopy j hc''
      fastL := fun w hw => by
        obtain ⟨cpL, hL, hLc⟩ := IO.fastL w hw
        by_cases hLa : rowOf q0 = a
        · rw [hLa] at hL ⊢; rw [hc'] at hL; cases hL
          exact ⟨_, hcpA, hLc⟩
        · exact ⟨cpL, by rw [cpOf_postN hst hLa]; exact hL, hLc⟩
      leaderCopy := fun _ => by
        obtain ⟨cpL, hL, hne⟩ := IO.leaderCopy ⟨a, cp, hc'⟩
        by_cases hLa : rowOf q0 = a
        · rw [hLa] at hL ⊢; rw [hc'] at hL; cases hL
          exact ⟨_, hcpA, hne⟩
        · exact ⟨cpL, by rw [cpOf_postN hst hLa]; exact hL, hne⟩
      ownMono := fun b' R' hR' hp => by rw [hbal]; exact IO.ownMono b' R' hR' hp
      fresh := fun hn => absurd ((hn a).symm.trans hcpA) (by simp) }
  refine inv_frame I hst hinf rfl (fun q i hn => setInst_other _ _ hn) (fun _ _ _ => rfl) rfl
    (fun r => I.crtOwn a r) hbelow E0 (fun _ h => h) hI0 ?_ ?_ (fun d m h => by simp at h) rfl
    (fun cp0 h1 h2 => ⟨_, setInst_self _ _ _ _, by rw [hc] at h1; cases h1; exact h2⟩)
  · intro cp' h1 h2
    cases Option.some.inj (h1.symm.trans (setInst_self _ _ _ _)); exact h2 cp hc
  · intro cp' lb2 h1 h2 h3 h4 _
    cases Option.some.inj (h1.symm.trans (setInst_self _ _ _ _)); cases h2
    exact ⟨cp, lb, hc, hl, by rw [← e1]; exact h3, h4, rfl, e2.symm⟩

/-! ## The step -/

/-- **`handleAcceptReply`** keeps `CInv` (same history). -/
theorem inv_acceptReply_core {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : AcceptReplyM}
    {s' : RState} {o : List Out} (I : CInv c G)
    (hst : c1.st = fun j => if j = a then s' else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv (.msg (.acceptReply m))) (c.inflight j) else c.inflight j) ++
        sentTo gNet j o)
    (hm : Msg.acceptReply m ∈ c.inflight a) (h : stepAcceptReply (c.st a) m = .ok (s', o)) :
    ∃ G', CInv c1 G' ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i) := by
  have hmo : MsgOk c G a (.acceptReply m) := I.msgs a _ hm
  have hbelow := I.msgBelow a _ m.replica m.inst hm rfl
  rcases stepAcceptReply_shape h with ⟨rfl, rfl⟩ | ⟨c0, lb, hc0, hb0, hl0, hr⟩
  · exact ⟨G, inv_frame_same I hst hinf rfl rfl rfl (fun r => I.crtOwn a r) hbelow
      (fun d m h => by simp at h) rfl⟩
  rcases hr with ⟨rfl, lb', hs', e1, e2, e3, e4⟩ | ⟨hok, hst0, lb'', hlc⟩
  · exact ⟨G, inv_lb I hst hinf hs' hc0 hl0 e1 e2 e3 e4 hbelow rfl⟩
  -- the commit: the value is chosen
  have IO := I.inst m.replica m.inst
  have A := IO.ainv
  have hc0' : cpOf c a m.replica m.inst = some c0 := hc0
  have h0 := IO.copies a c0 hc0'
  obtain ⟨Y, hYa, v, hY, ha⟩ := hmo.1 hok
  obtain ⟨hacc, hle⟩ := h0.accVote hst0
  have hvb : sint.Z c0.vbal = sint.Z m.ballot := by
    have k1 := hle _ _ ha
    have k2 := h0.vbalLe
    rw [hb0] at k2
    omega
  have hv : v = c0.valA := by
    rw [hvb] at hacc
    exact A.prop_uniq _ _ _ (A.acc_prop _ _ _ ha) (A.acc_prop _ _ _ hacc)
  subst hv
  have hch : Chosen (G m.replica m.inst) c0.valA := Or.inr ⟨_, Y, a, hYa, hY, ha⟩
  obtain ⟨cp, e1, e2, e3, hcs, hval, hcb, hcv, hout⟩ := leaderCommit_shape hlc
  have hcrt : ∀ p, s'.crt p = (c.st a).crt p := fun p => by simp only [RState.crt, e3]
  refine ⟨G, inv_commit_copy (q0 := m.replica) (i0 := m.inst) (cp := cp) I hst hinf e2
    (fun q i hn => by rw [e1]; exact setInst_other _ _ hn)
    (by rw [e1]; exact setInst_self _ _ _ _) (hcrt _)
    (fun r => by rw [hcrt]; exact I.crtOwn a r) hbelow hcs (by rw [hval]; exact hch)
    (Or.inr ⟨c0, hc0', hcb, hcv⟩) ?_ (by rw [e3])⟩
  intro d m' hd
  rw [hout d m' hd]
  exact ⟨rfl, hch, fun q j hj => by cases hj; exact ⟨rfl, rfl⟩⟩

end Perennial.gryff.pureA.A1d
