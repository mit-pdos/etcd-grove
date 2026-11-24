/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/StepSim.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1, internal (A1a): **near-frame steps** keep `CInv` with the same history. A step whose copies
change only by COMMITTED → EXECUTED or in bookkeeping `CInv` does not read (`CopySim`: same value,
ballot, vbal, and the same `preparing`/`recoveryInst`/`prepareOKs`), which keeps the ids and
`crtInstance`, consumes at most one message and sends no EPaxos message (`QuietO`): `inv_sim`.
Used by `inv_exec`, `inv_executed`, `inv_executeOverwrite`.
-/
module

public import Dsverify.Proof.gryff.PureA.StepBase

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn

/-- The bookkeeping `CInv` reads. -/
def lbProj (l : LB) : Bool × Option RecoveryInstance × w64 × w64 :=
  (l.preparing, l.recoveryInst, l.prepareOKs, l.preAcceptOKs)

/-- `cp'` is `cp` up to COMMITTED → EXECUTED and bookkeeping `CInv` does not read. -/
structure CopySim (cp cp' : Copy) : Prop where
  valA : cp'.valA = cp.valA
  ballot : cp'.ballot = cp.ballot
  vbal : cp'.vbal = cp.vbal
  st : cp'.status = cp.status ∨ (cp.status = St.COMMITTED ∧ cp'.status = St.EXECUTED)
  lb : cp'.lb.map lbProj = cp.lb.map lbProj

theorem CopySim.refl (cp : Copy) : CopySim cp cp := ⟨rfl, rfl, rfl, Or.inl rfl, rfl⟩

/-- Option-lifted `CopySim` (old, new). -/
def OSim : Option Copy → Option Copy → Prop
  | none, none => True
  | some cp, some cp' => CopySim cp cp'
  | _, _ => False

theorem OSim.refl : ∀ o : Option Copy, OSim o o
  | none => trivial
  | some cp => CopySim.refl cp

theorem OSim.some_r {o : Option Copy} {cp' : Copy} (h : OSim o (some cp')) :
    ∃ cp, o = some cp ∧ CopySim cp cp' := by
  cases o with
  | none => exact h.elim
  | some cp => exact ⟨cp, rfl, h⟩

theorem OSim.none_r {o : Option Copy} (h : OSim o none) : o = none := by
  cases o with
  | none => rfl
  | some _ => exact h.elim

theorem OSim.none_l {o : Option Copy} (h : OSim none o) : o = none := by
  cases o with
  | none => rfl
  | some _ => exact h.elim

theorem OSim.some_l {o : Option Copy} {cp : Copy} (h : OSim (some cp) o) :
    ∃ cp', o = some cp' ∧ CopySim cp cp' := by
  cases o with
  | none => exact h.elim
  | some cp' => exact ⟨cp', rfl, h⟩

theorem OSim.bal {o o' : Option Copy} (h : OSim o o') :
    o'.map (fun cp => sint.Z cp.ballot) = o.map (fun cp => sint.Z cp.ballot) := by
  cases o <;> cases o'
  · rfl
  · exact h.elim
  · exact h.elim
  · simp only [Option.map_some, CopySim.ballot h]

section sim
variable {cp cp' : Copy}

theorem CopySim.st_eq (h : CopySim cp cp') (hn : cp'.status ≠ St.EXECUTED) :
    cp'.status = cp.status := by
  rcases h.st with e | ⟨-, e⟩
  · exact e
  · exact absurd e hn

theorem CopySim.committed_iff (h : CopySim cp cp') : isCommitted cp'.status ↔ isCommitted cp.status := by
  rcases h.st with e | ⟨e1, e2⟩
  · rw [e]
  · rw [e1, e2]; exact ⟨fun _ => Or.inl rfl, fun _ => Or.inr rfl⟩

theorem CopySim.lb_some (h : CopySim cp cp') {l' : LB} (hl : cp'.lb = some l') :
    ∃ l, cp.lb = some l ∧ l.preparing = l'.preparing ∧ l.recoveryInst = l'.recoveryInst ∧
      l.prepareOKs = l'.prepareOKs ∧ l.preAcceptOKs = l'.preAcceptOKs := by
  have e := h.lb
  rw [hl] at e
  cases hc : cp.lb with
  | none => rw [hc] at e; cases e
  | some l =>
    rw [hc] at e
    simp only [Option.map_some, Option.some.injEq, lbProj, Prod.mk.injEq] at e
    exact ⟨l, rfl, e.1.symm, e.2.1.symm, e.2.2.1.symm, e.2.2.2.symm⟩

theorem CopySim.st_of (h : CopySim cp cp') {x : w8} (e : cp.status = x) (hx : x ≠ St.COMMITTED) :
    cp'.status = x := by
  rcases h.st with e' | ⟨e1, -⟩
  · exact e'.trans e
  · exact absurd (e.symm.trans e1) hx

theorem st_ne_ex : St.NONE ≠ St.EXECUTED ∧ St.PREACCEPTED ≠ St.EXECUTED ∧
    St.PREACCEPTED_EQ ≠ St.EXECUTED ∧ St.ACCEPTED ≠ St.EXECUTED := by decide

theorem CopySim.pre_eq (h : CopySim cp cp') (hp : cp'.status = St.NONE ∨ isPre cp'.status) :
    cp'.status = cp.status := by
  apply h.st_eq; intro e
  rcases hp with hp | hp | hp <;> rw [hp] at e
  · exact st_ne_ex.1 e
  · exact st_ne_ex.2.1 e
  · exact st_ne_ex.2.2.1 e

end sim

theorem copyOk_sim {c c1 : Cfg gNet} {G : GG} {q i : w32} {a : Fin 3} {cp cp' : Copy}
    (hb : balOf c1 q i = balOf c q i) (hs : CopySim cp cp') (h : CopyOk c G q i a cp) :
    CopyOk c1 G q i a cp' := by
  have eb := hs.ballot
  have ev := hs.vbal
  have eva := hs.valA
  refine
    { nonneg := by rw [eb]; exact h.nonneg
      ballotForm := by rw [eb]; exact h.ballotForm
      vbalLe := by rw [eb, ev]; exact h.vbalLe
      stOk := ?_
      noVotes := fun hp => by rw [hs.pre_eq hp] at hp; exact h.noVotes hp
      accVote := fun hp => by
        rw [hs.st_eq (by rw [hp]; exact st_ne_ex.2.2.2)] at hp
        rw [ev, eva]; exact h.accVote hp
      committed := fun hp => by rw [eva]; exact h.committed (hs.committed_iff.1 hp)
      rstVbal := fun hp hv => by
        rw [hs.pre_eq (Or.inr hp)] at hp; rw [ev] at hv ⊢; exact h.rstVbal hp hv
      eqCre := fun hp hv ha => by
        rw [hs.pre_eq (Or.inr (Or.inr hp))] at hp; rw [ev] at hv; rw [eva]; exact h.eqCre hp hv ha
      leader0 := fun ha hb0 hp => by
        rw [hs.pre_eq (Or.inr (Or.inl hp))] at hp; rw [eb] at hb0; rw [eva]
        obtain ⟨k1, k2, k3, k4⟩ := h.leader0 ha hb0 hp
        refine ⟨k1, k2, k3, fun l' hl' => ?_⟩
        obtain ⟨l, hl0, -, -, -, e4⟩ := hs.lb_some hl'
        rw [← e4]; exact k4 l hl0
      ownFresh := fun hp ho => by
        rw [hs.pre_eq hp] at hp; rw [eb] at ho ⊢; exact h.ownFresh hp ho
      preparing := fun l' hl hpr hnc ho => by
        obtain ⟨l, hl0, e1, e2, e3, -⟩ := hs.lb_some hl
        rw [← e1] at hpr
        rw [hs.committed_iff] at hnc
        rw [eb] at ho ⊢
        rw [← e2, ← e3, hb]
        exact h.preparing l hl0 hpr hnc ho
      eqTrack := fun ha he => by
        rcases h.eqTrack ha he with e | e | ⟨e1, e2⟩ | e
        · left; exact hs.st_of e (by decide)
        · right; left; exact hs.committed_iff.2 e
        · right; right; left
          rw [ev]; exact ⟨hs.st_of e1 (by decide), e2⟩
        · right; right; right; rw [eb]; exact e }
  rcases h.stOk with e | (e | e) | e | e
  · exact Or.inl (hs.st_of e (by decide))
  · exact Or.inr (Or.inl (Or.inl (hs.st_of e (by decide))))
  · exact Or.inr (Or.inl (Or.inr (hs.st_of e (by decide))))
  · exact Or.inr (Or.inr (Or.inl (hs.st_of e (by decide))))
  · exact Or.inr (Or.inr (Or.inr (hs.committed_iff.2 e)))

theorem balOf_sim {c c1 : Cfg gNet} {q i : w32} (h : ∀ a, OSim (cpOf c a q i) (cpOf c1 a q i)) :
    balOf c1 q i = balOf c q i := by
  funext a; exact OSim.bal (h a)

theorem instOk_sim {c c1 : Cfg gNet} {G : GG} {q i : w32} (h : ∀ a, OSim (cpOf c a q i) (cpOf c1 a q i))
    (I : InstOk c G q i) : InstOk c1 G q i := by
  have hb := balOf_sim h
  exact
    { ainv := hb ▸ I.ainv
      copies := fun a cp' hc => by
        obtain ⟨cp, h0, hs⟩ := OSim.some_r (hc ▸ h a)
        exact copyOk_sim hb hs (I.copies a cp h0)
      noCopy := fun a hc => I.noCopy a (OSim.none_r (hc ▸ h a))
      fastL := fun v hv => by
        obtain ⟨cp, hc, hcm⟩ := I.fastL v hv
        obtain ⟨cp', hc', hs⟩ := OSim.some_l (hc ▸ h (rowOf q))
        exact ⟨cp', hc', hs.committed_iff.2 hcm⟩
      leaderCopy := fun ⟨a, cp', hc⟩ => by
        obtain ⟨cp, h0, -⟩ := OSim.some_r (hc ▸ h a)
        obtain ⟨cl, hcl, hn⟩ := I.leaderCopy ⟨a, cp, h0⟩
        obtain ⟨cl', hcl', hs⟩ := OSim.some_l (hcl ▸ h (rowOf q))
        refine ⟨cl', hcl', fun e => hn ?_⟩
        rw [← hs.pre_eq (Or.inl e)]; exact e
      ownMono := fun b R hR hp => by rw [hb]; exact I.ownMono b R hR hp
      fresh := fun hn => I.fresh fun a => OSim.none_r ((hn a) ▸ h a) }

theorem msgOk_sim {c c1 : Cfg gNet} {G : GG} {d : Fin 3} {m : Msg}
    (hcp : ∀ q j, msgInst m = some (q, j) → ∀ a, OSim (cpOf c a q j) (cpOf c1 a q j))
    (hcnt : ∀ x, m = .preAccept x → (c.inflight d).count (Msg.preAccept x : gNet.M) = 1 →
      (c1.inflight d).count (Msg.preAccept x : gNet.M) = 1)
    (h : MsgOk c G d m) : MsgOk c1 G d m := by
  cases m with
  | preAccept x =>
    have e := hcp _ _ rfl
    have ec := hcnt x rfl
    unfold MsgOk at h ⊢
    refine ⟨fun hb => ?_, h.2⟩
    obtain ⟨k1, k2, k3, k4, k5⟩ := h.1 hb
    refine ⟨k1, k2, k3, fun cp' hc => ?_, ec k5⟩
    obtain ⟨cp, h0, hs⟩ := OSim.some_r (hc ▸ e d)
    rw [hs.ballot]
    rcases k4 cp h0 with k | k | k
    · exact Or.inl k
    · exact Or.inr (Or.inl (hs.st_of k (by decide)))
    · exact Or.inr (Or.inr (hs.committed_iff.2 k))
  | prepare x =>
    have e := balOf_sim (hcp _ _ rfl)
    simp only [MsgOk, e] at h ⊢; exact h
  | prepareReply x =>
    have e := balOf_sim (hcp _ _ rfl)
    simp only [MsgOk, e] at h ⊢; exact h
  | _ => exact h

/-- The replica's state changes by `CopySim` copies only. -/
def SimFrame (s t : RState) : Prop :=
  t.id = s.id ∧ t.crtInstance = s.crtInstance ∧ ∀ q i, OSim (s.inst q i) (t.inst q i)

theorem SimFrame.of_frame {s t : RState} (h : Frame s t) : SimFrame s t :=
  ⟨h.1, h.2.2, fun q i => by rw [h.2.1]; exact OSim.refl _⟩

theorem SimFrame.trans {s t u : RState} (h1 : SimFrame s t) (h2 : SimFrame t u) (hf : Frame s t) :
    SimFrame s u :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun q i => by have := h2.2.2 q i; rwa [hf.2.1] at this⟩

theorem simFrame_setInst {s : RState} {q i : w32} {cp cp' : Copy} (hc : s.inst q i = some cp)
    (hs : CopySim cp cp') : SimFrame s (s.setInst q i cp') := by
  refine ⟨rfl, rfl, fun q' i' => ?_⟩
  rw [setInst_inst]
  split
  · rename_i e; obtain ⟨rfl, rfl⟩ := e; rw [hc]; exact hs
  · exact OSim.refl _

/-- **A near-frame step** keeps the invariant with the same history. -/
theorem inv_sim {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {e : Ev} {s' : RState} {o : List Out}
    (I : CInv c G) (hp : Post c a e s' o c1) (hf : SimFrame (c.st a) s') (ho : QuietO o) :
    StepInv c c1 G := by
  have hst : ∀ j : Fin 3, SimFrame (c.st j) (c1.st j) := fun j => by
    rw [hp.1]
    by_cases h : j = a
    · subst h; simp only [ite_true]; exact hf
    · simp only [h, ite_false]; exact ⟨rfl, rfl, fun _ _ => OSim.refl _⟩
  have hcp : ∀ a q i, OSim (cpOf c a q i) (cpOf c1 a q i) := fun a q i => (hst a).2.2 q i
  have hcrt : ∀ (j : Fin 3) q, (c1.st j).crt q = (c.st j).crt q := fun j q => by
    simp only [RState.crt, (hst j).2.1]
  have hinf := quiet_inflight hp ho
  have hmem : ∀ d m, m ∈ c1.inflight d → isEp m = true → m ∈ c.inflight d := fun d m hm he => by
    obtain ⟨l, hs, hl, hn⟩ := hinf d
    rw [hl] at hm
    rcases List.mem_append.1 hm with h | h
    · exact hs.subset h
    · rw [hn m h] at he; cases he
  have hcntle : ∀ d (p : Msg → Bool), (∀ m, isEp m = false → p m = false) →
      (c1.inflight d).countP p ≤ (c.inflight d).countP p := fun d p hpq => by
    obtain ⟨l, hs, hl, hn⟩ := hinf d
    rw [hl]; exact countP_quiet hs hn hpq
  refine ⟨G, { ids := ?_, inst := ?_, msgs := ?_, crtOwn := ?_, copyBelow := ?_,
               msgBelow := ?_, crtLen := ?_, leaderHas := ?_, prepMult := ?_ }, fun q i => ?_⟩
  · intro j; rw [(hst j).1]; exact I.ids j
  · intro q i; exact instOk_sim (fun a => hcp a q i) (I.inst q i)
  · intro d m hm
    cases hq : isEp m
    · exact msgOk_quiet hq
    · refine msgOk_sim (fun q j _ a => hcp a q j) (fun x hx h3 => ?_) (I.msgs d m (hmem d m hm hq))
      subst hx
      have h1 := hcntle d (fun y => y == (Msg.preAccept x : gNet.M)) (fun y hy => by
        cases y <;> simp_all [isEp])
      have h2 : 0 < (c1.inflight d).count (Msg.preAccept x : gNet.M) := List.count_pos_iff.2 hm
      have e1 : (c1.inflight d).count (Msg.preAccept x : gNet.M) =
          (c1.inflight d).countP (fun y => y == (Msg.preAccept x : gNet.M)) := rfl
      have e2 : (c.inflight d).count (Msg.preAccept x : gNet.M) =
          (c.inflight d).countP (fun y => y == (Msg.preAccept x : gNet.M)) := rfl
      omega
  · intro j q; rw [hcrt, hcrt]; exact I.crtOwn j q
  · intro j q i cp' hc
    obtain ⟨cp, h0, -⟩ := OSim.some_r (hc ▸ hcp j q i)
    rw [hcrt]; exact I.copyBelow j q i cp h0
  · intro d m q j hm hj
    rw [hcrt]
    have he : isEp m = true := by cases m <;> simp_all [msgInst, isEp]
    exact I.msgBelow d m q j (hmem d m hm he) hj
  · intro j; rw [(hst j).2.1]; exact I.crtLen j
  · intro q j h0 h1
    rw [hcrt] at h1
    obtain ⟨cp, hc, hn⟩ := I.leaderHas q j h0 h1
    obtain ⟨cp', hc', hs⟩ := OSim.some_l (hc ▸ hcp q _ j)
    exact ⟨cp', hc', fun e => hn (by rw [← hs.pre_eq (Or.inl e)]; exact e)⟩
  · intro R q i cp' l' hc h1 h2 h3 h4
    obtain ⟨cp, h0, hs⟩ := OSim.some_r (hc ▸ hcp R q i)
    obtain ⟨l, hl, e1, -, e3, -⟩ := hs.lb_some h1
    rw [hs.ballot] at h4 ⊢
    rw [← e3]
    obtain ⟨k1, k2⟩ := I.prepMult R q i cp l h0 hl (e1 ▸ h2) (fun x => h3 (hs.committed_iff.2 x)) h4
    have hP : ∀ m, isEp m = false → isPrepareAt q i cp.ballot m = false := fun m hm => by
      cases m <;> simp_all [isEp, isPrepareAt]
    have hR : ∀ Y m, isEp m = false → isOKReplyAt q i cp.ballot Y m = false := fun Y m hm => by
      cases m <;> simp_all [isEp, isOKReplyAt]
    refine ⟨fun Y => Nat.le_trans (Nat.add_le_add (hcntle Y _ hP) (hcntle R _ (hR Y))) (k1 Y),
      fun ho => ?_⟩
    obtain ⟨k3, k4, k5⟩ := k2 ho
    exact ⟨k3, Nat.le_zero.1 (k4 ▸ hcntle _ _ hP), Nat.le_zero.1 (k5 ▸ hcntle R _ (hR _))⟩
  · rw [balOf_sim (fun a => hcp a q i)]; exact Evolve.refl (I.inst q i).ainv

end Perennial.gryff.pureA
