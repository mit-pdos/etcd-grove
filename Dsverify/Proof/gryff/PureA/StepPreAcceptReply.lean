/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/StepPreAcceptReply.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1c, internal: **`handlePreAcceptReply` and `handlePreAcceptOK` keep the agreement invariant**
(`inv_preAcceptReply_core`, `inv_preAcceptOK_core`, used by `Inv.lean`).

Three shapes of the proposer `a`'s step on its PREACCEPTED copy `cp` of `(q, i)` at ballot `b`:
* `inv_fast`: the fast commit (ballot 0, `a` the leader): the history gets `fast v` for the copy's
  value `v`, the creation value (`leader0`), with an unchanged pre-accept (`MsgOk` of the
  PreAcceptOK, or G41's equality-based reply clause);
* `inv_acceptOwn`: the slow path, a proposal `(b, v)` accepted by `a` (`Gh.addProp`): fresh
  (`leader0` at ballot 0, `ownFresh` at `a`'s ballot), safe (nothing below 0; a restart at `b` is
  `SafeAll`);
* `inv_keepPre`: the copy stays PREACCEPTED (a NACK; an OK not reaching a quorum, impossible at
  ballot 0 by `leader0`'s count): `CInv` reads no more of it.
-/
module

public import Dsverify.Proof.gryff.PureA.StepPreAcceptReplyCases
public import Dsverify.Proof.gryff.PureA.StepAcceptReply
public import Dsverify.Proof.gryff.PureA.StepHelp

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.SPA

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn

/-- The history with a fast commit of `v`. -/
def addFast (g : Gh Val) (v : Val) : Gh Val := { g with fast := fun w => g.fast w ∨ w = v }

theorem ainv_fastOnly {g : Gh Val} {bal bal' : Fin 3 → Option Int} {L : Fin 3} {f : Val → Prop}
    (I : AInv g bal L) (E : Evolve L g bal { g with fast := f } bal') :
    AInv { g with fast := f } bal' L where
  prop_uniq := I.prop_uniq
  acc_prop := I.acc_prop
  prop_nonneg := I.prop_nonneg
  prop_safe b v h := safeAt_evolve E (I.prop_safe b v h)
  rst_safe b h := safeAll_evolve E (I.rst_safe b h)
  cre_uniq := I.cre_uniq
  fast_cre := E.fast_cre
  fast_eq := E.fast_eq
  fast_noprop := E.fast_noprop

theorem st_facts : St.COMMITTED ≠ St.NONE ∧ St.COMMITTED ≠ St.PREACCEPTED ∧
    St.COMMITTED ≠ St.PREACCEPTED_EQ ∧ St.COMMITTED ≠ St.ACCEPTED ∧
    St.ACCEPTED ≠ St.NONE ∧ St.ACCEPTED ≠ St.PREACCEPTED ∧ St.ACCEPTED ≠ St.PREACCEPTED_EQ ∧
    St.ACCEPTED ≠ St.COMMITTED ∧ St.ACCEPTED ≠ St.EXECUTED ∧ St.PREACCEPTED ≠ St.COMMITTED ∧
    St.PREACCEPTED ≠ St.EXECUTED := by decide

theorem com_notPre' {x : w8} (h : x = St.COMMITTED) : ¬ (x = St.NONE ∨ isPre x) := by
  subst h; rintro (h | h | h)
  · exact st_facts.1 h
  · exact st_facts.2.1 h
  · exact st_facts.2.2.1 h

theorem acc_notPre' {x : w8} (h : x = St.ACCEPTED) : ¬ (x = St.NONE ∨ isPre x) := by
  subst h; rintro (h | h | h)
  · exact st_facts.2.2.2.2.1 h
  · exact st_facts.2.2.2.2.2.1 h
  · exact st_facts.2.2.2.2.2.2.1 h

theorem acc_notCom' {x : w8} (h : x = St.ACCEPTED) : ¬ isCommitted x := by
  subst h; rintro (h | h)
  · exact st_facts.2.2.2.2.2.2.2.1 h
  · exact st_facts.2.2.2.2.2.2.2.2.1 h

theorem pre_notCom {x : w8} (h : x = St.PREACCEPTED) : ¬ isCommitted x := by
  subst h; rintro (h | h)
  · exact st_facts.2.2.2.2.2.2.2.2.2.1 h
  · exact st_facts.2.2.2.2.2.2.2.2.2.2 h

theorem z0_iff {x : w32} (h : sint.Z x = 0) : x = 0 := by
  apply BitVec.eq_of_toInt_eq; simpa [sint.Z] using h

/-! ## The slow path: a proposal accepted by its proposer -/

set_option maxHeartbeats 1000000 in
/-- Proposer `a`'s PREACCEPTED copy `cp` of `(q, i)` at ballot `b` becomes ACCEPTED at `b` with
value `c'.valA`, and the Accepts go to the peers. -/
theorem inv_acceptOwn {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {q i : w32} {cp c' : Copy}
    {m0 : Msg} {o : List Out} (I : CInv c G)
    (hst : c1.st = fun j => if j = a then (c.st a).setInst q i c' else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv (.msg m0)) (c.inflight j) else c.inflight j) ++
        sentTo gNet j o)
    (hc : cpOf c a q i = some cp) (hpre : cp.status = St.PREACCEPTED)
    (hc'st : c'.status = St.ACCEPTED) (hc'b : c'.ballot = cp.ballot) (hc'v : c'.vbal = cp.ballot)
    (hprepF : ∀ lb, c'.lb = some lb → lb.preparing = true → ¬ Own (sint.Z cp.ballot) a)
    (hown : (cp.ballot = 0 ∧ a = rowOf q) ∨ Own (sint.Z cp.ballot) a)
    (hfresh : ∀ u, ¬ (G q i).prop (sint.Z cp.ballot) u)
    (hsafe : SafeAt (G q i) (balOf c q i) (rowOf q) (sint.Z cp.ballot) c'.valA)
    (hfast : sint.Z cp.ballot = 0 → ∀ v, ¬ (G q i).fast v)
    (ho : bcastAccept ((c.st a).setInst q i c') q i cp.ballot c'.cmds c'.seq c'.deps c'.base = some o) :
    ∃ G', CInv c1 G' ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i) := by
  have hbelow := I.copyBelow a q i cp hc
  have hC := (I.inst q i).copies a cp hc
  have hcpA : cpOf c1 a q i = some c' := by rw [cpOf_postA hst]; exact setInst_self _ _ _ _
  have S : Step1 c c1 a q i m0 o :=
    step1_of (e := .msg m0) rfl hst hinf rfl (fun q' i' h => setInst_other _ _ h) rfl rfl
      (fun r => I.crtOwn a r)
  have hbal : balOf c1 q i = balOf c q i := by
    funext j
    by_cases hj : j = a
    · subst hj; rw [balOf_some hcpA, balOf_some hc, hc'b]
    · simp only [balOf, cpOf_postN hst hj]
  have hb0 : 0 ≤ sint.Z cp.ballot := hC.nonneg
  obtain ⟨AI, E⟩ := ainv_addProp (R := a) (I.inst q i).ainv hfresh hb0 (balOf_some hc) hsafe hfast
  have E0 : Evolve (rowOf q) (G q i) (balOf c q i) ((G q i).addProp (sint.Z cp.ballot) c'.valA a)
      (balOf c1 q i) := by rw [hbal]; exact E
  have hown' : ∀ b, (b = sint.Z cp.ballot) → ((b = 0 ∧ a = rowOf q) ∨ Own b a) := by
    intro b hb; subst hb
    rcases hown with ⟨h0, h1⟩ | h
    · exact Or.inl ⟨by rw [h0, z0], h1⟩
    · exact Or.inr h
  have GO : GOnly a (rowOf q) (G q i) ((G q i).addProp (sint.Z cp.ballot) c'.valA a) :=
    ⟨fun y b u h hn => h.elim (fun h' => absurd h' hn) (fun h' => h'.1),
     fun b u h hn => h.elim (fun h' => absurd h' hn) (fun h' => hown' b h'.1),
     fun _ h => h, fun _ h => h, fun _ h hn => absurd h hn, fun _ h hn => absurd h hn⟩
  obtain ⟨G', hG'at, hG'ne⟩ : ∃ G' : GG,
      G' q i = (G q i).addProp (sint.Z cp.ballot) c'.valA a ∧
      ∀ q' i', ¬ (q' = q ∧ i' = i) → G' q' i' = G q' i' :=
    ⟨ggSet G _ _ _, ggSet_at _ _ _ _, fun _ _ h => ggSet_ne _ _ h⟩
  have hnewC : CopyOk c1 (fun _ _ => (G q i).addProp (sint.Z cp.ballot) c'.valA a) q i a c' :=
    { nonneg := by rw [hc'b]; exact hb0
      ballotForm := by rw [hc'b]; exact hC.ballotForm
      vbalLe := by rw [hc'b, hc'v]; exact Int.le_refl _
      stOk := Or.inr (Or.inr (Or.inl hc'st))
      noVotes := fun h => absurd h (acc_notPre' hc'st)
      accVote := fun _ => by
        refine ⟨Or.inr ⟨rfl, by rw [hc'v], rfl⟩, fun b u hu => ?_⟩
        rcases hu with hu | ⟨-, rfl, -⟩
        · exact absurd hu (hC.noVotes (Or.inr (Or.inl hpre)) b u)
        · rw [hc'v]; exact Int.le_refl _
      committed := fun h => absurd h (acc_notCom' hc'st)
      rstVbal := fun h => absurd (Or.inr h) (acc_notPre' hc'st)
      eqCre := fun h => absurd (Or.inr (Or.inr h)) (acc_notPre' hc'st)
      leader0 := fun _ _ h => absurd (Or.inr (Or.inl h)) (acc_notPre' hc'st)
      ownFresh := fun h => absurd h (acc_notPre' hc'st)
      preparing := fun lb hl hp _ ho => absurd (by rw [← hc'b]; exact ho) (hprepF lb hl hp)
      eqTrack := fun _ _ => Or.inl hc'st }
  have hI : InstOk c1 (fun _ _ => (G q i).addProp (sint.Z cp.ballot) c'.valA a) q i :=
    { ainv := by rw [hbal]; exact AI
      copies := by
        intro y cp'' hc''
        by_cases hy : y = a
        · subst hy; rw [hcpA] at hc''; cases hc''; exact hnewC
        · rw [cpOf_postN hst hy] at hc''
          exact copyOk_keep ((I.inst _ _).copies y cp'' hc'') E0 GO hy
      noCopy := by
        intro y hy
        have hya : y ≠ a := by rintro rfl; rw [hcpA] at hy; cases hy
        rw [cpOf_postN hst hya] at hy
        obtain ⟨k1, k2⟩ := (I.inst _ _).noCopy y hy
        exact ⟨fun b u hu => hu.elim (k1 b u) (fun h => hya h.1), k2⟩
      fastL := by
        intro v hv
        obtain ⟨cpL, hL, hcom⟩ := (I.inst _ _).fastL v hv
        by_cases hLa : rowOf q = a
        · exfalso; rw [hLa, hc] at hL; cases hL; exact pre_notCom hpre hcom
        · exact ⟨cpL, by rw [cpOf_postN hst hLa]; exact hL, hcom⟩
      leaderCopy := by
        intro _
        by_cases hLa : rowOf q = a
        · rw [hLa]; exact ⟨c', hcpA, fun h => st_facts.2.2.2.2.1 (hc'st.symm.trans h)⟩
        · obtain ⟨cpL, hL, hne⟩ := (I.inst _ _).leaderCopy ⟨a, cp, hc⟩
          exact ⟨cpL, by rw [cpOf_postN hst hLa]; exact hL, hne⟩
      ownMono := by
        intro b R hR hp
        rw [hbal]
        rcases hp with hp | ⟨u, hu | ⟨rfl, -⟩⟩
        · exact (I.inst _ _).ownMono b R hR (Or.inl hp)
        · exact (I.inst _ _).ownMono b R hR (Or.inr ⟨u, hu⟩)
        · rcases hown with ⟨h0, -⟩ | h
          · rw [h0, z0] at hR; have := own_ge hR; omega
          · rw [own_unique hR h]; exact ⟨_, balOf_some hc, Int.le_refl _⟩
      fresh := fun hn => by have := (hn a).symm.trans hcpA; cases this }
  have hid : ((c.st a).setInst q i c').id = rid32 a := I.ids a
  refine ⟨G', inv_frame I S hG'ne (by rw [hG'at]; exact E0) (instOk_G hG'at hI)
    (fun _ _ => hbelow) ?_ ?_ ?_ ?_⟩
  · intro d y hy
    rw [bcast_sentTo hid ho d] at hy
    split at hy
    · cases hy
    rename_i hd
    have hy' : y = _ := List.mem_singleton.1 hy
    subst hy'
    refine ⟨⟨?_, a, hid, Ne.symm hd, ?_, ?_⟩, fun q' j h => ?_, fun z h => Msg.noConfusion h,
      fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
    · show (G' q i).prop (sint.Z cp.ballot) c'.valA
      rw [hG'at]; exact Or.inr ⟨rfl, rfl⟩
    · exact hown
    · show (G' q i).acc a (sint.Z cp.ballot) c'.valA
      rw [hG'at]; exact Or.inr ⟨rfl, rfl, rfl⟩
    · simp only [msgInst, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hbelow
  · intro _ _ _ _ _ cp'' hc''
    rw [hcpA] at hc''; cases hc''; exact Or.inr (Or.inl hc'st)
  · intro cp'' lb hc'' hl hp _ ho'
    rw [hcpA] at hc''; cases hc''
    exact absurd (by rw [← hc'b]; exact ho') (hprepF lb hl hp)
  · intro _ _ _; exact ⟨c', hcpA, fun h => st_facts.2.2.2.2.1 (hc'st.symm.trans h)⟩

/-! ## The fast path -/

set_option maxHeartbeats 1000000 in
/-- The leader `a`'s PREACCEPTED ballot-0 copy `cp` of `(q, i)` is committed (`leaderCommit` of a
copy `c2` with `cp`'s value, ballot and vbal) on an unchanged pre-accept. -/
theorem inv_fast {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {q i : w32} {cp c2 : Copy} {lb2 : LB}
    {m0 : Msg} {s' : RState} {o : List Out} (I : CInv c G)
    (hst : c1.st = fun j => if j = a then s' else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv (.msg m0)) (c.inflight j) else c.inflight j) ++
        sentTo gNet j o)
    (hc : cpOf c a q i = some cp) (haL : a = rowOf q) (hb : cp.ballot = 0)
    (hpre : cp.status = St.PREACCEPTED) (heq : ∃ X, X ≠ rowOf q ∧ (G q i).eq X)
    (hlc : leaderCommit (c.st a) q i c2 lb2 = .ok (s', o))
    (hv : c2.valA = cp.valA) (hb2 : c2.ballot = cp.ballot) (hv2 : c2.vbal = cp.vbal) :
    ∃ G', CInv c1 G' ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i) := by
  have hbelow := I.copyBelow a q i cp hc
  have hC := (I.inst q i).copies a cp hc
  obtain ⟨cp', e1, e2, e3, hcs, hcv, hcb, hcvb, hout⟩ := A1d.leaderCommit_shape hlc
  have hcrt : ∀ p, s'.crt p = (c.st a).crt p := fun p => by simp only [RState.crt, e3]
  have hcpA : cpOf c1 a q i = some cp' := by
    rw [cpOf_postA hst, e1]; exact setInst_self _ _ _ _
  have S : Step1 c c1 a q i m0 o :=
    step1_of (e := .msg m0) rfl hst hinf e2 (fun q' i' h => by rw [e1]; exact setInst_other _ _ h)
      (by rw [e3]) (hcrt _) (fun r => by rw [hcrt]; exact I.crtOwn a r)
  have hbal : balOf c1 q i = balOf c q i := by
    funext j
    by_cases hj : j = a
    · subst hj; rw [balOf_some hcpA, balOf_some hc, hcb, hb2]
    · simp only [balOf, cpOf_postN hst hj]
  obtain ⟨k1, k2, k3, -⟩ := hC.leader0 haL hb hpre
  have AIo := (I.inst q i).ainv
  have E0 : Evolve (rowOf q) (G q i) (balOf c q i) (addFast (G q i) cp.valA) (balOf c1 q i) :=
    { le := ⟨fun _ _ _ h => h, fun _ _ h => h, fun _ h => h, fun _ h => h, fun _ h => h,
             fun _ h => Or.inl h⟩
      bal_mono := fun y B h => ⟨B, by rw [hbal]; exact h, Int.le_refl B⟩
      acc_new := fun _ _ _ h hn => absurd h hn
      eq_new := fun _ h hn => absurd h hn
      fast_new := by
        intro v hv' hn B hB
        rw [← haL, balOf_some hc, hb, z0] at hB; cases hB; exact Int.le_refl _
      fast_cre := fun v hv' => hv'.elim (AIo.fast_cre v) (fun e => e ▸ k1)
      fast_eq := fun v hv' => hv'.elim (AIo.fast_eq v) (fun _ => heq)
      fast_noprop := fun v hv' => hv'.elim (AIo.fast_noprop v) (fun _ => by rw [← z0]; exact k2) }
  have GO : GOnly a (rowOf q) (G q i) (addFast (G q i) cp.valA) :=
    ⟨fun _ _ _ h hn => absurd h hn, fun _ _ h hn => absurd h hn, fun _ h => h, fun _ h => h,
     fun _ h hn => absurd h hn, fun _ _ _ => haL⟩
  obtain ⟨G', hG'at, hG'ne⟩ : ∃ G' : GG, G' q i = addFast (G q i) cp.valA ∧
      ∀ q' i', ¬ (q' = q ∧ i' = i) → G' q' i' = G q' i' :=
    ⟨ggSet G _ _ _, ggSet_at _ _ _ _, fun _ _ h => ggSet_ne _ _ h⟩
  have hcom : isCommitted cp'.status := Or.inl hcs
  have hnewC : CopyOk c1 (fun _ _ => addFast (G q i) cp.valA) q i a cp' :=
    { nonneg := by rw [hcb, hb2]; exact hC.nonneg
      ballotForm := by rw [hcb, hb2]; exact hC.ballotForm
      vbalLe := by rw [hcb, hb2, hcvb, hv2]; exact hC.vbalLe
      stOk := Or.inr (Or.inr (Or.inr hcom))
      noVotes := fun h => absurd h (com_notPre' hcs)
      accVote := fun h => absurd (hcs.symm.trans h) st_facts.2.2.2.1
      committed := fun _ => Or.inl (Or.inr (by rw [hcv, hv]))
      rstVbal := fun h => absurd (Or.inr h) (com_notPre' hcs)
      eqCre := fun h => absurd (Or.inr (Or.inr h)) (com_notPre' hcs)
      leader0 := fun _ _ h => absurd (Or.inr (Or.inl h)) (com_notPre' hcs)
      ownFresh := fun h => absurd h (com_notPre' hcs)
      preparing := fun _ _ _ hn => absurd hcom hn
      eqTrack := fun h => absurd haL h }
  have hI : InstOk c1 (fun _ _ => addFast (G q i) cp.valA) q i :=
    { ainv := ainv_fastOnly AIo E0
      copies := by
        intro y cp'' hc''
        by_cases hy : y = a
        · subst hy; rw [hcpA] at hc''; cases hc''; exact hnewC
        · rw [cpOf_postN hst hy] at hc''
          exact copyOk_keep ((I.inst _ _).copies y cp'' hc'') E0 GO hy
      noCopy := by
        intro y hy
        have hya : y ≠ a := by rintro rfl; rw [hcpA] at hy; cases hy
        rw [cpOf_postN hst hya] at hy
        exact (I.inst _ _).noCopy y hy
      fastL := fun _ _ => ⟨cp', by rw [← haL]; exact hcpA, hcom⟩
      leaderCopy := fun _ => ⟨cp', by rw [← haL]; exact hcpA,
        fun h => st_facts.1 (hcs.symm.trans h)⟩
      ownMono := fun b R hR hp => by rw [hbal]; exact (I.inst _ _).ownMono b R hR hp
      fresh := fun hn => by have := (hn a).symm.trans hcpA; cases this }
  refine ⟨G', inv_frame I S hG'ne (by rw [hG'at]; exact E0) (instOk_G hG'at hI)
    (fun _ _ => hbelow) ?_ ?_ ?_ ?_⟩
  · intro d y hy
    have := hout d y (mem_sentTo hy)
    subst this
    refine ⟨?_, fun q' j h => ?_, fun z h => Msg.noConfusion h, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
    · show Chosen (G' q i) (c2.cmds, c2.seq, c2.deps, c2.base)
      rw [hG'at]; exact Or.inl (Or.inr hv)
    · simp only [msgInst, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hbelow
  · intro _ _ _ _ _ cp'' hc''
    rw [hcpA] at hc''; cases hc''; exact Or.inr (Or.inr hcom)
  · intro cp'' _ hc'' _ _ hn _
    rw [hcpA] at hc''; cases hc''; exact absurd hcom hn
  · intro _ _ _; exact ⟨cp', hcpA, fun h => st_facts.1 (hcs.symm.trans h)⟩

/-! ## The copy stays PREACCEPTED -/

set_option maxHeartbeats 1000000 in
/-- `a`'s PREACCEPTED copy `cp` is replaced by `cp'` with the same status, ballot, vbal and
bookkeeping read by `CInv` (the value may change, but not at the leader's ballot 0); nothing sent. -/
theorem inv_keepPre {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {q i : w32} {cp cp' : Copy}
    {m0 : Msg} (I : CInv c G)
    (hst : c1.st = fun j => if j = a then (c.st a).setInst q i cp' else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv (.msg m0)) (c.inflight j) else c.inflight j) ++
        sentTo gNet j [])
    (hc : cpOf c a q i = some cp) (hpre : cp.status = St.PREACCEPTED)
    (es : cp'.status = cp.status) (eb : cp'.ballot = cp.ballot) (ev : cp'.vbal = cp.vbal)
    (hlb : ∀ lb', cp'.lb = some lb' → ∃ lb, cp.lb = some lb ∧ lb'.preparing = lb.preparing ∧
      lb'.recoveryInst = lb.recoveryInst ∧ lb'.prepareOKs = lb.prepareOKs)
    (hl0 : a = rowOf q → cp.ballot = 0 →
      cp'.valA = cp.valA ∧ ∀ lb', cp'.lb = some lb' → lb'.preAcceptOKs = 0) :
    ∃ G', CInv c1 G' ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i) := by
  have hbelow := I.copyBelow a q i cp hc
  have hC := (I.inst q i).copies a cp hc
  have hcpA : cpOf c1 a q i = some cp' := by rw [cpOf_postA hst]; exact setInst_self _ _ _ _
  have S : Step1 c c1 a q i m0 [] :=
    step1_of (e := .msg m0) rfl hst hinf rfl (fun q' i' h => setInst_other _ _ h) rfl rfl
      (fun r => I.crtOwn a r)
  have hbal : balOf c1 q i = balOf c q i := by
    funext j
    by_cases hj : j = a
    · subst hj; rw [balOf_some hcpA, balOf_some hc, eb]
    · simp only [balOf, cpOf_postN hst hj]
  have IO := I.inst q i
  have E0 : Evolve (rowOf q) (G q i) (balOf c q i) (G q i) (balOf c1 q i) := by
    rw [hbal]; exact Evolve.refl IO.ainv
  have hP := pre_of (Or.inl (es.trans hpre))
  have hnewC : CopyOk c1 G q i a cp' :=
    { nonneg := by rw [eb]; exact hC.nonneg
      ballotForm := by rw [eb]; exact hC.ballotForm
      vbalLe := by rw [eb, ev]; exact hC.vbalLe
      stOk := Or.inr (Or.inl hP.1)
      noVotes := fun _ => hC.noVotes (Or.inr (Or.inl hpre))
      accVote := fun h => absurd h hP.2.2.1
      committed := fun h => absurd h hP.2.2.2
      rstVbal := fun _ h => by rw [ev] at h ⊢; exact hC.rstVbal (Or.inl hpre) h
      eqCre := fun h => absurd (es.symm.trans h |>.symm.trans hpre) (by decide)
      leader0 := fun h1 h2 _ => by
        rw [eb] at h2
        obtain ⟨k1, k2, k3, -⟩ := hC.leader0 h1 h2 hpre
        obtain ⟨j1, j2⟩ := hl0 h1 h2
        exact ⟨by rw [j1]; exact k1, k2, k3, j2⟩
      ownFresh := fun _ ho => by rw [eb] at ho ⊢; exact hC.ownFresh (Or.inr (Or.inl hpre)) ho
      preparing := fun lb' hl' hp hn ho => by
        obtain ⟨lb, hl, f1, f2, f3⟩ := hlb lb' hl'
        rw [f1] at hp; rw [eb] at ho ⊢; rw [hbal, f2, f3]
        exact hC.preparing lb hl hp (pre_notCom hpre) ho
      eqTrack := fun h1 h2 => by
        rcases hC.eqTrack h1 h2 with h | h | ⟨h, -⟩ | h
        · exact absurd (hpre.symm.trans h) (by decide)
        · exact absurd h (pre_notCom hpre)
        · exact absurd (hpre.symm.trans h) (by decide)
        · rw [eb]; exact Or.inr (Or.inr (Or.inr h)) }
  have hI : InstOk c1 G q i :=
    { ainv := by rw [hbal]; exact IO.ainv
      copies := fun j cp'' hc'' => by
        by_cases hj : j = a
        · subst hj; rw [hcpA] at hc''; cases hc''; exact hnewC
        · rw [cpOf_postN hst hj] at hc''
          exact copyOk_keep (IO.copies j cp'' hc'') E0 (GOnly.refl a _ _) hj
      noCopy := fun j hc'' => by
        by_cases hj : j = a
        · subst hj; rw [hcpA] at hc''; cases hc''
        · rw [cpOf_postN hst hj] at hc''; exact IO.noCopy j hc''
      fastL := fun w hw => by
        obtain ⟨cpL, hL, hLc⟩ := IO.fastL w hw
        by_cases hLa : rowOf q = a
        · exfalso; rw [hLa, hc] at hL; cases hL; exact pre_notCom hpre hLc
        · exact ⟨cpL, by rw [cpOf_postN hst hLa]; exact hL, hLc⟩
      leaderCopy := fun _ => by
        by_cases hLa : rowOf q = a
        · rw [hLa]; exact ⟨cp', hcpA, hP.2.1⟩
        · obtain ⟨cpL, hL, hne⟩ := IO.leaderCopy ⟨a, cp, hc⟩
          exact ⟨cpL, by rw [cpOf_postN hst hLa]; exact hL, hne⟩
      ownMono := fun b' R' hR' hp => by rw [hbal]; exact IO.ownMono b' R' hR' hp
      fresh := fun hn => by have := (hn a).symm.trans hcpA; cases this }
  refine ⟨G, inv_frame I S (fun _ _ _ => rfl) E0 hI (fun _ _ => hbelow)
    (fun _ _ h => absurd h List.not_mem_nil) ?_ ?_ ?_⟩
  · intro x hx hb hr hi cp'' hc''
    rw [hcpA] at hc''; cases hc''
    have hx' : Msg.preAccept x ∈ c.inflight a := by
      rw [S.inf a] at hx
      rcases List.mem_append.1 hx with h | h
      · exact S.old h
      · exact absurd h List.not_mem_nil
    have := ((I.msgs a _ hx').1 hb).2.2.2.1
    rw [hr, hi] at this
    rcases this cp hc with h | h | h
    · left; rw [eb]; exact h
    · exact absurd (hpre.symm.trans h) (by decide)
    · exact absurd h (pre_notCom hpre)
  · intro cp'' lb' hc'' hl' hp hn ho
    rw [hcpA] at hc''; cases hc''
    obtain ⟨lb, hl, f1, -, f3⟩ := hlb lb' hl'
    exact ⟨cp, lb, hc, hl, by rw [← f1]; exact hp, pre_notCom hpre, eb.symm, f3.symm⟩
  · intro _ _ _; exact ⟨cp', hcpA, hP.2.1⟩

/-! ## `handlePreAcceptOK` -/

theorem ballot0_of {c : Cfg gNet} {G : GG} {q i : w32} {a : Fin 3} {cp : Copy}
    (hC : CopyOk c G q i a cp) (h : isInitialBallot cp.ballot = true) : cp.ballot = 0 := by
  rcases hC.ballotForm with h0 | ⟨R, hR⟩
  · exact h0
  · have := own_ge hR; have := init_lt h; omega

theorem safeAt0 {g : Gh Val} {bal : Fin 3 → Option Int} {L : Fin 3} {v : Val} :
    SafeAt g bal L (sint.Z (0 : w32)) v := by
  intro b' h0 h1; rw [z0] at h1; omega

/-- **`handlePreAcceptOK` keeps the invariant.** -/
theorem inv_preAcceptOK_core {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : PreAcceptOKM} {s' : RState}
    {o : List Out} (I : CInv c G)
    (hst : c1.st = fun j => if j = a then s' else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv (.msg (.preAcceptOK m))) (c.inflight j) else c.inflight j) ++
        sentTo gNet j o)
    (hm : Msg.preAcceptOK m ∈ c.inflight a) (h : stepPreAcceptOK (c.st a) m = .ok (s', o)) :
    ∃ G', CInv c1 G' ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i) := by
  obtain ⟨-, hcases⟩ := stepPreAcceptOK_cases h
  have hid : (c.st a).id = rid32 a := I.ids a
  rcases hcases with ⟨rfl, rfl⟩ | ⟨c0, lb, hc, hpre, hinit, hl, rest⟩
  · exact ⟨G, inv_quiet I ⟨hst, hinf⟩ ⟨rfl, rfl, rfl⟩ quietO_nil⟩
  rw [hid] at hc
  have hc' : cpOf c a (rid32 a) m.inst = some c0 := hc
  have hC := (I.inst _ _).copies a c0 hc'
  have hb0 := ballot0_of hC hinit
  have haL : a = rowOf (rid32 a) := (rowOf_rid a).symm
  obtain ⟨k1, k2, k3, k4⟩ := hC.leader0 haL hb0 hpre
  have hM : ∃ X, X ≠ a ∧ (G (rid32 a) m.inst).eq X := I.msgs a _ hm
  rcases rest with ⟨-, hlc⟩ | ⟨rfl, ho⟩ | ⟨hsge, -, -⟩
  · rw [hid] at hlc
    refine inv_fast I hst hinf hc' haL hb0 hpre ?_ hlc rfl rfl rfl
    rw [← haL]; exact hM
  · rw [hid] at hst ho
    refine inv_acceptOwn I hst hinf hc' hpre rfl rfl rfl ?_ (Or.inl ⟨hb0, haL⟩) ?_ ?_ ?_ ho
    · intro _ _ _ ho'; rw [hb0, z0] at ho'; have := own_ge ho'; omega
    · rw [hb0]; exact k2
    · rw [hb0]; exact safeAt0
    · exact fun _ => k3
  · rw [k4 lb hl] at hsge; exact absurd hsge (by decide)

/-! ## `handlePreAcceptReply` -/

theorem prod3_eq {α β γ : Type} {p : α × β × γ} {z : γ} (h : p.2.2 = z) : p = (p.1, p.2.1, z) := by
  obtain ⟨x, y, w⟩ := p; cases h; rfl

theorem ofNat_ne_rid {k : Nat} {L : Fin 3} (hk : k < 3) (hne : k ≠ L.val) :
    BitVec.ofNat 32 k ≠ rid32 L := by
  intro h
  have e := congrArg BitVec.toNat h
  simp only [rid32, BitVec.toNat_ofNat] at e
  have := L.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e
  exact hne e

set_option maxHeartbeats 2000000 in
/-- **`handlePreAcceptReply` keeps the invariant.** -/
theorem inv_preAcceptReply_core {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : PreAcceptReplyM}
    {s' : RState} {o : List Out} (I : CInv c G)
    (hst : c1.st = fun j => if j = a then s' else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv (.msg (.preAcceptReply m))) (c.inflight j) else c.inflight j) ++
        sentTo gNet j o)
    (hm : Msg.preAcceptReply m ∈ c.inflight a) (h : stepPreAcceptReply (c.st a) m = .ok (s', o)) :
    ∃ G', CInv c1 G' ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i) := by
  obtain ⟨-, hcases⟩ := stepPreAcceptReply_cases h
  have hid : (c.st a).id = rid32 a := I.ids a
  rcases hcases with ⟨rfl, rfl⟩ | ⟨c0, lb, hc, hpre, hbm, hl, rest⟩
  · exact ⟨G, inv_quiet I ⟨hst, hinf⟩ ⟨rfl, rfl, rfl⟩ quietO_nil⟩
  have hc' : cpOf c a m.replica m.inst = some c0 := hc
  have hC := (I.inst _ _).copies a c0 hc'
  obtain ⟨hM0, hM1⟩ : MsgOk c G a (.preAcceptReply m) := I.msgs a _ hm
  have hlead : ∀ L, L = rowOf m.replica → a = L → c0.ballot = 0 → lb.preAcceptOKs = 0 := by
    intro L hL haL hb0
    subst hL
    exact (hC.leader0 haL hb0 hpre).2.2.2 lb hl
  rcases rest with ⟨-, rfl, lb', rfl, LS⟩ | ⟨hok, c2, lb2, rest, MG, LO⟩
  · -- a NACK
    refine inv_keepPre I hst hinf hc' hpre rfl rfl rfl ?_ ?_
    · intro lb'' hl''; cases hl''; exact ⟨lb, hl, LS.preparing, LS.recoveryInst, LS.prepareOKs⟩
    · intro haL hb0
      refine ⟨rfl, fun lb'' hl'' => ?_⟩
      cases hl''; rw [LS.oks]; exact hlead _ rfl haL hb0
  rcases rest with ⟨hinit, heq2, hgt, hlc⟩ | ⟨rfl, ho⟩ | ⟨hsge, rfl, rfl⟩
  · -- the fast commit
    have hb0 := ballot0_of hC hinit
    have hmb : m.ballot = 0 := hbm ▸ hb0
    obtain ⟨haL, hcA, hcv⟩ := hM0 hmb
    obtain ⟨k1, -, -, -⟩ := hC.leader0 haL hb0 hpre
    obtain ⟨e1, e2, e3, e4⟩ := merge_eq (prod3_eq heq2)
    have hbase : c2.base = c0.base := by
      rcases MG.base with ⟨h1, -⟩ | ⟨-, h2⟩
      · rw [hgt] at h1; cases h1
      · exact h2
    have hv : c2.valA = c0.valA := by
      simp only [Copy.valA, MG.cmds, MG.seq, MG.deps, e1, e2, hbase]
    obtain ⟨v, hvc, hlen, hrows, hbs⟩ := hcv hok
    have := (I.inst _ _).ainv.cre_uniq _ _ hvc k1
    subst this
    have hmdeps : m.deps = c0.deps := by
      refine deps_ext hlen fun k => ?_
      by_cases hk : k = (rowOf m.replica).val ∨ 3 ≤ k
      · exact hrows k hk
      · rw [not_or] at hk
        refine (e4 k (by omega) ?_).symm
        rw [I.ids a, haL]; exact ofNat_ne_rid (by omega) hk.1
    have hmbase : m.base = c0.base := hbs hgt
    refine inv_fast I hst hinf hc' haL hb0 hpre ?_ hlc hv (MG.ballot) (MG.vbal)
    exact hcA hok ⟨c0.valA, k1, by simp only [Copy.valA, e3, hmdeps, hmbase]⟩
  · -- the slow path: an Accept at the copy's ballot
    have hb := hC.nonneg
    by_cases hmb : m.ballot = 0
    · have hb0 : c0.ballot = 0 := hbm.trans hmb
      obtain ⟨haL, -, -⟩ := hM0 hmb
      obtain ⟨-, k2, k3, -⟩ := hC.leader0 haL hb0 hpre
      refine inv_acceptOwn I hst hinf hc' hpre rfl MG.ballot rfl ?_ (Or.inl ⟨hb0, haL⟩) ?_ ?_
        (fun _ => k3) ho
      · intro _ _ _ ho'; rw [hb0, z0] at ho'; have := own_ge ho'; omega
      · rw [hb0, z0]; exact k2
      · rw [hb0]; exact safeAt0
    · obtain ⟨hown, hrst⟩ := hM1 hmb hok
      rw [← hbm] at hown hrst
      refine inv_acceptOwn I hst hinf hc' hpre rfl MG.ballot rfl ?_ (Or.inr hown)
        (hC.ownFresh (Or.inr (Or.inl hpre)) hown)
        (((I.inst _ _).ainv.rst_safe _ hrst).safeAt _) ?_ ho
      · intro lb'' hl'' hp _
        cases hl''
        rw [LO.preparing] at hp
        exact (hC.preparing lb hl hp (pre_notCom hpre) hown).2.1 hrst
      · intro h0; have := own_ge hown; omega
  · -- no quorum yet (impossible at the leader's ballot 0)
    refine inv_keepPre I hst hinf hc' hpre MG.status MG.ballot MG.vbal ?_ ?_
    · intro lb'' hl''; cases hl''; exact ⟨lb, hl, LO.preparing, LO.recoveryInst, LO.prepareOKs⟩
    · intro haL hb0
      rw [hlead _ rfl haL hb0] at hsge; exact absurd hsge (by decide)

end Perennial.gryff.pureA.SPA
