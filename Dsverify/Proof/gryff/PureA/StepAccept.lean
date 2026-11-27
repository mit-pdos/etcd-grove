/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/StepAccept.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1 (sub-unit A1d), internal: **`handleAccept` keeps the agreement invariant**
(`inv_accept_core`, behind `Inv.lean`'s `inv_accept`).

`stepAccept_shape`: the step's three outcomes (the copy is committed: nothing; a higher ballot: a
NACK; else the copy becomes ACCEPTED at the Accept's ballot with its value and an OK reply goes to
the proposer). The history gains the acceptor's vote `(b, v)` (`addAcc`): it is for the Accept's
proposal (`MsgOk`), at a ballot at least the acceptor's (the ballot check), and the OK reply carries
the vote together with the proposer's own vote at `b` (`MsgOk`'s Accept clause, G19).
-/
module

public import Dsverify.Proof.gryff.PureA.StepFrame

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.A1d

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA

theorem stepAccept_shape {s s' : RState} {m : EAcceptM} {o : List Out}
    (h : stepAccept s m = .ok (s', o)) :
    (∃ c, s.inst m.replica m.inst = some c ∧ isCommitted c.status ∧ s' = s ∧ o = []) ∨
    ∃ t, CrtB s t m.replica m.inst ∧
      ((∃ c x, s.inst m.replica m.inst = some c ∧ ¬ isCommitted c.status ∧
          sint.Z m.ballot < sint.Z c.ballot ∧ s' = t ∧ o = [x] ∧
          sendPeer s m.leaderId (.acceptReply { replica := m.replica, inst := m.inst, ok := FALSE, ballot := c.ballot }) = some x) ∨
       (∃ cp x, s' = t.setInst m.replica m.inst cp ∧ o = [x] ∧
          cp.status = St.ACCEPTED ∧ cp.ballot = m.ballot ∧ cp.vbal = m.ballot ∧
          cp.valA = (m.cmds, m.seq, m.deps, m.base) ∧
          (s.inst m.replica m.inst = none ∨ ∃ c, s.inst m.replica m.inst = some c ∧
            ¬ isCommitted c.status ∧ sint.Z c.ballot ≤ sint.Z m.ballot ∧ cp.lb = c.lb) ∧
          sendPeer s m.leaderId (.acceptReply { replica := m.replica, inst := m.inst, ok := TRUE, ballot := m.ballot }) = some x)) := by
  unfold stepAccept at h
  cases hc : s.inst m.replica m.inst <;> simp only [hc] at h <;> peel h
  all_goals cases h
  · exact Or.inr ⟨_, Or.inr ⟨(by assumption), rfl⟩,
      Or.inr ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl, (by assumption)⟩⟩
  · exact Or.inr ⟨_, Or.inl rfl, Or.inr ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl,
      (by assumption)⟩⟩
  · exact Or.inl ⟨_, rfl, (by assumption), rfl, rfl⟩
  · exact Or.inr ⟨_, Or.inr ⟨(by assumption), rfl⟩, Or.inl ⟨_, _, rfl, (by assumption),
      (slt_iff _ _).1 (by assumption), rfl, rfl, (by assumption)⟩⟩
  · refine Or.inr ⟨_, Or.inr ⟨(by assumption), rfl⟩, Or.inr ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl,
      Or.inr ⟨_, rfl, (by assumption), ?_, rfl⟩, (by assumption)⟩⟩
    rename_i hs _ _ _; rw [slt_iff] at hs; omega
  · exact Or.inr ⟨_, Or.inl rfl, Or.inl ⟨_, _, rfl, (by assumption),
      (slt_iff _ _).1 (by assumption), rfl, rfl, (by assumption)⟩⟩
  · refine Or.inr ⟨_, Or.inl rfl, Or.inr ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl,
      Or.inr ⟨_, rfl, (by assumption), ?_, rfl⟩, (by assumption)⟩⟩
    rename_i hs _ _ _; rw [slt_iff] at hs; omega

/-- **`handleAccept`** keeps `CInv`. -/
theorem inv_accept_core {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : EAcceptM} {s' : RState}
    {o : List Out} (I : CInv c G)
    (hst : c1.st = fun j => if j = a then s' else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv (.msg (.accept m))) (c.inflight j) else c.inflight j) ++
        sentTo gNet j o)
    (hm : Msg.accept m ∈ c.inflight a) (h : stepAccept (c.st a) m = .ok (s', o)) :
    ∃ G', CInv c1 G' ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i) := by
  obtain ⟨hprop, R, hlid, hRa, hown, haccR⟩ := I.msgs a _ hm
  have hbelow := I.msgBelow a _ m.replica m.inst hm rfl
  rcases stepAccept_shape h with ⟨c0, hc0, hcom, rfl, rfl⟩ | ⟨t, hcb, hr⟩
  · exact ⟨G, inv_frame_same I hst hinf rfl rfl rfl (fun r => I.crtOwn a r) hbelow
      (fun d m h => by simp at h) rfl⟩
  obtain ⟨ht1, ht2, ht3, ht4, ht5⟩ := crtB_facts I hcb hbelow
  rcases hr with ⟨c0, x, hc0, hncom, hlt, rfl, rfl, hx⟩ |
    ⟨cp, x, rfl, rfl, hcs, hcb', hcv, hval, hold, hx⟩
  · -- a NACK
    rw [hlid] at hx
    have := sendPeer_dst hx; subst this
    refine ⟨G, inv_frame_same I hst hinf ht1 ht2 ht3 ht4 hbelow ?_ ht5⟩
    intro d m' hd
    simp only [List.mem_singleton, Out.send.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    exact ⟨rfl, ⟨fun h => absurd rfl h, fun h => absurd rfl h⟩,
      fun q j hj => by cases hj; exact ⟨rfl, rfl⟩⟩
  -- the copy becomes ACCEPTED at `b` with `v`; the acceptor votes
  rw [hlid] at hx
  have := sendPeer_dst hx; subst this
  have IO := I.inst m.replica m.inst
  have A := IO.ainv
  have notOwnA : ¬ Own (sint.Z m.ballot) a := by
    intro ho
    rcases hown with ⟨h0, -⟩ | hoR
    · rw [h0] at ho; have := Own.pos ho; revert this; decide
    · exact hRa (Own.uniq hoR ho)
  have hcpA : cpOf c1 a m.replica m.inst = some cp := by
    rw [cpOf_postA hst]; exact setInst_self _ _ _ _
  have hbalA : balOf c1 m.replica m.inst a = some (sint.Z m.ballot) := by
    rw [balOf_some hcpA, hcb']
  have hbalN : ∀ j, j ≠ a → balOf c1 m.replica m.inst j = balOf c m.replica m.inst j := by
    intro j hj; simp only [balOf, cpOf_postN hst hj]
  have hballe : ∀ B, balOf c m.replica m.inst a = some B → B ≤ sint.Z m.ballot := by
    intro B hB
    obtain ⟨cp0, h0, rfl⟩ := balOf_some_inv hB
    rcases hold with hn | ⟨c0, hc0, -, hle, -⟩
    · have e : cpOf c a m.replica m.inst = none := hn
      rw [e] at h0; cases h0
    · have e : cpOf c a m.replica m.inst = some c0 := hc0
      rw [e] at h0; cases h0; exact hle
  have hvle : ∀ b u, (G m.replica m.inst).acc a b u → b ≤ sint.Z m.ballot := by
    intro b u hu
    rcases hold with hn | ⟨c0, hc0, hnc, hle, -⟩
    · exact absurd hu ((IO.noCopy a hn).1 b u)
    · exact Int.le_trans (votes_le (IO.copies a c0 hc0) hnc b u hu) hle
  let v : Val := (m.cmds, m.seq, m.deps, m.base)
  let g := G m.replica m.inst
  let g' := addAcc g a (sint.Z m.ballot) v
  have E0 : Evolve (rowOf m.replica) g (balOf c m.replica m.inst) g' (balOf c1 m.replica m.inst) :=
    { le := le_addAcc g a _ v
      bal_mono := fun j B hB => by
        by_cases hj : j = a
        · subst hj; exact ⟨_, hbalA, hballe B hB⟩
        · rw [hbalN j hj]; exact ⟨B, hB, Int.le_refl B⟩
      acc_new := fun j b' w hn hno B hB => by
        rcases hn with hn | ⟨rfl, rfl, rfl⟩
        · exact absurd hn hno
        · exact hballe B hB
      eq_new := fun _ hn hno => absurd hn hno
      fast_new := fun _ hn hno => absurd hn hno
      fast_cre := A.fast_cre
      fast_eq := A.fast_eq
      fast_noprop := A.fast_noprop }
  have hNew : CopyOk c1 (fun _ _ => g') m.replica m.inst a cp :=
    { nonneg := by
        rw [hcb']
        rcases hown with ⟨h0, -⟩ | ho
        · rw [h0]; decide
        · exact Int.le_of_lt (Own.pos ho)
      ballotForm := by
        rw [hcb']
        rcases hown with ⟨h0, -⟩ | ho
        · exact Or.inl h0
        · exact Or.inr ⟨R, ho⟩
      vbalLe := by rw [hcv, hcb']; exact Int.le_refl _
      stOk := Or.inr (Or.inr (Or.inl hcs))
      noVotes := fun hs => absurd hs (acc_notPre hcs)
      accVote := fun _ => ⟨Or.inr ⟨rfl, by rw [hcv], hval⟩, fun b' u hu => by
        rw [hcv]
        rcases hu with hu | ⟨-, rfl, -⟩
        · exact hvle b' u hu
        · exact Int.le_refl _⟩
      committed := fun hs => absurd hs (acc_notCommitted hcs)
      rstVbal := fun hs => absurd (Or.inr hs) (acc_notPre hcs)
      eqCre := fun hs => absurd (Or.inr (Or.inr hs)) (acc_notPre hcs)
      leader0 := fun _ _ hs => absurd (Or.inr (Or.inl hs)) (acc_notPre hcs)
      ownFresh := fun hs => absurd hs (acc_notPre hcs)
      preparing := fun _ _ _ _ ho => absurd (by rw [hcb'] at ho; exact ho) notOwnA
      eqTrack := fun _ _ => Or.inl hcs }
  have hI0 : InstOk c1 (fun _ _ => g') m.replica m.inst :=
    { ainv :=
        { prop_uniq := A.prop_uniq
          acc_prop := fun j b' u hu => by
            rcases hu with hu | ⟨-, rfl, rfl⟩
            · exact A.acc_prop j b' u hu
            · exact hprop
          prop_nonneg := A.prop_nonneg
          prop_safe := fun b' u hp => safeAt_evolve E0 (A.prop_safe b' u hp)
          rst_safe := fun b' hr => safeAll_evolve E0 (A.rst_safe b' hr)
          cre_uniq := A.cre_uniq
          fast_cre := A.fast_cre
          fast_eq := A.fast_eq
          fast_noprop := A.fast_noprop }
      copies := fun j cp' hc => by
        by_cases hj : j = a
        · subst hj; rw [hcpA] at hc; cases hc; exact hNew
        · rw [cpOf_postN hst hj] at hc
          exact copyOk_narrow (G' := fun _ _ => g') E0 (narrow_addAcc g hj _ v)
            (IO.copies j cp' hc)
      noCopy := fun j hc => by
        by_cases hj : j = a
        · subst hj; rw [hcpA] at hc; cases hc
        · rw [cpOf_postN hst hj] at hc
          obtain ⟨k1, k2⟩ := IO.noCopy j hc
          exact ⟨fun b' u hu => hu.elim (k1 b' u) (fun k => hj k.1), k2⟩
      fastL := fun w hw => by
        obtain ⟨cpL, hL, hLc⟩ := IO.fastL w hw
        by_cases hLa : rowOf m.replica = a
        · exfalso
          rw [hLa] at hL
          rcases hold with hn | ⟨c0, hc0, hnc, -, -⟩
          · have e : cpOf c a m.replica m.inst = none := hn
            rw [e] at hL; cases hL
          · have e : cpOf c a m.replica m.inst = some c0 := hc0
            rw [e] at hL; cases hL; exact hnc hLc
        · exact ⟨cpL, by rw [cpOf_postN hst hLa]; exact hL, hLc⟩
      leaderCopy := fun _ => by
        by_cases hLa : rowOf m.replica = a
        · exact ⟨cp, by rw [hLa]; exact hcpA, by rw [hcs]; exact acc_ne.1⟩
        · cases hR : cpOf c R m.replica m.inst with
          | none => exact absurd haccR ((IO.noCopy R hR).1 _ _)
          | some cpR =>
            obtain ⟨cpL, hL, hne⟩ := IO.leaderCopy ⟨R, cpR, hR⟩
            exact ⟨cpL, by rw [cpOf_postN hst hLa]; exact hL, hne⟩
      ownMono := fun b' R' hR' hp => by
        obtain ⟨B, hB, hle⟩ := IO.ownMono b' R' hR' hp
        obtain ⟨B', hB', hle'⟩ := E0.bal_mono R' B hB
        exact ⟨B', hB', Int.le_trans hle hle'⟩
      fresh := fun hn => absurd ((hn a).symm.trans hcpA) (by simp) }
  let G' := ggSet G m.replica m.inst g'
  have hG0 : G' m.replica m.inst = g' := ggSet_at G _ _ g'
  refine ⟨G', inv_frame (q0 := m.replica) (i0 := m.inst) I hst hinf ht1
    (fun q i hn => by rw [setInst_other _ _ hn, ht2]) (fun q i hn => ggSet_ne G g' hn) ht3 ht4
    hbelow (by rw [hG0]; exact E0) (fun w hw => by rw [hG0] at hw; exact hw)
    (instOk_G (G := fun _ _ => g') hG0 hI0) ?_ ?_ ?_ ht5
    (fun _ _ _ => ⟨_, setInst_self _ _ _ _, by rw [hcs]; decide⟩)⟩
  · intro cp' h1 _
    rw [setInst_self] at h1; cases h1; exact Or.inr (Or.inl hcs)
  · intro cp' lb' h1 _ _ _ ho
    rw [setInst_self] at h1; cases h1
    exact absurd (by rw [hcb'] at ho; exact ho) notOwnA
  · intro d m' hd
    simp only [List.mem_singleton, Out.send.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    refine ⟨rfl, ⟨fun _ => ⟨a, Ne.symm hRa, v, ?_, ?_⟩, fun _ => hown⟩,
      fun q j hj => by cases hj; exact ⟨rfl, rfl⟩⟩
    · show (G' m.replica m.inst).acc a (sint.Z m.ballot) v
      rw [hG0]; exact Or.inr ⟨rfl, rfl, rfl⟩
    · show (G' m.replica m.inst).acc d (sint.Z m.ballot) v
      rw [hG0]; exact Or.inl haccR

end Perennial.gryff.pureA.A1d
