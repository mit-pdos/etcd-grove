/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/StepCommit.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1 (sub-unit A1d), internal: **`handleCommit` keeps the agreement invariant**
(`inv_commit_core`, behind `Inv.lean`'s `inv_commit`).

`stepCommit_shape`: an EXECUTED copy is left alone (only `crt` may rise); otherwise the copy becomes
COMMITTED with the Commit's value (its ballot and vbal kept; a new copy at ballot 0), the conflicts
and `CommittedUpTo` are updated, and the re-proposal of the bookkeeping's client proposals when a
no-op is committed only touches `proposeQ` and `lb` (which `CInv` does not read on a committed copy).
The history is unchanged: the Commit's value is chosen (`MsgOk`).
-/
module

public import Dsverify.Proof.gryff.PureA.StepFrame

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.A1d

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA

theorem stepCommit_shape {s s' : RState} {m : ECommitM} {o : List Out}
    (h : stepCommit s m = .ok (s', o)) :
    o = [] ∧ ∃ t, CrtB s t m.replica m.inst ∧
      ((∃ c, s.inst m.replica m.inst = some c ∧ c.status = St.EXECUTED ∧ s' = t) ∨
       ∃ cp, s'.inst = (t.setInst m.replica m.inst cp).inst ∧ s'.id = t.id ∧
         s'.crtInstance = t.crtInstance ∧ cp.status = St.COMMITTED ∧ cp.valA = m.valA ∧
         ((s.inst m.replica m.inst = none ∧ cp.ballot = 0 ∧ cp.vbal = 0) ∨
          ∃ c, s.inst m.replica m.inst = some c ∧ c.status ≠ St.EXECUTED ∧ cp.ballot = c.ballot ∧
            cp.vbal = c.vbal)) := by
  unfold stepCommit at h
  cases hc : s.inst m.replica m.inst <;> simp only [hc] at h <;> peel h
  all_goals cases h
  all_goals first
    | exact ⟨rfl, _, Or.inr ⟨(by assumption), rfl⟩, Or.inl ⟨_, rfl, (by assumption), rfl⟩⟩
    | exact ⟨rfl, _, Or.inl rfl, Or.inl ⟨_, rfl, (by assumption), rfl⟩⟩
    | skip
  all_goals (
    obtain ⟨e1, e2, e3⟩ := updateCommitted_inst (by assumption)
    have u := updateConflicts_inst
    first
    | exact ⟨rfl, _, Or.inr ⟨(by assumption), rfl⟩, Or.inr ⟨_,
        by first | (rw [e1, (u _ _ _ _ _).1] <;> rfl) | (rw [e1] <;> rfl),
        by first | (rw [e2, (u _ _ _ _ _).2.1] <;> rfl) | (rw [e2] <;> rfl),
        by first | (rw [e3, (u _ _ _ _ _).2.2] <;> rfl) | (rw [e3] <;> rfl),
        by rfl, by rfl,
        by first | exact Or.inl ⟨rfl, rfl, rfl⟩ | exact Or.inr ⟨_, rfl, (by assumption), rfl, rfl⟩⟩⟩
    | exact ⟨rfl, _, Or.inl rfl, Or.inr ⟨_,
        by first | (rw [e1, (u _ _ _ _ _).1] <;> rfl) | (rw [e1] <;> rfl),
        by first | (rw [e2, (u _ _ _ _ _).2.1] <;> rfl) | (rw [e2] <;> rfl),
        by first | (rw [e3, (u _ _ _ _ _).2.2] <;> rfl) | (rw [e3] <;> rfl),
        by rfl, by rfl,
        by first | exact Or.inl ⟨rfl, rfl, rfl⟩ | exact Or.inr ⟨_, rfl, (by assumption), rfl, rfl⟩⟩⟩)

/-- `AInv` along an evolution that keeps the history. -/
theorem ainv_evolve_same {g : Gh Val} {bal bal' : Fin 3 → Option Int} {L : Fin 3} (A : AInv g bal L)
    (E : Evolve L g bal g bal') : AInv g bal' L :=
  { A with
    prop_safe := fun b u hp => safeAt_evolve E (A.prop_safe b u hp)
    rst_safe := fun b hr => safeAll_evolve E (A.rst_safe b hr) }

/-- The committed copy (ballot and vbal: the old copy's, or `0` for a new one). -/
theorem copyOk_commit {c c1 : Cfg gNet} {G : GG} {q i : w32} {a : Fin 3} {cp : Copy}
    (IO : InstOk c G q i) (hcs : cp.status = St.COMMITTED) (hch : Chosen (G q i) cp.valA)
    (hold : (cpOf c a q i = none ∧ cp.ballot = 0 ∧ cp.vbal = 0) ∨
      ∃ c0, cpOf c a q i = some c0 ∧ cp.ballot = c0.ballot ∧ cp.vbal = c0.vbal) :
    CopyOk c1 G q i a cp :=
  { nonneg := by
      rcases hold with ⟨-, h0, -⟩ | ⟨c0, hc0, hb, -⟩
      · rw [h0]; decide
      · rw [hb]; exact (IO.copies a c0 hc0).nonneg
    ballotForm := by
      rcases hold with ⟨-, h0, -⟩ | ⟨c0, hc0, hb, -⟩
      · exact Or.inl h0
      · rw [hb]; exact (IO.copies a c0 hc0).ballotForm
    vbalLe := by
      rcases hold with ⟨-, h0, h1⟩ | ⟨c0, hc0, hb, hv⟩
      · rw [h0, h1]; exact Int.le_refl _
      · rw [hb, hv]; exact (IO.copies a c0 hc0).vbalLe
    stOk := Or.inr (Or.inr (Or.inr (Or.inl hcs)))
    noVotes := fun hs => absurd hs (com_notPre hcs)
    accVote := fun hs => absurd (hcs.symm.trans hs) com_ne.2.2.2
    committed := fun _ => hch
    rstVbal := fun hs => absurd (Or.inr hs) (com_notPre hcs)
    eqCre := fun hs => absurd (Or.inr (Or.inr hs)) (com_notPre hcs)
    leader0 := fun _ _ hs => absurd (Or.inr (Or.inl hs)) (com_notPre hcs)
    ownFresh := fun hs => absurd hs (com_notPre hcs)
    preparing := fun _ _ _ hn => absurd (Or.inl hcs) hn
    eqTrack := fun _ _ => Or.inr (Or.inl (Or.inl hcs)) }

/-- A chosen value has a copy somewhere (so the leader's copy exists). -/
theorem chosen_copy {c : Cfg gNet} {G : GG} {q i : w32} (IO : InstOk c G q i) {v : Val}
    (h : Chosen (G q i) v) : ∃ a cp, cpOf c a q i = some cp := by
  rcases h with hf | ⟨b, a1, -, -, h1, -⟩
  · obtain ⟨cp, hc, -⟩ := IO.fastL v hf; exact ⟨_, cp, hc⟩
  · cases hc : cpOf c a1 q i with
    | none => exact absurd h1 ((IO.noCopy a1 hc).1 b v)
    | some cp => exact ⟨a1, cp, hc⟩

/-- **A copy becomes COMMITTED with a chosen value** (its ballot and vbal kept, or `0` for a new
copy), nothing else changes in the instance space, no message is sent: `CInv` is kept with the same
history. Shared with `StepAcceptReply.lean` (the proposer's commit). -/
theorem inv_commit_copy {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} {q0 i0 : w32} {cp : Copy} (I : CInv c G)
    (hst : c1.st = fun j => if j = a then s' else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv e) (c.inflight j) else c.inflight j) ++ sentTo gNet j o)
    (hid : s'.id = (c.st a).id)
    (hcp : ∀ q i, ¬ (q = q0 ∧ i = i0) → s'.inst q i = (c.st a).inst q i)
    (hcp0 : s'.inst q0 i0 = some cp)
    (hcrtA : s'.crt (rid32 a) = (c.st a).crt (rid32 a))
    (hcrtLe : ∀ r : Fin 3, sint.Z (s'.crt (rid32 r)) ≤ sint.Z ((c.st r).crt (rid32 r)))
    (hbelow : rowOk q0 = true ∧ 0 ≤ sint.Z i0 ∧ sint.Z i0 < sint.Z ((c.st (rowOf q0)).crt q0))
    (hcs : cp.status = St.COMMITTED) (hch : Chosen (G q0 i0) cp.valA)
    (hold : (cpOf c a q0 i0 = none ∧ cp.ballot = 0 ∧ cp.vbal = 0) ∨
      ∃ c0, cpOf c a q0 i0 = some c0 ∧ cp.ballot = c0.ballot ∧ cp.vbal = c0.vbal)
    (hO : ∀ d m, Out.send d m ∈ o → isPP m = false ∧ MsgOk c1 G d m ∧
      ∀ q j, msgInst m = some (q, j) → q = q0 ∧ j = i0)
    (hlen : s'.crtInstance.length = (c.st a).crtInstance.length) :
    CInv c1 G ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G q i) (balOf c1 q i) := by
  have IO := I.inst q0 i0
  have A := IO.ainv
  have hcpA : cpOf c1 a q0 i0 = some cp := by rw [cpOf_postA hst]; exact hcp0
  have hbalN : ∀ j, j ≠ a → balOf c1 q0 i0 j = balOf c q0 i0 j := by
    intro j hj; simp only [balOf, cpOf_postN hst hj]
  have E0 : Evolve (rowOf q0) (G q0 i0) (balOf c q0 i0) (G q0 i0) (balOf c1 q0 i0) :=
    { le := Gh.Le.refl _
      bal_mono := fun j B hB => by
        by_cases hj : j = a
        · subst hj
          obtain ⟨cp0, h0, rfl⟩ := balOf_some_inv hB
          refine ⟨_, balOf_some hcpA, ?_⟩
          rcases hold with ⟨hn, -⟩ | ⟨c0, hc0, hb, -⟩
          · rw [hn] at h0; cases h0
          · rw [hc0] at h0; cases h0; rw [hb]; exact Int.le_refl _
        · rw [hbalN j hj]; exact ⟨B, hB, Int.le_refl B⟩
      acc_new := fun _ _ _ hn hno => absurd hn hno
      eq_new := fun _ hn hno => absurd hn hno
      fast_new := fun _ hn hno => absurd hn hno
      fast_cre := A.fast_cre
      fast_eq := A.fast_eq
      fast_noprop := A.fast_noprop }
  have hI0 : InstOk c1 G q0 i0 :=
    { ainv := ainv_evolve_same A E0
      copies := fun j cp' hc => by
        by_cases hj : j = a
        · subst hj; rw [hcpA] at hc; cases hc; exact copyOk_commit IO hcs hch hold
        · rw [cpOf_postN hst hj] at hc
          exact copyOk_narrow E0 (Narrow.refl _ _) (IO.copies j cp' hc)
      noCopy := fun j hc => by
        by_cases hj : j = a
        · subst hj; rw [hcpA] at hc; cases hc
        · rw [cpOf_postN hst hj] at hc; exact IO.noCopy j hc
      fastL := fun w hw => by
        by_cases hLa : rowOf q0 = a
        · exact ⟨cp, by rw [hLa]; exact hcpA, Or.inl hcs⟩
        · obtain ⟨cpL, hL, hLc⟩ := IO.fastL w hw
          exact ⟨cpL, by rw [cpOf_postN hst hLa]; exact hL, hLc⟩
      leaderCopy := fun _ => by
        by_cases hLa : rowOf q0 = a
        · exact ⟨cp, by rw [hLa]; exact hcpA, by rw [hcs]; exact com_ne.1⟩
        · obtain ⟨cpL, hL, hne⟩ := IO.leaderCopy (chosen_copy IO hch)
          exact ⟨cpL, by rw [cpOf_postN hst hLa]; exact hL, hne⟩
      ownMono := fun b' R' hR' hp => by
        obtain ⟨B, hB, hle⟩ := IO.ownMono b' R' hR' hp
        obtain ⟨B', hB', hle'⟩ := E0.bal_mono R' B hB
        exact ⟨B', hB', Int.le_trans hle hle'⟩
      fresh := fun hn => absurd ((hn a).symm.trans hcpA) (by simp) }
  refine inv_frame I hst hinf hid hcp (fun _ _ _ => rfl) hcrtA hcrtLe hbelow E0 (fun _ h => h) hI0
    ?_ ?_ hO hlen (fun _ _ _ => ⟨cp, hcp0, by rw [hcs]; exact com_ne.1⟩)
  · intro cp' h1 _; rw [hcp0] at h1; cases h1; exact Or.inr (Or.inr (Or.inl hcs))
  · intro cp' lb' h1 _ _ hn _; rw [hcp0] at h1; cases h1; exact absurd (Or.inl hcs) hn

/-- **`handleCommit`** keeps `CInv` (same history). -/
theorem inv_commit_core {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : ECommitM} {s' : RState}
    {o : List Out} (I : CInv c G)
    (hst : c1.st = fun j => if j = a then s' else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv (.msg (.commit m))) (c.inflight j) else c.inflight j) ++
        sentTo gNet j o)
    (hm : Msg.commit m ∈ c.inflight a) (h : stepCommit (c.st a) m = .ok (s', o)) :
    ∃ G', CInv c1 G' ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i) := by
  have hch : Chosen (G m.replica m.inst) m.valA := I.msgs a _ hm
  have hbelow := I.msgBelow a _ m.replica m.inst hm rfl
  obtain ⟨rfl, t, hcb, hr⟩ := stepCommit_shape h
  obtain ⟨ht1, ht2, ht3, ht4, ht5⟩ := crtB_facts I hcb hbelow
  have hO : ∀ d m', Out.send d m' ∈ ([] : List Out) → isPP m' = false ∧ MsgOk c1 G d m' ∧
      ∀ q j, msgInst m' = some (q, j) → q = m.replica ∧ j = m.inst := fun d m h => by simp at h
  rcases hr with ⟨c0, -, -, rfl⟩ | ⟨cp, e1, e2, e3, hcs, hval, hold⟩
  · exact ⟨G, inv_frame_same I hst hinf ht1 ht2 ht3 ht4 hbelow hO ht5⟩
  have hcrt : ∀ p, s'.crt p = t.crt p := fun p => by simp only [RState.crt, e3]
  refine ⟨G, inv_commit_copy (q0 := m.replica) (i0 := m.inst) (cp := cp) I hst hinf
    (e2.trans ht1) (fun q i hn => by rw [e1, setInst_inst, if_neg hn, ht2])
    (by rw [e1, setInst_inst, if_pos ⟨rfl, rfl⟩]) (by rw [hcrt]; exact ht3)
    (fun r => by rw [hcrt]; exact ht4 r) hbelow hcs (by rw [hval]; exact hch) ?_ hO (by rw [e3]; exact ht5)⟩
  rcases hold with ⟨hn, hb, hv⟩ | ⟨c0, hc0, -, hb, hv⟩
  · exact Or.inl ⟨hn, hb, hv⟩
  · exact Or.inr ⟨c0, hc0, hb, hv⟩

end Perennial.gryff.pureA.A1d
