/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/StepPreAccept.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1c, internal: **`handlePreAccept` keeps the agreement invariant** (`inv_preAccept_core`, used
by `Inv.lean`'s `inv_preAccept`).

By `stepPreAccept_cases`: an early return and a NACK leave the copies alone (`inv_frame_same`);
the update of replica `a`'s copy of `(q, i)` (`q = m.replica`, `i = m.inst`, leader `L`) goes through
`SPA.inv_frame` with the history extended by `eq a` when the copy is pre-accepted unchanged at
ballot 0 (G41: PREACCEPTED_EQ iff the attributes equal the PreAccept's):
* at ballot 0, `a` had no copy (`MsgOk`: its copy would be past ballot 0 or accepted); the new copy
  carries the creation value when unchanged (`updAttr_deps`: the rows `≥ 3` are kept, `depsEqual`
  compares the others); the reply carries the creation's rows `L`, `≥ 3`, its length, and its base
  unless a larger tag replaced it; the PreAcceptOK and an OK reply with the creation's attributes
  come with the new `eq a`;
* at a ballot `b > 0` (a restart by `R ≠ a`), the copy is pre-accepted at `b` (a restart, `RstBelow`
  for `eqTrack`); an OK reply records `Own b R` and the restart;
* the ballot-0 PreAccept consumed was the only one in flight to `a` (`count = 1`), so no ballot-0
  PreAccept to `a` about `(q, i)` remains.
-/
module

public import Dsverify.Proof.gryff.PureA.StepPreAcceptCases

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.SPA

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn

/-! ## Helpers -/

theorem step1_of {c c1 : Cfg gNet} {a : Fin 3} {e : Ev} {m0 : Msg} {s' : RState} {o : List Out}
    {q0 i0 : w32} (he : gNet.recv e = some m0)
    (hst : c1.st = fun j => if j = a then s' else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv e) (c.inflight j) else c.inflight j) ++ sentTo gNet j o)
    (hid : s'.id = (c.st a).id)
    (hinst : ∀ q i, ¬ (q = q0 ∧ i = i0) → s'.inst q i = (c.st a).inst q i)
    (hlen : s'.crtInstance.length = (c.st a).crtInstance.length)
    (hcrtA : s'.crt (rid32 a) = (c.st a).crt (rid32 a))
    (hcrtLe : ∀ r : Fin 3, sint.Z (s'.crt (rid32 r)) ≤ sint.Z ((c.st r).crt (rid32 r))) :
    Step1 c c1 a q0 i0 m0 o := by
  have hstA : c1.st a = s' := by rw [hst]; exact if_pos rfl
  refine ⟨fun j hj => by rw [hst]; exact if_neg hj, fun j => ?_, by rw [hstA]; exact hid,
    fun q i h => by rw [hstA]; exact hinst q i h, by rw [hstA]; exact hlen, by rw [hstA]; exact hcrtA,
    fun r => by rw [hstA]; exact hcrtLe r⟩
  rw [hinf]
  simp only [he, consume]

theorem cpOf_postA {c c1 : Cfg gNet} {a : Fin 3} {s' : RState}
    (hst : c1.st = fun j => if j = a then s' else c.st j) (q i : w32) :
    cpOf c1 a q i = s'.inst q i := by
  have : c1.st a = s' := by rw [hst]; exact if_pos rfl
  simp only [cpOf, this]

theorem cpOf_postN {c c1 : Cfg gNet} {a j : Fin 3} {s' : RState}
    (hst : c1.st = fun j => if j = a then s' else c.st j) (h : j ≠ a) (q i : w32) :
    cpOf c1 j q i = cpOf c j q i := by
  have : c1.st j = c.st j := by rw [hst]; exact if_neg h
  simp only [cpOf, this]

theorem pa_nonneg {c : Cfg gNet} {G : GG} {d : Fin 3} {m : PreAcceptM}
    (hM : MsgOk c G d (.preAccept m)) : 0 ≤ sint.Z m.ballot := by
  by_cases h0 : m.ballot = 0
  · rw [h0]; decide
  · exact Int.le_of_lt (hM.2 h0).1

theorem notCAE_pre {c : Cfg gNet} {G : GG} {q i : w32} {a : Fin 3} {cp : Copy}
    (hC : CopyOk c G q i a cp) (h : ¬ isCAE cp) : cp.status = St.NONE ∨ isPre cp.status := by
  rcases hC.stOk with h1 | h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exact absurd (Or.inr (Or.inl h1)) h
  · exact absurd (Or.inl h1) h
  · exact absurd (Or.inr (Or.inr h1)) h

theorem deps_ext {d1 d2 : Deps} (hl : d1.length = d2.length) (h : ∀ k, d1.at k = d2.at k) :
    d1 = d2 := by
  apply List.ext_getElem hl
  intro k h1 h2
  have := h k
  simp only [Deps.at, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some] at this
  exact this

theorem depsEqual_at {d1 d2 : Deps} (h : depsEqual d1 d2 = true) {k : Nat} (hk : k < 5) :
    d1.at k = d2.at k := by
  simp only [depsEqual, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h k hk

theorem depsEqual_refl (d : Deps) : depsEqual d d = true := by
  simp [depsEqual]

/-- An `updateAttributes` result at a non-leader equal (as `depsEqual`) to the PreAccept's deps is
the PreAccept's deps. -/
theorem deps_of_upd {s : RState} {cmds : List Cmd} {seq0 : w32} {deps0 : Deps} {r : w32} {seq : w32}
    {deps : Deps} {ch : Bool} (h : updateAttributes s cmds seq0 deps0 r = some (seq, deps, ch))
    (he : depsEqual deps deps0 = true) : deps = deps0 := by
  obtain ⟨hl, hk⟩ := updAttr_deps h
  refine deps_ext hl fun k => ?_
  by_cases k3 : 3 ≤ k
  · exact hk k (Or.inl k3)
  · exact depsEqual_at he (by omega)

theorem count_erase_one {l : List Msg} {x : Msg} (h : l.count x = 1) : x ∉ l.erase x := by
  intro hx
  have h1 := List.count_pos_iff.2 hx
  rw [List.count_erase_self] at h1
  omega

/-- `AInv` for a history adding only unchanged pre-accepts, along an evolution. -/
theorem ainv_eqOnly {g : Gh Val} {bal bal' : Fin 3 → Option Int} {L : Fin 3} {e : Fin 3 → Prop}
    (I : AInv g bal L) (E : Evolve L g bal { g with eq := e } bal') :
    AInv { g with eq := e } bal' L where
  prop_uniq := I.prop_uniq
  acc_prop := I.acc_prop
  prop_nonneg := I.prop_nonneg
  prop_safe b v h := safeAt_evolve E (I.prop_safe b v h)
  rst_safe b h := safeAll_evolve E (I.rst_safe b h)
  cre_uniq := I.cre_uniq
  fast_cre := I.fast_cre
  fast_eq := E.fast_eq
  fast_noprop := I.fast_noprop

theorem stPre_ne : St.PREACCEPTED ≠ St.NONE ∧ St.PREACCEPTED_EQ ≠ St.NONE ∧
    St.PREACCEPTED ≠ St.ACCEPTED ∧ St.PREACCEPTED_EQ ≠ St.ACCEPTED ∧
    St.PREACCEPTED ≠ St.COMMITTED ∧ St.PREACCEPTED_EQ ≠ St.COMMITTED ∧
    St.PREACCEPTED ≠ St.EXECUTED ∧ St.PREACCEPTED_EQ ≠ St.EXECUTED := by decide

theorem pre_of {x : w8} (h : x = St.PREACCEPTED ∨ x = St.PREACCEPTED_EQ) :
    isPre x ∧ x ≠ St.NONE ∧ x ≠ St.ACCEPTED ∧ ¬ isCommitted x := by
  rcases h with rfl | rfl
  · exact ⟨Or.inl rfl, stPre_ne.1, stPre_ne.2.2.1, fun h => h.elim stPre_ne.2.2.2.2.1 stPre_ne.2.2.2.2.2.2.1⟩
  · exact ⟨Or.inr rfl, stPre_ne.2.1, stPre_ne.2.2.2.1,
      fun h => h.elim stPre_ne.2.2.2.2.2.1 stPre_ne.2.2.2.2.2.2.2⟩

theorem sendP_dst {s : RState} {R : Fin 3} {msg : Msg} {x : Out} (h : SendP s (rid32 R) msg x) :
    x = .send R msg := by
  obtain ⟨-, d, hd, rfl⟩ := h
  rw [dstOf_rid] at hd; cases hd; rfl

theorem storeVT_t (s : RState) : s.storeVT.t = s.tag := rfl

/-! ## The update of the copy -/

/-- The history after the update: `eq a` when the new copy is unchanged at ballot 0. -/
def gUpd (g : Gh Val) (a : Fin 3) (cp : Copy) (b : w32) : Gh Val :=
  { g with eq := fun x => g.eq x ∨ (x = a ∧ cp.status = St.PREACCEPTED_EQ ∧ b = 0) }

theorem z0 : sint.Z (0 : w32) = 0 := by decide

theorem mem_sentTo {o : List Out} {d : Fin 3} {m : Msg} (h : m ∈ sentTo gNet d o) :
    Out.send d m ∈ o := by
  unfold sentTo at h
  obtain ⟨y, hy, hy'⟩ := List.mem_filterMap.1 h
  cases y with
  | send d' m' =>
    simp only at hy'
    split at hy'
    · cases hy'; subst_vars; exact hy
    · cases hy'
  | ext x => cases hy'

theorem mem_sent1 {d0 d : Fin 3} {msg y : Msg} (h : y ∈ sentTo gNet d [Out.send d0 msg]) :
    d0 = d ∧ y = msg := by
  have := List.mem_singleton.1 (mem_sentTo h)
  cases this; exact ⟨rfl, rfl⟩

/-- A step of `a` leaving its copy of `(q0, i0)` (and every other) alone, sending no PreAccept:
the history is unchanged. -/
theorem inv_same {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {q0 i0 : w32} {m0 : Msg} {o : List Out}
    (I : CInv c G) (S : Step1 c c1 a q0 i0 m0 o) (hcpA : cpOf c1 a q0 i0 = cpOf c a q0 i0)
    (hbelow : rowOk q0 = true ∧ 0 ≤ sint.Z i0 ∧ sint.Z i0 < sint.Z ((c.st (rowOf q0)).crt q0))
    (hnew : ∀ d x, x ∈ sentTo gNet d o → MsgOk c1 G d x ∧
      (∀ q j, msgInst x = some (q, j) →
        rowOk q = true ∧ 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ((c.st (rowOf q)).crt q)) ∧
      (∀ y, x ≠ .preAccept y) ∧ (∀ q i b, isPrepareAt q i b x = false) ∧
      (∀ q i b Y, isOKReplyAt q i b Y x = false)) :
    CInv c1 G ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G q i) (balOf c1 q i) := by
  have hcp : ∀ j, cpOf c1 j q0 i0 = cpOf c j q0 i0 := fun j => by
    by_cases hj : j = a
    · subst hj; exact hcpA
    · exact S.cp j q0 i0 (fun h => hj h.1)
  refine inv_frame I S (fun _ _ _ => rfl) (by rw [balOf_congr hcp]; exact Evolve.refl (I.inst _ _).ainv)
    (instOk_congr hcp (I.inst _ _)) (fun _ _ => hbelow) hnew ?_ ?_ ?_
  · intro x hx hb hr hi cp hc
    rw [hcpA] at hc
    have hx' : Msg.preAccept x ∈ c.inflight a := by
      rw [S.inf a] at hx
      rcases List.mem_append.1 hx with h | h
      · exact S.old h
      · exact absurd rfl ((hnew a _ h).2.2.1 x)
    have := ((I.msgs a _ hx').1 hb).2.2.2.1
    rw [hr, hi] at this
    exact this cp hc
  · intro cp lb hc h1 h2 h3 _
    rw [hcpA] at hc; exact ⟨cp, lb, hc, h1, h2, h3, rfl, rfl⟩
  · intro cp hc hne; rw [hcpA]; exact ⟨cp, hc, hne⟩

set_option maxHeartbeats 1000000 in
/-- The update of `a`'s copy of `(m.replica, m.inst)` (`PAUpd`). -/
theorem inv_preAccept_upd {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : PreAcceptM} {s1 : RState}
    {cp : Copy} {x : Out} (I : CInv c G)
    (hst : c1.st = fun j => if j = a then
      updateConflicts (s1.setInst m.replica m.inst cp) m.cmds m.replica m.inst m.seq else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv (.msg (.preAccept m))) (c.inflight j) else c.inflight j) ++
        sentTo gNet j [x])
    (hm : Msg.preAccept m ∈ c.inflight a)
    (hb : CrtB (c.st a) s1 m.replica m.inst) (U : PAUpd (c.st a) m s1 cp x) :
    ∃ G', CInv c1 G' ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i) := by
  have hM := I.msgs a _ hm
  have hbelow := I.msgBelow a _ m.replica m.inst hm rfl
  have hrow := hbelow.1
  obtain ⟨f1, f2, f3, f4, f5⟩ := crtB_facts I hb hbelow
  have hs'inst : (updateConflicts (s1.setInst m.replica m.inst cp) m.cmds m.replica m.inst m.seq).inst =
      (s1.setInst m.replica m.inst cp).inst := (updateConflicts_inst _ _ _ _ _).1
  have hs'crt : ∀ p, (updateConflicts (s1.setInst m.replica m.inst cp) m.cmds m.replica m.inst
      m.seq).crt p = s1.crt p := fun p => by
    simp only [RState.crt, (updateConflicts_inst _ _ _ _ _).2.2]; rfl
  have S : Step1 c c1 a m.replica m.inst (.preAccept m) [x] :=
    step1_of rfl hst hinf ((uc_id _ _ _ _ _).trans f1)
      (fun q i h => by rw [hs'inst, setInst_other _ _ h, f2])
      (by rw [(updateConflicts_inst _ _ _ _ _).2.2]; exact f5) (by rw [hs'crt]; exact f3) (fun r => by rw [hs'crt]; exact f4 r)
  have hcpA : cpOf c1 a m.replica m.inst = some cp := by
    rw [cpOf_postA hst, hs'inst]; exact setInst_self _ _ _ _
  have hnn := pa_nonneg hM
  obtain ⟨hM0, hM1⟩ := hM
  have hpre := pre_of U.st1
  obtain ⟨ch, hua⟩ := U.ua
  -- the old copy
  have hold : ∀ c0, cpOf c a m.replica m.inst = some c0 →
      sint.Z c0.ballot ≤ sint.Z m.ballot ∧ ¬ isCAE c0 := by
    intro c0 hc0
    change (c.st a).inst m.replica m.inst = some c0 at hc0
    rcases U.old with hn | ⟨c0', hc0', hcae, hslt, -⟩
    · rw [hn] at hc0; cases hc0
    · rw [hc0'] at hc0; cases hc0
      refine ⟨?_, hcae⟩
      have : ¬ sint.Z m.ballot < sint.Z c0.ballot := fun h => by
        rw [(slt_iff _ _).2 h] at hslt; cases hslt
      omega
  have hnone0 : m.ballot = 0 → cpOf c a m.replica m.inst = none := by
    intro h0
    cases hc0 : cpOf c a m.replica m.inst with
    | none => rfl
    | some c0 =>
      exfalso
      obtain ⟨k1, k2⟩ := hold c0 hc0
      rcases (hM0 h0).2.2.2.1 c0 hc0 with h | h | h
      · rw [h0, z0] at k1; omega
      · exact k2 (Or.inr (Or.inl h))
      · rcases h with h | h
        · exact k2 (Or.inl h)
        · exact k2 (Or.inr (Or.inr h))
  have ownNot : ¬ Own (sint.Z m.ballot) a := by
    intro hown
    by_cases h0 : m.ballot = 0
    · rw [h0, z0] at hown; have := own_ge hown; omega
    · obtain ⟨-, -, R, hR, -, hRa⟩ := hM1 h0
      exact hRa (own_unique hR hown)
  have oldNoVotes : ∀ b u, ¬ (G m.replica m.inst).acc a b u := by
    intro b u
    cases hc0 : cpOf c a m.replica m.inst with
    | none => exact ((I.inst _ _).noCopy a hc0).1 b u
    | some c0 =>
      have hC := (I.inst _ _).copies a c0 hc0
      exact hC.noVotes (notCAE_pre hC (hold c0 hc0).2) b u
  have hasCopy : ∃ y cp0, cpOf c y m.replica m.inst = some cp0 := by
    by_cases h0 : m.ballot = 0
    · obtain ⟨-, -, hcre, -, -⟩ := hM0 h0
      refine Classical.byContradiction fun hn => ?_
      have hall : ∀ y, cpOf c y m.replica m.inst = none := fun y => by
        cases e : cpOf c y m.replica m.inst with
        | none => rfl
        | some cp0 => exact absurd ⟨y, cp0, e⟩ hn
      exact ((I.inst _ _).fresh hall).1 _ hcre
    · obtain ⟨-, hrst, R, hown, -, -⟩ := hM1 h0
      obtain ⟨B, hB, -⟩ := (I.inst _ _).ownMono _ R hown (Or.inl hrst)
      obtain ⟨cp0, hcp0, -⟩ := balOf_some_inv hB
      exact ⟨R, cp0, hcp0⟩
  have hbalA : balOf c1 m.replica m.inst a = some (sint.Z m.ballot) := by
    rw [balOf_some hcpA, U.ballot]
  have hbalN : ∀ y, y ≠ a → balOf c1 m.replica m.inst y = balOf c m.replica m.inst y :=
    fun y hy => by simp only [balOf, cpOf_postN hst hy]
  -- the history
  have E0 : Evolve (rowOf m.replica) (G m.replica m.inst) (balOf c m.replica m.inst)
      (gUpd (G m.replica m.inst) a cp m.ballot) (balOf c1 m.replica m.inst) :=
    { le := ⟨fun _ _ _ h => h, fun _ _ h => h, fun _ h => h, fun _ h => h, fun _ h => Or.inl h,
             fun _ h => h⟩
      bal_mono := by
        intro y B hB
        by_cases hy : y = a
        · subst hy
          obtain ⟨c0, hc0, rfl⟩ := balOf_some_inv hB
          exact ⟨_, hbalA, (hold c0 hc0).1⟩
        · exact ⟨B, by rw [hbalN y hy]; exact hB, Int.le_refl B⟩
      acc_new := fun _ _ _ h hn => absurd h hn
      eq_new := by
        intro y hy hn B hB
        rcases hy with hy | ⟨rfl, -, h0⟩
        · exact absurd hy hn
        · obtain ⟨c0, hc0, rfl⟩ := balOf_some_inv hB
          rw [hnone0 h0] at hc0; cases hc0
      fast_new := fun _ h hn => absurd h hn
      fast_cre := (I.inst _ _).ainv.fast_cre
      fast_eq := fun v hv =>
        let ⟨y, hy, he⟩ := (I.inst _ _).ainv.fast_eq v hv
        ⟨y, hy, Or.inl he⟩
      fast_noprop := (I.inst _ _).ainv.fast_noprop }
  have GO : GOnly a (rowOf m.replica) (G m.replica m.inst) (gUpd (G m.replica m.inst) a cp m.ballot) :=
    ⟨fun _ _ _ h hn => absurd h hn, fun _ _ h hn => absurd h hn, fun _ h => h, fun _ h => h,
     fun _ h hn => h.elim (fun h' => absurd h' hn) (fun h' => h'.1), fun _ h hn => absurd h hn⟩
  obtain ⟨G', hG'at, hG'ne⟩ : ∃ G' : GG, G' m.replica m.inst = gUpd (G m.replica m.inst) a cp m.ballot ∧
      ∀ q i, ¬ (q = m.replica ∧ i = m.inst) → G' q i = G q i :=
    ⟨ggSet G _ _ _, ggSet_at _ _ _ _, fun _ _ h => ggSet_ne _ _ h⟩
  -- the new copy
  have hnewC : CopyOk c1 (fun _ _ => gUpd (G m.replica m.inst) a cp m.ballot) m.replica m.inst a cp :=
    { nonneg := by rw [U.ballot]; exact hnn
      ballotForm := by
        rw [U.ballot]
        by_cases h0 : m.ballot = 0
        · exact Or.inl h0
        · obtain ⟨-, -, R, hown, -⟩ := hM1 h0; exact Or.inr ⟨R, hown⟩
      vbalLe := by rw [U.vbal, U.ballot]; exact Int.le_refl _
      stOk := Or.inr (Or.inl hpre.1)
      noVotes := fun _ b u hu => oldNoVotes b u hu
      accVote := fun h => absurd h hpre.2.2.1
      committed := fun h => absurd h hpre.2.2.2
      rstVbal := fun _ hv => by
        rw [U.vbal] at hv ⊢; exact ⟨(hM1 hv).1, (hM1 hv).2.1⟩
      eqCre := by
        intro hs hv _
        rw [U.vbal] at hv
        obtain ⟨-, -, hcre, -, -⟩ := hM0 hv
        obtain ⟨e1, e2, e3⟩ := U.st2 hs
        have hbase : cp.base = m.base := by
          rcases U.base with ⟨-, h⟩ | ⟨h, -⟩
          · exact h
          · rw [e3] at h; cases h
        have hval : cp.valA = (m.cmds, m.seq, m.deps, m.base) := by
          simp only [Copy.valA, U.cmds, e1, deps_of_upd hua e2, hbase]
        show (G m.replica m.inst).cre cp.valA
        rw [hval]; exact hcre
      leader0 := by
        intro haL hb0 _
        rw [U.ballot] at hb0; exact absurd haL (hM0 hb0).1
      ownFresh := by
        intro _ hown; rw [U.ballot] at hown; exact absurd hown ownNot
      preparing := by
        intro _ _ _ _ hown; rw [U.ballot] at hown; exact absurd hown ownNot
      eqTrack := by
        intro _ he
        rcases he with he | ⟨-, hs, h0⟩
        · by_cases h0 : m.ballot = 0
          · exact absurd he ((I.inst _ _).noCopy a (hnone0 h0)).2
          · refine Or.inr (Or.inr (Or.inr ?_))
            rw [U.ballot]; exact ⟨_, (hM1 h0).1, Int.le_refl _, (hM1 h0).2.1⟩
        · exact Or.inr (Or.inr (Or.inl ⟨hs, by rw [U.vbal]; exact h0⟩)) }
  have hI : InstOk c1 (fun _ _ => gUpd (G m.replica m.inst) a cp m.ballot) m.replica m.inst :=
    { ainv := ainv_eqOnly (I.inst _ _).ainv E0
      copies := by
        intro y cp' hc'
        by_cases hy : y = a
        · subst hy; rw [hcpA] at hc'; cases hc'; exact hnewC
        · rw [cpOf_postN hst hy] at hc'
          exact copyOk_keep ((I.inst _ _).copies y cp' hc') E0 GO hy
      noCopy := by
        intro y hy
        have hya : y ≠ a := by rintro rfl; rw [hcpA] at hy; cases hy
        rw [cpOf_postN hst hya] at hy
        obtain ⟨k1, k2⟩ := (I.inst _ _).noCopy y hy
        exact ⟨k1, fun he => he.elim k2 (fun h => hya h.1)⟩
      fastL := by
        intro v hv
        obtain ⟨cpL, hL, hcom⟩ := (I.inst _ _).fastL v hv
        by_cases hLa : rowOf m.replica = a
        · exfalso
          rw [hLa] at hL
          exact (hold cpL hL).2 (hcom.elim Or.inl (fun h => Or.inr (Or.inr h)))
        · exact ⟨cpL, by rw [cpOf_postN hst hLa]; exact hL, hcom⟩
      leaderCopy := by
        intro _
        by_cases hLa : rowOf m.replica = a
        · rw [hLa]; exact ⟨cp, hcpA, hpre.2.1⟩
        · obtain ⟨cpL, hL, hne⟩ := (I.inst _ _).leaderCopy hasCopy
          exact ⟨cpL, by rw [cpOf_postN hst hLa]; exact hL, hne⟩
      ownMono := by
        intro b R hR hp
        obtain ⟨B, hB, hle⟩ := (I.inst _ _).ownMono b R hR hp
        obtain ⟨B', hB', hle'⟩ := E0.bal_mono R B hB
        exact ⟨B', hB', Int.le_trans hle hle'⟩
      fresh := fun hn => by have := (hn a).symm.trans hcpA; cases this }
  refine ⟨G', inv_frame I S hG'ne (by rw [hG'at]; exact E0) (instOk_G hG'at hI)
    (fun _ _ => hbelow) ?_ ?_ ?_ ?_⟩
  · -- the reply
    intro d y hy
    rcases U.out with hx | ⟨hEQ, -, hinit, hx⟩
    · obtain ⟨-, d0, hd0, rfl⟩ := hx
      obtain ⟨rfl, rfl⟩ := mem_sent1 hy
      refine ⟨⟨fun hb0 => ?_, fun hb0 _ => ?_⟩, ?_, fun z h => Msg.noConfusion h, fun _ _ _ => rfl,
        fun _ _ _ _ => rfl⟩
      · change m.ballot = 0 at hb0
        obtain ⟨haL, hlead, hcre, -, -⟩ := hM0 hb0
        rw [hlead, dstOf_rid] at hd0; cases hd0
        have e : G' (okOf m cp).replica (okOf m cp).inst = gUpd (G m.replica m.inst) a cp m.ballot :=
          hG'at
        rw [e]
        refine ⟨rfl, fun _ hca => ?_, fun _ => ⟨_, hcre, (updAttr_deps hua).1, fun k hk => ?_, ?_⟩⟩
        · obtain ⟨v, hv, hv2⟩ := hca
          have := (I.inst _ _).ainv.cre_uniq _ _ hv hcre
          subst this
          simp only [okOf, Prod.mk.injEq] at hv2
          obtain ⟨e1, e2, e3⟩ := hv2
          have hgt : s1.tag.gt m.base.t = false := by
            rcases U.base with ⟨h, -⟩ | ⟨h, h'⟩
            · exact h
            · rw [e3, h', storeVT_t, tag_gt_irrefl] at h; cases h
          have hs := U.st3 e1.symm (by rw [← e2]; exact depsEqual_refl _) hgt
          exact ⟨a, haL, Or.inr ⟨rfl, hs, hb0⟩⟩
        · rcases hk with hk | hk
          · refine (updAttr_deps hua).2 k (Or.inr ⟨?_, ?_⟩)
            · rw [f1, I.ids a, ← rid_rowOf hrow]; exact rid_ne (Ne.symm (Ne.symm haL))
            · rw [hk, ← rid_rowOf hrow]; rfl
          · exact (updAttr_deps hua).2 k (Or.inl hk)
        · intro hgt
          rcases U.base with ⟨-, h⟩ | ⟨h, h'⟩
          · exact h
          · change cp.base.t.gt m.base.t = false at hgt
            rw [h', storeVT_t, h] at hgt; cases hgt
      · change m.ballot ≠ 0 at hb0
        obtain ⟨-, hrst, R, hown, hlead, -⟩ := hM1 hb0
        rw [hlead, dstOf_rid] at hd0; cases hd0
        have e : G' (okOf m cp).replica (okOf m cp).inst = gUpd (G m.replica m.inst) a cp m.ballot :=
          hG'at
        rw [e]; exact ⟨hown, hrst⟩
      · intro q' j h
        simp only [msgInst, okOf, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact hbelow
    · have hb0 : m.ballot = 0 := by
        refine Classical.byContradiction fun h0 => ?_
        obtain ⟨-, -, R, hown, -⟩ := hM1 h0
        have := own_ge hown; have := init_lt hinit; omega
      obtain ⟨haL, hlead, -, -, -⟩ := hM0 hb0
      obtain ⟨-, d0, hd0, rfl⟩ := hx
      obtain ⟨rfl, rfl⟩ := mem_sent1 hy
      rw [hlead, dstOf_rid] at hd0; cases hd0
      refine ⟨⟨a, haL, ?_⟩, (fun _ _ h => by simp [msgInst] at h), fun z h => Msg.noConfusion h,
        fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
      show (G' (rid32 (rowOf m.replica)) m.inst).eq a
      rw [rid_rowOf hrow, hG'at]
      exact Or.inr ⟨rfl, hEQ, hb0⟩
  · -- no ballot-0 PreAccept to `a` about the instance remains
    intro y hy hy0 hyr hyi cp' hc'
    rw [hcpA] at hc'; cases hc'
    by_cases h0 : m.ballot = 0
    · exfalso
      rw [S.inf a] at hy
      rcases List.mem_append.1 hy with hy' | hy'
      · rw [if_pos rfl] at hy'
        have hyc := List.mem_of_mem_erase hy'
        obtain ⟨-, hly, hcy, -, -⟩ := (I.msgs a _ hyc).1 hy0
        obtain ⟨-, hlm, hcm, -, hcnt⟩ := hM0 h0
        rw [hyr, hyi] at hcy; rw [hyr] at hly
        have hv := (I.inst _ _).ainv.cre_uniq _ _ hcy hcm
        simp only [Prod.mk.injEq] at hv
        obtain ⟨v1, v2, v3, v4⟩ := hv
        have : y = m := by
          cases y; cases m
          simp only at *
          subst_vars; rfl
        subst this
        exact count_erase_one hcnt hy'
      · rcases U.out with hx | ⟨-, -, -, hx⟩ <;>
        · obtain ⟨-, d0, -, rfl⟩ := hx
          obtain ⟨-, h⟩ := mem_sent1 hy'
          exact Msg.noConfusion h
    · left; rw [U.ballot]; exact (hM1 h0).1
  · intro cp' lb hc' _ _ _ hown
    rw [hcpA] at hc'; cases hc'
    rw [U.ballot] at hown; exact absurd hown ownNot
  · intro _ _ _; exact ⟨cp, hcpA, hpre.2.1⟩

/-- **`handlePreAccept` keeps the invariant.** -/
theorem inv_preAccept_core {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : PreAcceptM} {s' : RState}
    {o : List Out} (I : CInv c G)
    (hst : c1.st = fun j => if j = a then s' else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv (.msg (.preAccept m))) (c.inflight j) else c.inflight j) ++
        sentTo gNet j o)
    (hm : Msg.preAccept m ∈ c.inflight a) (h : stepPreAccept (c.st a) m = .ok (s', o)) :
    ∃ G', CInv c1 G' ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i) := by
  obtain ⟨-, hcases⟩ := stepPreAccept_cases h
  have hbelow := I.msgBelow a _ m.replica m.inst hm rfl
  rcases hcases with ⟨rfl, rfl⟩ | ⟨s1, c0, x, hb, hc, -, hslt, rfl, rfl, hx⟩ |
    ⟨s1, cp, x, hb, rfl, rfl, U⟩
  · refine ⟨G, inv_same I (step1_of rfl hst hinf rfl (fun _ _ _ => rfl) rfl rfl
      (fun r => I.crtOwn a r)) (by rw [cpOf_postA hst]; rfl) hbelow (fun _ _ h => absurd h List.not_mem_nil)⟩
  · obtain ⟨f1, f2, f3, f4, f5⟩ := crtB_facts I hb hbelow
    refine ⟨G, inv_same I (step1_of rfl hst hinf f1 (fun q i _ => by rw [f2]) f5 f3 f4)
      (by rw [cpOf_postA hst, f2]; rfl) hbelow ?_⟩
    intro d y hy
    obtain ⟨-, d0, -, rfl⟩ := hx
    obtain ⟨rfl, rfl⟩ := mem_sent1 hy
    have hpos : 0 < sint.Z c0.ballot := by
      have := (slt_iff _ _).1 hslt; have := pa_nonneg (I.msgs a _ hm); omega
    refine ⟨⟨fun hb0 => ?_, fun _ hok => absurd rfl hok⟩, fun q j h => ?_, fun z h => Msg.noConfusion h,
      fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
    · change c0.ballot = 0 at hb0
      rw [hb0, z0] at hpos; omega
    · simp only [msgInst, nackOf, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hbelow
  · exact inv_preAccept_upd I hst hinf hm hb U

end Perennial.gryff.pureA.SPA
