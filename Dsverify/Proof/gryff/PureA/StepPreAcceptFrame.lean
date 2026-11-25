/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/StepPreAcceptFrame.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1c, internal: a frame for the steps `inv_preAccept`, `inv_preAcceptReply`, `inv_preAcceptOK`
(`notes/unit-A1c.md`).

* small facts: `rowOf_rid`, `rid_rowOf`, `dstOf_rid`, `own_unique`, `own_ge`, `init_lt`,
  `tag_gt_irrefl`; `updAttr_deps` (`updateAttributes` touches only rows 0-2, not the leader's row at
  a non-leader), `merge_eq` (`mergeAttributes` reporting `equal` changes nothing and compared the
  rows other than the merger's);
* `GOnly R`: the history grows only by facts about acceptor `R` (the stepping replica);
  `copyOk_keep`: an unchanged copy of another acceptor keeps `CopyOk`;
* `msgOk_evolve`: `MsgOk` is monotone along `Evolve` (but for a ballot-0 PreAccept's receiver copy
  and multiplicity);
* `inv_frame`: a step of replica `a` touching only its copy of instance `(q0, i0)` (and `crt`),
  consuming `m0`, sending `o`, keeps `CInv` given the new `InstOk` at `(q0, i0)` and the new
  messages' facts.

Everything lives in `pureA.SPA` (so that the sibling units' helpers do not clash).
-/
module

public import Dsverify.Proof.gryff.PureA.Exec

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.SPA

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn

/-! ## Small facts -/

theorem rowOf_rid (a : Fin 3) : rowOf (rid32 a) = a := by
  revert a; decide

theorem dstOf_rid (a : Fin 3) : dstOf (rid32 a) = some a := by
  revert a; decide

theorem rid_rowOf {q : w32} (h : rowOk q = true) : rid32 (rowOf q) = q := by
  simp only [rowOk, decide_eq_true_eq] at h
  unfold rowOf rid32
  rw [dif_pos h]
  simp only
  word

theorem rid_ne {a b : Fin 3} (h : a ≠ b) : rid32 a ≠ rid32 b := by
  revert a b; decide

theorem own_unique {b : Int} {R R' : Fin 3} (h : Own b R) (h' : Own b R') : R = R' := by
  obtain ⟨k, hk, rfl⟩ := h; obtain ⟨k', hk', e⟩ := h'
  have := R.isLt; have := R'.isLt
  apply Fin.ext; omega

theorem own_ge {b : Int} {R : Fin 3} (h : Own b R) : 16 ≤ b := by
  obtain ⟨k, hk, rfl⟩ := h; omega

theorem init_lt {x : w32} (h : isInitialBallot x = true) : sint.Z x < 16 := by
  simp only [isInitialBallot, beq_iff_eq] at h
  have e := congrArg BitVec.toInt h
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow] at e
  simp at e
  show x.toInt < 16
  omega

theorem tag_gt_irrefl (t : model.Tag) : t.gt t = false := by
  simp [model.Tag.gt, model.Tag.cmp, slt]

theorem forIn_opt_mem {α β : Type} (l : List α) (b : β) (f : α → β → Option (ForInStep β))
    (P : β → Prop) (h0 : P b) (hf : ∀ a b st, a ∈ l → P b → f a b = some st → P st.value) :
    ∀ r, forIn l b f = some r → P r := by
  induction l generalizing b with
  | nil => intro r h; cases h; exact h0
  | cons a l ih =>
    intro r h
    rw [List.forIn_cons] at h
    cases hfa : f a b with
    | none => rw [hfa] at h; cases h
    | some st =>
      have := hf a b st (by simp) h0 hfa
      rw [hfa] at h
      cases st with
      | done b' => cases h; exact this
      | yield b' => exact ih b' this (fun a' b'' st' ha => hf a' b'' st' (by simp [ha])) r h

theorem setAt_length (d : Deps) (q : Nat) (x : w32) : (d.setAt q x).length = d.length := by
  simp [Deps.setAt]

theorem setAt_at_ne (d : Deps) {q k : Nat} (x : w32) (h : k ≠ q) : (d.setAt q x).at k = d.at k := by
  simp [Deps.setAt, Deps.at, List.getD_eq_getElem?_getD, Ne.symm h]

/-- `updateAttributes` keeps the length and the rows `≥ 3`, and (at a non-leader) the leader's row. -/
theorem updAttr_deps {s : RState} {cmds : List Cmd} {seq0 : w32} {deps0 : Deps} {r : w32} {seq : w32}
    {deps : Deps} {ch : Bool}
    (h : updateAttributes s cmds seq0 deps0 r = some (seq, deps, ch)) :
    deps.length = deps0.length ∧
      ∀ k, (3 ≤ k ∨ (s.id ≠ r ∧ BitVec.ofNat 32 k = r)) → deps.at k = deps0.at k := by
  let P : w32 × Deps × Bool → Prop := fun st => st.2.1.length = deps0.length ∧
      ∀ k, (3 ≤ k ∨ (s.id ≠ r ∧ BitVec.ofNat 32 k = r)) → st.2.1.at k = deps0.at k
  unfold updateAttributes at h
  simp only [bind, Option.bind] at h
  split at h
  · cases h
  rename_i _ _ r1 hr1
  have P1 : P r1 := by
    refine forIn_opt_mem _ _ _ P ⟨rfl, fun _ _ => rfl⟩ ?_ r1 hr1
    intro q st st' hq hP hst
    split at hst
    · cases hst; exact hP
    · rename_i hskip
      split at hst
      · cases hst
      rename_i _ _ r2 hr2
      cases hst
      refine forIn_opt_mem _ _ _ P hP ?_ r2 hr2
      intro _ st2 st2' _ hP2 hst2
      have hq3 : q < 3 := by simp at hq; omega
      have key : ∀ (hi : w32) (x : w32) (b : Bool), P (x, st2.2.1.setAt q hi, b) := by
        intro hi x b
        refine ⟨by rw [setAt_length]; exact hP2.1, fun k hk => ?_⟩
        have hkq : k ≠ q := by
          rintro rfl
          rcases hk with hk | ⟨h1, h2⟩
          · omega
          · exact hskip ⟨h1, h2⟩
        rw [setAt_at_ne _ _ hkq]; exact hP2.2 k hk
      split at hst2
      · split at hst2
        · split at hst2
          · split at hst2 <;> (cases hst2; exact key _ _ _)
          · split at hst2
            · cases hst2
            · cases hst2; exact key _ _ _
        · cases hst2; exact hP2
      · cases hst2; exact hP2
  simp only at h
  split at h
  · cases h
  · cases h; exact P1

theorem forIn_flag {f : Nat → Bool × Deps → Id (ForInStep (Bool × Deps))} {sid : w32} {deps2 : Deps}
    (hf : ∀ q st, ∃ st', f q st = .yield st' ∧ (st'.1 = true → st.1 = true ∧ st'.2 = st.2 ∧
      (BitVec.ofNat 32 q ≠ sid → st.2.at q = deps2.at q))) :
    ∀ (l : List Nat) (st : Bool × Deps), (forIn l st f).1 = true →
      st.1 = true ∧ (forIn l st f).2 = st.2 ∧ ∀ q ∈ l, BitVec.ofNat 32 q ≠ sid → st.2.at q = deps2.at q
  | [], st, h => ⟨h, rfl, fun _ h => by cases h⟩
  | q :: l, st, h => by
    obtain ⟨st', e, k⟩ := hf q st
    have h' : (forIn l st' f).1 = true := by
      rw [List.forIn_cons, e] at h; exact h
    obtain ⟨a1, a2, a3⟩ := forIn_flag hf l st' h'
    obtain ⟨b1, b2, b3⟩ := k a1
    refine ⟨b1, ?_, ?_⟩
    · rw [List.forIn_cons, e]; exact a2.trans b2
    · intro q' hq' hne
      rcases List.mem_cons.1 hq' with rfl | hq'
      · exact b3 hne
      · rw [← b2]; exact a3 q' hq' hne

/-- `mergeAttributes` reporting `equal`: nothing changed, the seqs agree, and so do the rows other
than the merger's. -/
theorem merge_eq {s : RState} {seq1 seq2 seq : w32} {deps1 deps2 deps : Deps}
    (h : mergeAttributes s seq1 deps1 seq2 deps2 = (seq, deps, true)) :
    seq = seq1 ∧ deps = deps1 ∧ seq1 = seq2 ∧
      ∀ q : Nat, q < 3 → BitVec.ofNat 32 q ≠ s.id → deps1.at q = deps2.at q := by
  unfold mergeAttributes at h
  simp only [Id.run, bind, pure] at h
  have hf : ∀ q (st : Bool × Deps), ∃ st', (if BitVec.ofNat 32 q = s.id then
        ForInStep.yield (st.fst, st.snd)
      else if st.snd.at q ≠ deps2.at q then
        if sgt (deps2.at q) (st.snd.at q) = true then
          ForInStep.yield (false, st.snd.setAt q (deps2.at q))
        else ForInStep.yield (false, st.snd)
      else ForInStep.yield (st.fst, st.snd) : Id (ForInStep (Bool × Deps))) = .yield st' ∧
      (st'.1 = true → st.1 = true ∧ st'.2 = st.2 ∧
        (BitVec.ofNat 32 q ≠ s.id → st.2.at q = deps2.at q)) := by
    intro q st
    by_cases h1 : BitVec.ofNat 32 q = s.id
    · exact ⟨st, by simp [h1], fun e => ⟨e, rfl, fun hn => absurd h1 hn⟩⟩
    by_cases h2 : st.snd.at q ≠ deps2.at q
    · by_cases h3 : sgt (deps2.at q) (st.snd.at q) = true
      · exact ⟨(false, st.snd.setAt q (deps2.at q)), by simp [h1, h2, h3], fun e => by simp at e⟩
      · exact ⟨(false, st.snd), by simp [h1, h2, h3], fun e => by simp at e⟩
    · exact ⟨st, by simp [h1, h2], fun e => ⟨e, rfl, fun _ => by simpa using h2⟩⟩
  have e3 : ∀ q : Nat, q < 3 → q ∈ [0, 1, 2] := by intro q hq; simp; omega
  by_cases hs : seq1 ≠ seq2
  · exfalso
    rw [if_pos hs] at h
    split at h <;>
    · simp only [Prod.mk.injEq] at h
      exact absurd (forIn_flag hf _ _ h.2.2).1 (by simp)
  · rw [if_neg hs] at h; simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨-, k2, k3⟩ := forIn_flag hf _ _ h3
    exact ⟨h1.symm, h2.symm.trans k2, by simpa using hs, fun q hq hne => k3 q (e3 q hq) hne⟩

/-! ## `crt` and copies after a step (after `A1d`'s `StepFrame.lean`) -/

theorem crt_setCrt' (s : RState) (q x p : w32) :
    ((s.setCrt q x).crt p = x ∨ (s.setCrt q x).crt p = s.crt p) ∧
    (q ≠ p → (s.setCrt q x).crt p = s.crt p) := by
  simp only [RState.crt, RState.setCrt, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases e : q = p
  · subst e
    refine ⟨?_, fun h => absurd rfl h⟩
    simp only [ite_true]; split
    · simp
    · right; rename_i h; simp [List.getElem?_eq_none (Nat.le_of_not_lt h)]
  · have : q.toNat ≠ p.toNat := fun h => e (BitVec.eq_of_toNat_eq h)
    simp [e, this]

theorem Z_succ32' {x : w32} (h1 : sint.Z x < 2 ^ 31 - 1) : sint.Z (x + 1) = sint.Z x + 1 := by
  simp only [sint.Z] at *
  rw [BitVec.toInt_add]
  have := BitVec.toInt_le (x := x); have := BitVec.le_toInt (x := x)
  simp [Int.bmod]; omega

theorem rid_inj {a b : Fin 3} (h : rid32 a = rid32 b) : a = b := by
  revert a b; decide

/-- `t` is `s`, or `s` with `crt[q]` raised to `j + 1` (when `j ≥ crt[q]`). -/
def CrtB (s t : RState) (q j : w32) : Prop :=
  t = s ∨ (sge j (s.crt q) = true ∧ t = s.setCrt q (j + 1))

theorem crtB_core {s t : RState} {q0 i0 : w32} (h : CrtB s t q0 i0) (O : Fin 3 → w32)
    (hO : ∀ r, sint.Z (s.crt (rid32 r)) ≤ sint.Z (O r))
    (hbelow : rowOk q0 = true ∧ 0 ≤ sint.Z i0 ∧ sint.Z i0 < sint.Z (O (rowOf q0)))
    (a : Fin 3) (hOa : O a = s.crt (rid32 a)) :
    t.id = s.id ∧ t.inst = s.inst ∧ t.crt (rid32 a) = s.crt (rid32 a) ∧
      (∀ r : Fin 3, sint.Z (t.crt (rid32 r)) ≤ sint.Z (O r)) ∧
      t.crtInstance.length = s.crtInstance.length := by
  rcases h with rfl | ⟨hge, rfl⟩
  · exact ⟨rfl, rfl, rfl, hO, rfl⟩
  refine ⟨rfl, rfl, ?_, fun r => ?_, List.length_set ..⟩
  · refine (crt_setCrt' _ _ _ _).2 (fun e => ?_)
    have : rowOf q0 = a := rid_inj ((rid_rowOf hbelow.1).trans e)
    rw [this, hOa, ← e] at hbelow
    simp only [sge, sle, decide_eq_true_eq] at hge
    omega
  · by_cases e : q0 = rid32 r
    · have hr : rowOf q0 = r := rid_inj ((rid_rowOf hbelow.1).trans e)
      rcases (crt_setCrt' s q0 (i0 + 1) (rid32 r)).1 with h1 | h1
      · rw [h1]
        rw [hr] at hbelow
        have hlt : sint.Z (O r) < 2 ^ 31 := by
          simp only [sint.Z]; have := BitVec.toInt_lt (x := O r); omega
        rw [Z_succ32' (by omega)]; omega
      · rw [h1]; exact hO r
    · rw [(crt_setCrt' _ _ _ _).2 e]; exact hO r

theorem crtB_facts {c : Cfg gNet} {G : GG} (I : CInv c G) {a : Fin 3} {t : RState} {q0 i0 : w32}
    (h : CrtB (c.st a) t q0 i0)
    (hbelow : rowOk q0 = true ∧ 0 ≤ sint.Z i0 ∧ sint.Z i0 < sint.Z ((c.st (rowOf q0)).crt q0)) :
    t.id = (c.st a).id ∧ t.inst = (c.st a).inst ∧ t.crt (rid32 a) = (c.st a).crt (rid32 a) ∧
      (∀ r : Fin 3, sint.Z (t.crt (rid32 r)) ≤ sint.Z ((c.st r).crt (rid32 r))) ∧
      t.crtInstance.length = (c.st a).crtInstance.length := by
  have hb : rowOk q0 = true ∧ 0 ≤ sint.Z i0 ∧
      sint.Z i0 < sint.Z ((fun r : Fin 3 => (c.st r).crt (rid32 r)) (rowOf q0)) := by
    simp only [rid_rowOf hbelow.1]; exact hbelow
  exact crtB_core h (fun r : Fin 3 => (c.st r).crt (rid32 r)) (fun r => I.crtOwn a r) hb a rfl

theorem balOf_some {c : Cfg gNet} {q i : w32} {a : Fin 3} {cp : Copy} (h : cpOf c a q i = some cp) :
    balOf c q i a = some (sint.Z cp.ballot) := by
  simp only [balOf, h, Option.map_some]

theorem balOf_some_inv {c : Cfg gNet} {q i : w32} {a : Fin 3} {B : Int}
    (h : balOf c q i a = some B) : ∃ cp, cpOf c a q i = some cp ∧ sint.Z cp.ballot = B := by
  simp only [balOf] at h
  cases e : cpOf c a q i with
  | none => rw [e] at h; cases h
  | some cp => rw [e] at h; cases h; exact ⟨cp, rfl, rfl⟩

theorem setInst_self (t : RState) (q i : w32) (cp : Copy) : (t.setInst q i cp).inst q i = some cp := by
  simp [setInst_inst]

theorem setInst_other (t : RState) {q i q' i' : w32} (cp : Copy) (h : ¬ (q' = q ∧ i' = i)) :
    (t.setInst q i cp).inst q' i' = t.inst q' i' := by
  rw [setInst_inst, if_neg h]

/-- The history with instance `(q0, i0)`'s ghost replaced. -/
def ggSet (G : GG) (q0 i0 : w32) (g : Gh Val) : GG :=
  fun q i => if q = q0 ∧ i = i0 then g else G q i

theorem ggSet_at (G : GG) (q0 i0 : w32) (g : Gh Val) : ggSet G q0 i0 g q0 i0 = g := by
  simp [ggSet]

theorem ggSet_ne (G : GG) {q0 i0 q i : w32} (g : Gh Val) (h : ¬ (q = q0 ∧ i = i0)) :
    ggSet G q0 i0 g q i = G q i := by
  simp only [ggSet, h, ite_false]

/-! ## Transport (copies of `Inv.lean`'s, which imports this file) -/

theorem balOf_congr {c c1 : Cfg gNet} {q i : w32} (h : ∀ a, cpOf c1 a q i = cpOf c a q i) :
    balOf c1 q i = balOf c q i := by
  funext a; simp only [balOf, h]

theorem copyOk_congr {c c1 : Cfg gNet} {G : GG} {q i : w32} {a : Fin 3} {cp : Copy}
    (hb : balOf c1 q i = balOf c q i) (h : CopyOk c G q i a cp) : CopyOk c1 G q i a cp :=
  { h with preparing := by rw [hb]; exact h.preparing }

theorem instOk_congr {c c1 : Cfg gNet} {G : GG} {q i : w32} (h : ∀ a, cpOf c1 a q i = cpOf c a q i)
    (I : InstOk c G q i) : InstOk c1 G q i := by
  have hb := balOf_congr h
  exact
    { ainv := hb ▸ I.ainv
      copies := fun a cp hc => copyOk_congr hb (I.copies a cp ((h a).symm.trans hc))
      noCopy := fun a hc => I.noCopy a ((h a).symm.trans hc)
      fastL := fun v hv => by rw [h]; exact I.fastL v hv
      leaderCopy := fun ⟨a, cp, hc⟩ => by
        rw [h]; exact I.leaderCopy ⟨a, cp, (h a).symm.trans hc⟩
      ownMono := fun b R hR hp => by rw [hb]; exact I.ownMono b R hR hp
      fresh := fun hn => I.fresh (fun a => (h a).symm.trans (hn a)) }

theorem copyOk_G {c : Cfg gNet} {G1 G2 : GG} {q i : w32} {a : Fin 3} {cp : Copy}
    (e : G2 q i = G1 q i) (h : CopyOk c G1 q i a cp) : CopyOk c G2 q i a cp where
  nonneg := h.nonneg
  ballotForm := h.ballotForm
  vbalLe := h.vbalLe
  stOk := h.stOk
  noVotes := e ▸ h.noVotes
  accVote := e ▸ h.accVote
  committed := e ▸ h.committed
  rstVbal := e ▸ h.rstVbal
  eqCre := e ▸ h.eqCre
  leader0 := e ▸ h.leader0
  ownFresh := e ▸ h.ownFresh
  preparing := e ▸ h.preparing
  eqTrack := e ▸ h.eqTrack

theorem instOk_G {c : Cfg gNet} {G1 G2 : GG} {q i : w32} (e : G2 q i = G1 q i)
    (I : InstOk c G1 q i) : InstOk c G2 q i where
  ainv := e ▸ I.ainv
  copies a cp hc := copyOk_G e (I.copies a cp hc)
  noCopy a hc := e ▸ I.noCopy a hc
  fastL v hv := I.fastL v (e ▸ hv)
  leaderCopy := I.leaderCopy
  ownMono b R hR hp := I.ownMono b R hR (e ▸ hp)
  fresh hn := e ▸ I.fresh hn

/-! ## The history grows only at the stepping acceptor -/

/-- `g'` adds to `g` only facts about acceptor `R` (proposals at `R`'s ballots or `L`'s ballot 0
when `R = L`, `R`'s votes and unchanged pre-accepts, a fast commit when `R = L`). -/
structure GOnly (R L : Fin 3) (g g' : Gh Val) : Prop where
  acc : ∀ a b u, g'.acc a b u → ¬ g.acc a b u → a = R
  prop : ∀ b u, g'.prop b u → ¬ g.prop b u → (b = 0 ∧ R = L) ∨ Own b R
  rst : ∀ b, g'.rst b → g.rst b
  cre : ∀ v, g'.cre v → g.cre v
  eq : ∀ a, g'.eq a → ¬ g.eq a → a = R
  fast : ∀ v, g'.fast v → ¬ g.fast v → R = L

theorem GOnly.refl (R L : Fin 3) (g : Gh Val) : GOnly R L g g :=
  ⟨fun _ _ _ h hn => absurd h hn, fun _ _ h hn => absurd h hn, fun _ h => h, fun _ h => h,
   fun _ h hn => absurd h hn, fun _ h hn => absurd h hn⟩

/-- An unchanged copy of an acceptor other than the stepping one keeps `CopyOk`. -/
theorem copyOk_keep {c c1 : Cfg gNet} {G G' : GG} {q i : w32} {a R : Fin 3} {cp : Copy}
    (hC : CopyOk c G q i a cp)
    (E : Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i))
    (O : GOnly R (rowOf q) (G q i) (G' q i)) (ha : a ≠ R) : CopyOk c1 G' q i a cp := by
  have noprop : ∀ b u, Own b a → (G' q i).prop b u → (G q i).prop b u := by
    intro b u hown hu
    refine Classical.byContradiction fun h0 => ?_
    rcases O.prop b u hu h0 with ⟨rfl, -⟩ | h
    · have := own_ge hown; omega
    · exact ha (own_unique hown h)
  refine
    { nonneg := hC.nonneg, ballotForm := hC.ballotForm, vbalLe := hC.vbalLe, stOk := hC.stOk
      noVotes := ?_, accVote := ?_, committed := ?_, rstVbal := ?_, eqCre := ?_, leader0 := ?_
      ownFresh := ?_, preparing := ?_, eqTrack := ?_ }
  · intro hs b u h'
    by_cases h0 : (G q i).acc a b u
    · exact hC.noVotes hs b u h0
    · exact ha (O.acc a b u h' h0)
  · intro hs
    obtain ⟨k1, k2⟩ := hC.accVote hs
    refine ⟨E.le.acc _ _ _ k1, fun b u h' => ?_⟩
    by_cases h0 : (G q i).acc a b u
    · exact k2 b u h0
    · exact absurd (O.acc a b u h' h0) ha
  · intro hs; exact chosen_mono E.le (hC.committed hs)
  · intro hs hv; obtain ⟨k1, k2⟩ := hC.rstVbal hs hv; exact ⟨k1, E.le.rst _ k2⟩
  · intro h1 h2 h3; exact E.le.cre _ (hC.eqCre h1 h2 h3)
  · intro haL hb hs
    obtain ⟨k1, k2, k3, k4⟩ := hC.leader0 haL hb hs
    refine ⟨E.le.cre _ k1, fun u hu => ?_, fun v hv => ?_, k4⟩
    · by_cases h0 : (G q i).prop 0 u
      · exact k2 u h0
      · rcases O.prop 0 u hu h0 with ⟨-, h⟩ | h
        · exact ha (haL.trans h.symm)
        · have := own_ge h; omega
    · by_cases h0 : (G q i).fast v
      · exact k3 v h0
      · exact ha (haL.trans (O.fast v hv h0).symm)
  · intro hs hown u hu
    exact hC.ownFresh hs hown u (noprop _ u hown hu)
  · intro lb hl hp hnc hown
    obtain ⟨k1, k2, k3, k4, k5⟩ := hC.preparing lb hl hp hnc hown
    have hb : 0 < sint.Z cp.ballot := by have := own_ge hown; omega
    exact ⟨riOk_evolve E hb k1, fun h => k2 (O.rst _ h), fun u hu => k3 u (noprop _ u hown hu), k4, k5⟩
  · intro hL he
    by_cases h0 : (G q i).eq a
    · rcases hC.eqTrack hL h0 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (rstBelow_mono E.le h)))
    · exact absurd (O.eq a he h0) ha

/-! ## Messages along an evolution -/

/-- `MsgOk` along an evolution of every instance (the cre's are unique in the new history), given a
ballot-0 PreAccept's receiver-copy and multiplicity facts in the new configuration. -/
theorem msgOk_evolve {c c1 : Cfg gNet} {G G' : GG}
    (E : ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i))
    (hcu : ∀ q i v w, (G' q i).cre v → (G' q i).cre w → v = w)
    {d : Fin 3} {m : Msg} (h : MsgOk c G d m)
    (hpa : ∀ x, m = .preAccept x → x.ballot = 0 →
      (∀ cp, cpOf c1 d x.replica x.inst = some cp →
        0 < sint.Z cp.ballot ∨ cp.status = St.ACCEPTED ∨ isCommitted cp.status) ∧
      (c1.inflight d).count (Msg.preAccept x : gNet.M) = 1) :
    MsgOk c1 G' d m := by
  cases m with
  | preAccept x =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun hb => ?_, fun hb => ?_⟩
    · obtain ⟨k1, k2, k3, -, -⟩ := h1 hb
      obtain ⟨k4, k5⟩ := hpa x rfl hb
      exact ⟨k1, k2, (E _ _).le.cre _ k3, k4, k5⟩
    · obtain ⟨k1, k2, k3⟩ := h2 hb
      exact ⟨k1, (E _ _).le.rst _ k2, k3⟩
  | preAcceptReply x =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun hb => ?_, fun hb hok => ?_⟩
    · obtain ⟨k1, k2, k3⟩ := h1 hb
      refine ⟨k1, fun hok hc => ?_, fun hok => ?_⟩
      · obtain ⟨v, hv, -⟩ := k3 hok
        obtain ⟨w, hw, hw'⟩ := hc
        have : w = v := hcu _ _ _ _ hw ((E _ _).le.cre _ hv)
        subst this
        obtain ⟨X, hX, hX'⟩ := k2 hok ⟨w, hv, hw'⟩
        exact ⟨X, hX, (E _ _).le.eq _ hX'⟩
      · obtain ⟨v, hv, k⟩ := k3 hok
        exact ⟨v, (E _ _).le.cre _ hv, k⟩
    · obtain ⟨k1, k2⟩ := h2 hb hok
      exact ⟨k1, (E _ _).le.rst _ k2⟩
  | preAcceptOK x =>
    obtain ⟨X, hX, hX'⟩ := h
    exact ⟨X, hX, (E _ _).le.eq _ hX'⟩
  | accept x =>
    obtain ⟨h1, R, k1, k2, k3, k4⟩ := h
    exact ⟨(E _ _).le.prop _ _ h1, R, k1, k2, k3, (E _ _).le.acc _ _ _ k4⟩
  | acceptReply x =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun hok => ?_, h2⟩
    obtain ⟨Y, hY, v, hv, hv'⟩ := h1 hok
    exact ⟨Y, hY, v, (E _ _).le.acc _ _ _ hv, (E _ _).le.acc _ _ _ hv'⟩
  | commit x => exact chosen_mono (E _ _).le h
  | prepare x =>
    obtain ⟨h1, R, h2, h3, h4, B, hB, hle⟩ := h
    obtain ⟨B', hB', hle'⟩ := (E _ _).bal_mono R B hB
    exact ⟨h1, R, h2, h3, h4, B', hB', Int.le_trans hle hle'⟩
  | prepareReply x =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨fun hs => chosen_mono (E _ _).le (h1 hs), fun hok => ?_, h3⟩
    obtain ⟨⟨B, hB, hle⟩, Y, k1, k2, k3, k4⟩ := h2 hok
    obtain ⟨B', hB', hle'⟩ := (E _ _).bal_mono d B hB
    have hb : 0 < sint.Z x.ballot := by have := own_ge k3; omega
    exact ⟨⟨B', hB', Int.le_trans hle hle'⟩, Y, k1, k2, k3, fun hs hn =>
      repOk_evolve (E _ _) hb (k4 hs (fun u hu => hn u ((E _ _).le.prop _ _ hu)))⟩
  | _ => trivial

/-! ## The frame of a one-instance step -/

/-- Replica `a`'s step touching (in its state) only its copy of `(q0, i0)` and its `crt` (its own
row's unchanged, the others' within their owners'), consuming `m0` and sending `o`. -/
structure Step1 (c c1 : Cfg gNet) (a : Fin 3) (q0 i0 : w32) (m0 : Msg) (o : List Out) : Prop where
  st : ∀ j, j ≠ a → c1.st j = c.st j
  inf : ∀ j : Fin 3, c1.inflight j =
    (if j = a then (c.inflight j).erase m0 else c.inflight j) ++ sentTo gNet j o
  id : (c1.st a).id = (c.st a).id
  inst : ∀ q i, ¬ (q = q0 ∧ i = i0) → (c1.st a).inst q i = (c.st a).inst q i
  len : (c1.st a).crtInstance.length = (c.st a).crtInstance.length
  crtA : (c1.st a).crt (rid32 a) = (c.st a).crt (rid32 a)
  crtLe : ∀ r : Fin 3, sint.Z ((c1.st a).crt (rid32 r)) ≤ sint.Z ((c.st r).crt (rid32 r))

section frame
variable {c c1 : Cfg gNet} {a : Fin 3} {q0 i0 : w32} {m0 : Msg} {o : List Out}

theorem Step1.cp (S : Step1 c c1 a q0 i0 m0 o) (j : Fin 3) (q i : w32)
    (h : ¬ (j = a ∧ q = q0 ∧ i = i0)) : cpOf c1 j q i = cpOf c j q i := by
  unfold cpOf
  by_cases hj : j = a
  · subst hj; exact S.inst q i (fun e => h ⟨rfl, e⟩)
  · rw [S.st j hj]

theorem Step1.bal (S : Step1 c c1 a q0 i0 m0 o) (q i : w32) (h : ¬ (q = q0 ∧ i = i0)) :
    balOf c1 q i = balOf c q i :=
  balOf_congr fun j => S.cp j q i (fun e => h e.2)

theorem Step1.crt_own (S : Step1 c c1 a q0 i0 m0 o) (q : Fin 3) :
    (c1.st q).crt (rid32 q) = (c.st q).crt (rid32 q) := by
  by_cases hq : q = a
  · subst hq; exact S.crtA
  · rw [S.st q hq]

theorem Step1.crt_row (S : Step1 c c1 a q0 i0 m0 o) {q : w32} (h : rowOk q = true) :
    (c1.st (rowOf q)).crt q = (c.st (rowOf q)).crt q := by
  have := S.crt_own (rowOf q); rwa [rid_rowOf h] at this

theorem Step1.old (_S : Step1 c c1 a q0 i0 m0 o) {d : Fin 3} {x : Msg}
    (h : x ∈ (if d = a then (c.inflight d).erase m0 else c.inflight d)) : x ∈ c.inflight d := by
  split at h
  · exact List.erase_subset h
  · exact h

theorem Step1.countP_le (S : Step1 c c1 a q0 i0 m0 o) (d : Fin 3) (p : Msg → Bool)
    (hp : ∀ x, x ∈ sentTo gNet d o → p x = false) :
    (c1.inflight d).countP p ≤ (c.inflight d).countP p := by
  have e1 : (c1.inflight d).countP p = (if d = a then (c.inflight d).erase m0 else c.inflight d).countP p +
      (sentTo gNet d o).countP p := by rw [S.inf d]; exact List.countP_append ..
  have : (sentTo gNet d o).countP p = 0 := List.countP_eq_zero.2 fun x hx => by rw [hp x hx]; simp
  rw [e1, this, Nat.add_zero]
  split
  · exact (List.erase_sublist).countP_le
  · exact Nat.le_refl _

theorem beq_pa_false {z : Msg} {y : PreAcceptM} (h : z ≠ .preAccept y) :
    (z == (Msg.preAccept y : gNet.M)) = false := by
  cases z <;> simp_all

/-- **The frame.** -/
theorem inv_frame {G G' : GG} (I : CInv c G) (S : Step1 c c1 a q0 i0 m0 o)
    (hG : ∀ q i, ¬ (q = q0 ∧ i = i0) → G' q i = G q i)
    (E0 : Evolve (rowOf q0) (G q0 i0) (balOf c q0 i0) (G' q0 i0) (balOf c1 q0 i0))
    (hI0 : InstOk c1 G' q0 i0)
    (hcb : ∀ cp, cpOf c1 a q0 i0 = some cp →
      rowOk q0 = true ∧ 0 ≤ sint.Z i0 ∧ sint.Z i0 < sint.Z ((c.st (rowOf q0)).crt q0))
    (hnew : ∀ d x, x ∈ sentTo gNet d o → MsgOk c1 G' d x ∧
      (∀ q j, msgInst x = some (q, j) →
        rowOk q = true ∧ 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ((c.st (rowOf q)).crt q)) ∧
      (∀ y, x ≠ .preAccept y) ∧ (∀ q i b, isPrepareAt q i b x = false) ∧
      (∀ q i b Y, isOKReplyAt q i b Y x = false))
    (hpa0 : ∀ x, Msg.preAccept x ∈ c1.inflight a → x.ballot = 0 → x.replica = q0 → x.inst = i0 →
      ∀ cp, cpOf c1 a q0 i0 = some cp →
        0 < sint.Z cp.ballot ∨ cp.status = St.ACCEPTED ∨ isCommitted cp.status)
    (hprep : ∀ cp lb, cpOf c1 a q0 i0 = some cp → cp.lb = some lb → lb.preparing = true →
      ¬ isCommitted cp.status → Own (sint.Z cp.ballot) a →
      ∃ cp0 lb0, cpOf c a q0 i0 = some cp0 ∧ cp0.lb = some lb0 ∧ lb0.preparing = true ∧
        ¬ isCommitted cp0.status ∧ cp0.ballot = cp.ballot ∧ lb0.prepareOKs = lb.prepareOKs)
    (hNN : ∀ cp, cpOf c a q0 i0 = some cp → cp.status ≠ St.NONE →
      ∃ cp', cpOf c1 a q0 i0 = some cp' ∧ cp'.status ≠ St.NONE) :
    CInv c1 G' ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i) := by
  have EV : ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i) := by
    intro q i
    by_cases hf : q = q0 ∧ i = i0
    · obtain ⟨rfl, rfl⟩ := hf; exact E0
    · rw [hG q i hf, S.bal q i hf]; exact Evolve.refl (I.inst q i).ainv
  have IO : ∀ q i, InstOk c1 G' q i := by
    intro q i
    by_cases hf : q = q0 ∧ i = i0
    · obtain ⟨rfl, rfl⟩ := hf; exact hI0
    · exact instOk_G (hG q i hf) (instOk_congr (fun j => S.cp j q i (fun e => hf e.2)) (I.inst q i))
  have hcu : ∀ q i v w, (G' q i).cre v → (G' q i).cre w → v = w := fun q i =>
    (IO q i).ainv.cre_uniq
  have hmem : ∀ (d : Fin 3) x, x ∈ c1.inflight d →
      x ∈ (if d = a then (c.inflight d).erase m0 else c.inflight d) ∨ x ∈ sentTo gNet d o := by
    intro d x hx; rw [S.inf d] at hx; exact List.mem_append.1 hx
  refine ⟨{ ids := ?_, inst := IO, msgs := ?_, crtOwn := ?_, copyBelow := ?_, msgBelow := ?_,
            crtLen := ?_, leaderHas := ?_, prepMult := ?_ }, EV⟩
  · intro j
    by_cases hj : j = a
    · subst hj; rw [S.id]; exact I.ids j
    · rw [S.st j hj]; exact I.ids j
  · intro d x hx
    rcases hmem d x hx with hx' | hx'
    · refine msgOk_evolve EV hcu (I.msgs d x (S.old hx')) (fun y hy hb => ?_)
      subst hy
      refine ⟨fun cp hc => ?_, ?_⟩
      · by_cases hf : d = a ∧ y.replica = q0 ∧ y.inst = i0
        · obtain ⟨rfl, e1, e2⟩ := hf
          rw [e1, e2] at hc
          exact hpa0 y hx hb e1 e2 cp hc
        · rw [S.cp d _ _ hf] at hc
          exact ((I.msgs d _ (S.old hx')).1 hb).2.2.2.1 cp hc
      · have h1 : (c.inflight d).count (Msg.preAccept y : gNet.M) = 1 :=
          ((I.msgs d _ (S.old hx')).1 hb).2.2.2.2
        have h2 := S.countP_le d (fun z => z == (Msg.preAccept y : gNet.M)) (fun z hz => by
          exact beq_pa_false ((hnew d z hz).2.2.1 y))
        have h3 : 0 < (c1.inflight d).count (Msg.preAccept y : gNet.M) := List.count_pos_iff.2 hx
        have e1 : (c1.inflight d).count (Msg.preAccept y : gNet.M) =
            (c1.inflight d).countP (fun z => z == (Msg.preAccept y : gNet.M)) := rfl
        have e2 : (c.inflight d).count (Msg.preAccept y : gNet.M) =
            (c.inflight d).countP (fun z => z == (Msg.preAccept y : gNet.M)) := rfl
        omega
    · exact (hnew d x hx').1
  · intro j q
    rw [S.crt_own q]
    by_cases hj : j = a
    · subst hj; exact S.crtLe q
    · rw [S.st j hj]; exact I.crtOwn j q
  · intro j q i cp hc
    by_cases hf : j = a ∧ q = q0 ∧ i = i0
    · obtain ⟨rfl, rfl, rfl⟩ := hf
      obtain ⟨k1, k2, k3⟩ := hcb cp hc
      rw [S.crt_row k1]; exact ⟨k1, k2, k3⟩
    · rw [S.cp j q i hf] at hc
      obtain ⟨k1, k2, k3⟩ := I.copyBelow j q i cp hc
      rw [S.crt_row k1]; exact ⟨k1, k2, k3⟩
  · intro d x q j hx hj
    rcases hmem d x hx with hx' | hx'
    · obtain ⟨k1, k2, k3⟩ := I.msgBelow d x q j (S.old hx') hj
      rw [S.crt_row k1]; exact ⟨k1, k2, k3⟩
    · obtain ⟨k1, k2, k3⟩ := (hnew d x hx').2.1 q j hj
      rw [S.crt_row k1]; exact ⟨k1, k2, k3⟩
  · intro j
    by_cases hj : j = a
    · subst hj; rw [S.len]; exact I.crtLen j
    · rw [S.st j hj]; exact I.crtLen j
  · intro q j h0 h1
    rw [S.crt_own q] at h1
    obtain ⟨cp, hc, hne⟩ := I.leaderHas q j h0 h1
    by_cases hf : q = a ∧ rid32 q = q0 ∧ j = i0
    · obtain ⟨rfl, rfl, rfl⟩ := hf; exact hNN cp hc hne
    · rw [S.cp q _ j hf]; exact ⟨cp, hc, hne⟩
  · intro R q i cp lb hc hl hp hnc hown
    obtain ⟨cp0, lb0, hc0, hl0, hp0, hnc0, eb, eo⟩ : ∃ cp0 lb0, cpOf c R q i = some cp0 ∧
        cp0.lb = some lb0 ∧ lb0.preparing = true ∧ ¬ isCommitted cp0.status ∧
        cp0.ballot = cp.ballot ∧ lb0.prepareOKs = lb.prepareOKs := by
      by_cases hf : R = a ∧ q = q0 ∧ i = i0
      · obtain ⟨rfl, rfl, rfl⟩ := hf; exact hprep cp lb hc hl hp hnc hown
      · rw [S.cp R q i hf] at hc; exact ⟨cp, lb, hc, hl, hp, hnc, rfl, rfl⟩
    rw [← eb] at hown ⊢
    obtain ⟨k1, k2⟩ := I.prepMult R q i cp0 lb0 hc0 hl0 hp0 hnc0 hown
    have cP : ∀ Y, (c1.inflight Y).countP (isPrepareAt q i cp0.ballot) ≤
        (c.inflight Y).countP (isPrepareAt q i cp0.ballot) := fun Y =>
      S.countP_le Y _ (fun z hz => (hnew Y z hz).2.2.2.1 _ _ _)
    have cR : ∀ Y, (c1.inflight R).countP (isOKReplyAt q i cp0.ballot Y) ≤
        (c.inflight R).countP (isOKReplyAt q i cp0.ballot Y) := fun Y =>
      S.countP_le R _ (fun z hz => (hnew R z hz).2.2.2.2 _ _ _ _)
    refine ⟨fun Y => Nat.le_trans (Nat.add_le_add (cP Y) (cR Y)) (k1 Y), fun h1 => ?_⟩
    obtain ⟨k3, k4, k5⟩ := k2 (by rw [eo]; exact h1)
    exact ⟨k3, Nat.le_zero.1 (k4 ▸ cP _), Nat.le_zero.1 (k5 ▸ cR _)⟩

end frame

end Perennial.gryff.pureA.SPA
