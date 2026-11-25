/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/IntfSteps.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AI, internal: the local obligations of the EPaxos handlers for the interference invariant
(`StepI`: the table grows, the own row's `crt` is kept, the recorded instance `ox` is in the table,
has a copy, and was recorded by someone before (or is of the own row); `LocalI` w.r.t. the ghost
with `ox` recorded at the step's time `κ`). Same pattern as unit AW's `WitSteps.lean`.
-/
module

public import Dsverify.Proof.gryff.PureA.IntfFrame
public import Dsverify.Proof.gryff.PureA.WitSteps

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AI

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA
open Perennial.gryff.pureA.AW

/-- What a step of replica `a` from state `s` may use. -/
structure CtxI (rc : RecG) (κ : Nat) (dg : DepG) (s : RState) (a : Fin 3) : Prop where
  id : s.id = rid32 a
  copies : ∀ q i cp, s.inst q i = some cp → CopyI rc κ dg q i a cp
  tab : ∀ (r : Fin 3) j t, rc a (rid32 r) j = some t →
    ∃ hi, s.confAt r.val = some hi ∧ sint.Z j ≤ sint.Z hi
  confLen : s.conf.length = 3
  clock : ∀ w q j t, rc w q j = some t → t < κ
  own : ∀ w r j t, rc w (rid32 r) j = some t → ∃ t0, rc r (rid32 r) j = some t0 ∧ t0 ≤ t

/-- A step's obligations (no creation). -/
structure StepI (rc : RecG) (κ : Nat) (dg : DepG) (s s' : RState) (a : Fin 3) (o : List Out)
    (ox : Option (w32 × w32)) : Prop where
  conf : ConfLe s s'
  crtOwn : s'.crt s.id = s.crt s.id
  recd : ∀ q j, ox = some (q, j) → (∃ hi, s'.confAt q.toNat = some hi ∧ sint.Z j ≤ sint.Z hi) ∧
    s'.inst q j ≠ none ∧ (q = s.id ∨ ∃ w t, rc w q j = some t)
  loc : LocalI (addRec rc a κ ox) (κ + 1) dg s s' a o

variable {rc : RecG} {κ : Nat} {dg : DepG} {s s' : RState} {a : Fin 3} {o : List Out}

/-! ## Helpers -/

theorem cpI_setInst {rc' : RecG} {κ' : Nat} {t : RState} {q0 i0 : w32} {cp0 : Copy}
    (ht : t.inst = s.inst) (h : CopyI rc' κ' dg q0 i0 a cp0) :
    ∀ q i cp, (t.setInst q0 i0 cp0).inst q i = some cp → s.inst q i = some cp ∨
      CopyI rc' κ' dg q i a cp := by
  intro q i cp hc
  rw [setInst_inst] at hc
  split at hc
  · rename_i e; obtain ⟨rfl, rfl⟩ := e; cases hc; exact Or.inr h
  · rw [ht] at hc; exact Or.inl hc

theorem localI_same : LocalI rc κ dg s s a [] :=
  ⟨fun _ _ _ h => Or.inl h, fun _ _ h => (sentR_nil h).elim⟩

theorem stepI_same : StepI rc κ dg s s a [] none :=
  ⟨ConfLe.refl s, rfl, fun _ _ h => (by cases h), localI_same⟩

/-- `setCrt` at another row keeps the own row's `crt`. -/
theorem crt_setCrt_ne {t : RState} {q p x : w32} (h : p ≠ q) : (t.setCrt q x).crt p = t.crt p := by
  unfold RState.setCrt RState.crt
  dsimp only
  have : p.toNat ≠ q.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
  simp [List.getD, Ne.symm this]

/-- A raised `crt` (by a message about `(q, j)`) keeps the own row's: the own row is not raised by
messages (`hb`: instances of the own row are below `crt`). -/
theorem bump_crtOwn {s1 : RState} {m : PreAcceptM} (hb0 : SPA.Bump s m s1)
    (hb : m.replica = s.id → sint.Z m.inst < sint.Z (s.crt m.replica)) :
    s1.crt s.id = s.crt s.id := by
  rcases hb0 with rfl | ⟨hge, rfl⟩
  · rfl
  · by_cases e : m.replica = s.id
    · have := hb e
      simp only [sge, sle, decide_eq_true_eq] at hge
      omega
    · exact crt_setCrt_ne (Ne.symm e)

theorem cand_of_old {q i : w32} {c : Copy} (hc : CopyI rc κ dg q i a c) {lb : LB}
    (hl : c.lb = some lb) (hn : ¬ isCommitted c.status) :
    CandI (addRec rc a κ ox) (κ + 1) q i lb.recoveryInst :=
  candI_mono (addRec_ext rc a κ ox) (Nat.le_succ _) (hc.cand lb hl hn)

theorem confLe_of_eq {t : RState} (h : t.conf = s.conf) : ConfLe s t :=
  ⟨by rw [h], fun k hi hh => ⟨hi, by unfold RState.confAt; rw [h]; exact hh, Int.le_refl _⟩⟩

theorem uc_crt (t : RState) (cmds : List Cmd) (q j sq p : w32) :
    (updateConflicts t cmds q j sq).crt p = t.crt p := by
  unfold RState.crt; rw [(updateConflicts_inst _ _ _ _ _).2.2]

theorem toNat_lt_of_inBox {q j : w32} (h : inBox q j = true) : q.toNat < 3 := by
  simp only [inBox, decide_eq_true_eq] at h
  obtain ⟨h1, h2, -⟩ := h
  unfold sint.Z at h1 h2
  rw [BitVec.toInt_eq_toNat_cond] at h1 h2
  split at h1 <;> omega

/-- A coverer of `D` covers `D'` equal to it on the three rows. -/
theorem cov_eq3 {rc : RecG} {κ : Nat} {q i : w32} {D D' : Deps} {w : Fin 3} {e : Option (Fin 3)}
    (hD : ∀ k, k < 5 → D.at k = D'.at k) (h : Cov rc κ q i D w e) : Cov rc κ q i D' w e :=
  cov_weaken (fun _ h => h) (fun r _ => by rw [hD r.val (by omega)]; exact Int.le_refl _) h

/-! ## handlePreAccept -/

theorem pa_cmds {m : PreAcceptM} (h : stepPreAccept s m = .ok (s', o)) (hn : m.cmds = []) :
    o = [] := by
  unfold stepPreAccept at h
  rw [hn] at h
  peel h
  all_goals (cases h; rfl)

theorem li_preAccept {m : PreAcceptM} (C : CtxI rc κ dg s a) (hm : MsgI rc κ dg a (.preAccept m))
    (hP0 : isInitialBallot m.ballot = true → m.ballot = 0)
    (h0 : m.ballot = 0 → m.replica ≠ rid32 a)
    (hb : m.replica = s.id → sint.Z m.inst < sint.Z (s.crt m.replica))
    (h : stepPreAccept s m = .ok (s', o)) : ∃ ox, StepI rc κ dg s s' a o ox := by
  obtain ⟨-, hc⟩ := SPA.stepPreAccept_cases h
  rcases hc with ⟨rfl, rfl⟩ | ⟨s1, c, x, hb0, -, -, -, es, rfl, hx⟩ | ⟨s1, cp, x, hb0, rfl, rfl, U⟩
  · exact ⟨none, stepI_same⟩
  · rw [es]
    obtain ⟨ei, -, -⟩ := bump_facts hb0
    have hcf : s1.conf = s.conf := by rcases hb0 with rfl | ⟨-, rfl⟩ <;> rfl
    refine ⟨none, ⟨⟨by rw [hcf], fun k hi h => ⟨hi, by unfold RState.confAt; rw [hcf]; exact h,
      Int.le_refl _⟩⟩, bump_crtOwn hb0 hb, fun _ _ h => (by cases h), ?_⟩⟩
    refine ⟨fun q i cp hc => Or.inl (by rw [← ei]; exact hc), fun d y hy => ?_⟩
    obtain ⟨-, d0, -, rfl⟩ := hx
    rw [sentR_send hy]; intro hne; exact absurd rfl hne
  · obtain ⟨ei, -, eid⟩ := bump_facts hb0
    have hcf : s1.conf = s.conf := by rcases hb0 with rfl | ⟨-, rfl⟩ <;> rfl
    have hconf1 : ∀ k, s1.confAt k = s.confAt k := fun k => by unfold RState.confAt; rw [hcf]
    have hcmd : m.cmds ≠ [] := fun hn => by cases pa_cmds h hn
    obtain ⟨hl, hsr, ⟨w, hw, hcw⟩, hz⟩ := hm hcmd
    obtain ⟨ch, hua⟩ := U.ua
    obtain ⟨hdle, hlen, hcov⟩ := updAttr_facts hua hl
    have hbox := (SPA.stepPreAccept_cases h).1
    -- the new state
    obtain ⟨UC1, UC2, -⟩ := uc_facts (s1.setInst m.replica m.inst cp) m.cmds m.replica m.inst m.seq
    have ecid : s1.id = rid32 a := eid.trans C.id
    have E := addRec_ext rc a κ (some (m.replica, m.inst))
    -- a's coverage
    have hrec := addRec_self (rc := rc) (a := a) (κ := κ) (q := m.replica) (j := m.inst)
      (fun t ht => C.clock _ _ _ _ ht)
    have hcovA : Cov (addRec rc a κ (some (m.replica, m.inst))) (κ + 1) m.replica m.inst cp.deps a
        none := by
      refine cov_new C.tab (fun r hr _ hi hh => ?_) ⟨_, hrec.choose_spec.1, hrec.choose_spec.2.1⟩
      have : ¬ (s1.id ≠ m.replica ∧ BitVec.ofNat 32 r.val = m.replica) := fun ⟨_, e⟩ => hr e
      exact hcov hcmd r.val r.isLt this hi (by rw [hconf1]; exact hh)
    have hcovW := cov_dle hdle (cov_mono E (Nat.le_succ _) hcw)
    have hsr' := sameRow_dle hdle hsr
    have hin : (updateConflicts (s1.setInst m.replica m.inst cp) m.cmds m.replica m.inst m.seq).inst
        m.replica m.inst = some cp := by
      rw [(updateConflicts_inst _ _ _ _ _).1, setInst_inst, if_pos ⟨rfl, rfl⟩]
    refine ⟨some (m.replica, m.inst), ⟨(confLe_of_eq hcf).trans UC1, ?_, ?_, ?_, ?_⟩⟩
    · rw [uc_crt]; show s1.crt s.id = s.crt s.id; exact bump_crtOwn hb0 hb
    · intro q j e; cases e
      refine ⟨UC2 hcmd (by show _ < s1.conf.length; rw [hcf, C.confLen]; exact toNat_lt_of_inBox hbox),
        by rw [hin]; simp, ?_⟩
      obtain ⟨τ, -, ⟨t, ht, -⟩, -⟩ := hcw
      exact Or.inr ⟨w, t, ht⟩
    · intro q i cp' hc'
      rw [(updateConflicts_inst _ _ _ _ _).1] at hc'
      refine cpI_setInst ei ⟨fun _ _ => ⟨⟨hsr', ⟨w, hcovW⟩, fun _ =>
        ⟨w, a, none, hw, hcovW, hcovA, Or.inl rfl⟩⟩, fun _ => ⟨hcovA, by rw [hlen]; exact hl⟩⟩,
        fun _ hq hb0' _ => absurd hq (h0 (by rw [← U.ballot]; exact hb0')), ?_⟩ q i cp' hc'
      intro lb hlb hn
      rcases U.old with hn0 | ⟨c, hc, hnc, -, el⟩
      · rw [preAccept_lb_none h hn0 cp hin] at hlb; cases hlb
      · rw [el] at hlb; exact cand_of_old (C.copies _ _ _ hc) hlb (not_cae hnc)
    · intro d y hy
      have hda : ∀ d0 : Fin 3, dstOf m.leaderId = some d0 → m.leaderId ≠ s.id → d0 ≠ a := by
        intro d0 hd0 hne e; subst e
        exact hne (by rw [C.id, ← A1b.dstOf_some hd0])
      rcases U.out with ⟨hne, d0, hd0, rfl⟩ | ⟨hEQ, hrl, hinit, hne, d0, hd0, rfl⟩
      · obtain ⟨ey, ed⟩ := sentR_send2 hy
        rw [ey, ← ed]
        intro _
        exact ⟨hsr', a, (hda _ hd0 hne).symm, hcovA⟩
      · obtain ⟨ey, ed⟩ := sentR_send2 hy
        rw [ey, ← ed]
        have e1 : rid32 d0 = m.replica := by rw [A1b.dstOf_some hd0, hrl]
        refine ⟨m.deps, by rw [e1]; exact hz (hP0 hinit), a, (hda _ hd0 hne).symm, ?_⟩
        rw [e1]
        exact cov_eq3 (fun k hk => SPA.depsEqual_at (U.st2 hEQ).2.1 hk) hcovA

end Perennial.gryff.pureA.AI
