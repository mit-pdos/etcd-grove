/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/IntfSteps3.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AI, internal: the creation (`handlePropose`'s `startPhase1` at `(id, crt[id])`, ballot 0: the
creator records its instance and covers its whole table, the creation deps go to the ghost `dg`),
`startRecoveryForInstance`, and `handlePrepareReply` (G22's commit, the candidate updates, the
Accept of a candidate, the restart `startPhase1` of G9/G32 (the recoverer records the instance and
covers its table but the instance's row, where `deps[L] = i - 1`), the no-op).
-/
module

public import Dsverify.Proof.gryff.PureA.IntfSteps2

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AI

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA
open Perennial.gryff.pureA.AW

variable {rc : RecG} {κ : Nat} {dg : DepG} {s s' : RState} {a : Fin 3} {o : List Out}

/-- `startPhase1`'s result (the new copy, its deps from `updateAttributes`, the table, the
PreAccepts). -/
theorem sp1I {t t' : RState} {r i b : w32} {ps : List Proposal} {cs : List Cmd} {o : List Out}
    (h : startPhase1 t r i b ps cs = .ok (t', o)) :
    ∃ (cp : Copy) (D0 : Deps) (ch : Bool), (∀ q j, t'.inst q j = if q = r ∧ j = i then some cp else t.inst q j) ∧
      t'.id = t.id ∧ t'.crtInstance = t.crtInstance ∧
      cp.status = St.PREACCEPTED ∧ cp.ballot = b ∧ cp.cmds = cs ∧ cs ≠ [] ∧
      (∀ lb, cp.lb = some lb → lb.recoveryInst = none) ∧ inBox r i = true ∧
      D0.length = 5 ∧ (r ≠ t.id → D0.at r.toNat = i - 1) ∧ (r = t.id → D0 = [-1, -1, -1, 0, 0]) ∧
      updateAttributes t cs 0 D0 r = some (cp.seq, cp.deps, ch) ∧
      t' = updateConflicts (t.setInst r i cp) cs r i cp.seq ∧
      ∀ (d : Fin 3) y, y ∈ A1b.sentR d o → ∃ x : PreAcceptM, y = .preAccept x ∧
        x.replica = r ∧ x.inst = i ∧ x.ballot = b ∧ x.deps = cp.deps ∧ x.cmds = cs ∧
        rid32 d ≠ t.id := by
  unfold startPhase1 at h
  peel h
  all_goals (
    rename_i hbc
    cases h
    obtain ⟨e1, e2, e3⟩ := updateConflicts_inst (t.setInst r i _) cs r i _
    have hbox : inBox r i = true := by simpa using ‹¬(!inBox r i) = true›
    refine ⟨_, _, _, fun q' i' => by rw [e1]; rfl, e2, e3, rfl, rfl, rfl, ?_,
      fun lb hl => by cases hl; rfl, hbox, ?_, ?_, ?_, ‹updateAttributes _ _ _ _ _ = some _›, rfl, ?_⟩
    · intro hn; subst hn; simp at *
    · first | rfl | simp [Deps.setAt]
    · intro hne
      first
        | exact absurd hne ‹¬r ≠ t.id›
        | exact setAt_at_same (by have := toNat_lt_of_inBox hbox; simp; omega)
    · intro he
      first
        | rfl
        | exact absurd he ‹r ≠ t.id›
    intro d y hy
    obtain ⟨h1, h2⟩ := A1b.bcast_sent' hbc d y hy
    exact ⟨_, h1, rfl, rfl, rfl, rfl, rfl, by rw [e2] at h2; exact h2⟩)

/-- The RMW's `handlePropose` is `startPhase1` at slot `crt[id]` from a state with the same id,
store, copies and table, `crt[id]` raised. -/
theorem rmwI {rid cid : w32} {k : w64} {d : Dep} {oldV newV : w64}
    (h : stepClientRMW s rid cid k d oldV newV = .ok (s', o)) :
    ∃ t ps cs, t.id = s.id ∧ t.conf = s.conf ∧ t.inst = s.inst ∧
      t.crtInstance = (s.setCrt s.id (s.crt s.id + 1)).crtInstance ∧
      startPhase1 t s.id (s.crt s.id) 0 ps cs = .ok (s', o) := by
  unfold stepClientRMW at h; peel h
  have h' := (handlePropose_ok h).2.2
  unfold handleProposeBody at h'
  dsimp only at h'
  refine ⟨_, _, _, ?_, ?_, ?_, ?_, h'⟩
  · rfl
  · rfl
  · rfl
  · simp only [RState.setCrt, RState.crt]

def dgSet (dg : DepG) (q i : w32) (D : Deps) : DepG :=
  fun q' i' => if q' = q ∧ i' = i then some D else dg q' i'

theorem dgSet_le {q i : w32} {D : Deps} (h : dg q i = none) : DgLe dg (dgSet dg q i D) :=
  fun q' i' D' hD => by
    unfold dgSet; split
    · rename_i e; obtain ⟨rfl, rfl⟩ := e; rw [h] at hD; cases hD
    · exact hD

theorem sint_m1 : sint.Z (-1 : w32) = -1 := by decide

theorem sint_sub1 {x : w32} (h0 : 1 ≤ sint.Z x) (h1 : sint.Z x < SLOTS) :
    sint.Z (x - 1) = sint.Z x - 1 := by
  unfold SLOTS at h1; word

theorem at_m1 (k : Nat) (hk : k < 3) : sint.Z (Deps.at [-1, -1, -1, 0, 0] k) = -1 := by
  rcases k with _ | _ | _ | k <;> first | omega | decide

theorem not_strong_pre : ¬ Strong St.PREACCEPTED := by unfold Strong; decide

theorem dle_at {D D' : Deps} (h : DLe D D') (k : Nat) : sint.Z (D.at k) ≤ sint.Z (D'.at k) := h k

/-! ## The creation -/

/-- The creation's obligations: the table grows and covers the new instance, the new instance's
copy, the own row's `crt` grows by one, and the local obligations with the record and the creation
deps. -/
theorem li_rmw {rid cid : w32} {k : w64} {d : Dep} {oldV newV : w64} (C : CtxI rc κ dg s a)
    (hcl : s.crtInstance.length = 3)
    (hown : ∀ j, 0 ≤ sint.Z j → sint.Z j < sint.Z (s.crt (rid32 a)) → ∃ t, rc a (rid32 a) j = some t)
    (h : stepClientRMW s rid cid k d oldV newV = .ok (s', o)) :
    ∃ D, ConfLe s s' ∧
      (∃ hi, s'.confAt (rid32 a).toNat = some hi ∧
        sint.Z (s.crt (rid32 a)) ≤ sint.Z hi) ∧
      s'.inst (rid32 a) (s.crt (rid32 a)) ≠ none ∧
      (∀ j, 0 ≤ sint.Z j → sint.Z j < sint.Z (s'.crt (rid32 a)) →
        sint.Z j < sint.Z (s.crt (rid32 a)) ∨ j = s.crt (rid32 a)) ∧
      LocalI (addRec rc a κ (some (rid32 a, s.crt (rid32 a)))) (κ + 1)
        (dgSet dg (rid32 a) (s.crt (rid32 a)) D) s s' a o := by
  obtain ⟨t, ps, cs, hti, htc, htinst, htcrt, hsp⟩ := rmwI h
  rw [C.id] at hsp htcrt
  obtain ⟨cp, D0, ch, hi, -, ecrt, hps, hcb, hcm, hne, hlb, hbox, hl0, -, hD0, hua, rfl, hout⟩ := sp1I hsp
  have hid : t.id = rid32 a := hti.trans C.id
  have hD0' := hD0 hid.symm
  subst hD0'
  obtain ⟨hdle, hlen, hcov⟩ := updAttr_facts hua (by decide)
  have hconf1 : ∀ k, t.confAt k = s.confAt k := fun k => by unfold RState.confAt; rw [htc]
  have E := addRec_ext rc a κ (some (rid32 a, (s.crt (rid32 a))))
  obtain ⟨UC1, UC2, -⟩ := uc_facts (t.setInst (rid32 a) (s.crt (rid32 a)) cp) cs (rid32 a) (s.crt (rid32 a)) cp.seq
  have hrec := addRec_self (rc := rc) (a := a) (κ := κ) (q := rid32 a) (j := (s.crt (rid32 a)))
    (fun t ht => C.clock _ _ _ _ ht)
  have nsk : ∀ k, ¬ (t.id ≠ rid32 a ∧ BitVec.ofNat 32 k = rid32 a) := fun k ⟨h1, _⟩ => h1 hid
  have hcovA : Cov (addRec rc a κ (some (rid32 a, (s.crt (rid32 a))))) (κ + 1) (rid32 a) (s.crt (rid32 a)) cp.deps a none :=
    cov_new C.tab (fun r _ _ hi hh => hcov hne r.val r.isLt (nsk _) hi (by rw [hconf1]; exact hh))
      ⟨_, hrec.choose_spec.1, hrec.choose_spec.2.1⟩
  have hbox' := hbox
  simp only [inBox, decide_eq_true_eq] at hbox'
  obtain ⟨-, -, hi1, hi2⟩ := hbox'
  have hsr : SameRow (rid32 a) (s.crt (rid32 a)) cp.deps := by
    unfold SameRow
    rw [rid32_toNat]
    by_cases h1 : sint.Z (s.crt (rid32 a)) ≥ 1
    · have e2 := sint_sub1 h1 hi2
      obtain ⟨t1, ht1⟩ := hown (s.crt (rid32 a) - 1) (by omega) (by omega)
      obtain ⟨hh, e1, l1⟩ := C.tab a _ _ ht1
      have := hcov hne a.val a.isLt (nsk _) hh (by rw [hconf1]; exact e1)
      dsimp only at this
      omega
    · have := dle_at hdle a.val
      dsimp only at this
      have e3 : sint.Z (Deps.at [-1, -1, -1, 0, 0] a.val) = -1 := at_m1 a.val a.isLt
      omega
  refine ⟨cp.deps, confLe_of_eq htc |>.trans UC1, ?_, ?_, ?_, ?_⟩
  · refine UC2 hne ?_
    show (rid32 a).toNat < t.conf.length
    rw [htc, C.confLen, rid32_toNat]; exact a.isLt
  · rw [(updateConflicts_inst _ _ _ _ _).1, setInst_inst, if_pos ⟨rfl, rfl⟩]; simp
  · intro j h0 hlt
    have ec : (updateConflicts (t.setInst (rid32 a) (s.crt (rid32 a)) cp) cs (rid32 a)
        (s.crt (rid32 a)) cp.seq).crt (rid32 a) = s.crt (rid32 a) + 1 := by
      rw [uc_crt]
      show t.crt (rid32 a) = _
      unfold RState.crt; rw [htcrt]
      rw [show (s.setCrt (rid32 a) (s.crt (rid32 a) + 1)).crtInstance.getD (rid32 a).toNat 0 =
        (s.setCrt (rid32 a) (s.crt (rid32 a) + 1)).crt (rid32 a) from rfl]
      rw [crt_setCrt _ _ _ _ (by rw [hcl, rid32_toNat]; exact a.isLt), if_pos rfl]
      rfl
    rw [ec, zsucc hi1 hi2] at hlt
    by_cases e : sint.Z j < sint.Z (s.crt (rid32 a))
    · exact Or.inl e
    · exact Or.inr (BitVec.toInt_inj.1 (by unfold sint.Z at *; omega))
  · have hlen5 : 3 ≤ cp.deps.length := by rw [hlen]; decide
    have hdg : dgSet dg (rid32 a) (s.crt (rid32 a)) cp.deps (rid32 a) (s.crt (rid32 a)) =
        some cp.deps := by simp [dgSet]
    refine ⟨fun q j cp' hc => ?_, fun d' y hy => ?_⟩
    · rw [(updateConflicts_inst _ _ _ _ _).1, setInst_inst] at hc
      split at hc
      · rename_i e; obtain ⟨rfl, rfl⟩ := e; cases hc
        refine Or.inr ⟨fun _ _ => ⟨⟨hsr, ⟨a, hcovA⟩, fun hs => absurd (hps ▸ hs) not_strong_pre⟩,
          fun _ => ⟨hcovA, hlen5⟩⟩, fun _ _ _ _ => ⟨cp.deps, hdg, DLe.refl _⟩,
          fun lb hl _ => by rw [hlb lb hl]; intro r hr; cases hr⟩
      · rw [htinst] at hc; exact Or.inl hc
    · obtain ⟨x, rfl, hxr, hxi, hxb, hxd, -, hd⟩ := hout d' y hy
      have hda : a ≠ d' := fun e => hd (by rw [← e, hid])
      intro _
      rw [hxr, hxi, hxd]
      exact ⟨hlen5, hsr, ⟨a, hda, hcovA⟩, fun _ => hdg⟩

/-! ## startRecoveryForInstance -/

theorem candI_recRI {rc' : RecG} {κ' : Nat} {q i sid q' : w32} {c0 : Copy}
    (h : c0.cmds ≠ [] → c0.status ≠ St.NONE → ValI rc' κ' q i c0.deps c0.status) :
    CandI rc' κ' q i (recRI c0 sid q') := by
  unfold recRI
  split
  · rename_i hs
    intro r hr hc; cases hr; exact h hc (by rw [hs]; decide)
  · split
    · rename_i _ hs
      intro r hr hc; cases hr
      exact h hc (fun e => by rw [e] at hs; exact absurd hs (by decide))
    · intro r hr; cases hr

theorem li_recover {q i : w32} (C : CtxI rc κ dg s a)
    (hnn : ∀ c, s.inst q i = some c → 0 ≤ sint.Z c.ballot)
    (h : stepRecover s q i = .ok (s', o)) : StepI rc κ dg s s' a o none := by
  rcases stepRecover_cases h with ⟨rfl, rfl⟩ | ⟨c0, hc0, -, -, -, -, hmx, rfl, hbc⟩
  · exact stepI_same
  have hcw : CopyI (addRec rc a κ none) (κ + 1) dg q i a c0 := by
    rcases hc0 with hc | ⟨-, rfl⟩
    · exact cM (C.copies _ _ _ hc)
    · exact ⟨fun hn => absurd rfl hn, fun hn => absurd rfl hn, fun _ hl => by cases hl⟩
  have h0 : 0 ≤ sint.Z c0.ballot := by
    rcases hc0 with hc | ⟨-, rfl⟩
    · exact hnn _ hc
    · show 0 ≤ sint.Z (0 : w32); decide
  have hb : (recCopy c0 s.id q).ballot ≠ 0 := by
    intro e
    have k := (makeBallot_own (a := a) h0 hmx).1
    rw [← C.id] at k
    have k2 := pureA.own_pos k
    unfold recCopy at e; dsimp only at e; rw [e] at k2; exact absurd k2 (by decide)
  refine ⟨confLe_of_eq rfl, rfl, fun _ _ h => (by cases h), cpI_setInst rfl ⟨hcw.val,
    fun _ _ hb' _ => absurd hb' hb, fun lb hl _ => ?_⟩, fun d y hy => by rw [sentR_bcast hbc hy]; trivial⟩
  cases hl
  exact candI_recRI (fun h1 h2 => (hcw.val h1 h2).1)

/-! ## The restart of phase 1 (G9, G32) -/

theorem sint_pred {x : w32} (h0 : 0 ≤ sint.Z x) (h1 : sint.Z x < SLOTS) :
    sint.Z (x - 1) = sint.Z x - 1 := by
  unfold SLOTS at h1; word

theorem li_restart {q i b : w32} {ps : List Proposal} {cs : List Cmd} {c' : Copy} {D : Deps}
    (C : CtxI rc κ dg s a) (hv : cs ≠ [] → ∃ w, Cov rc (κ + 1) q i D w none) (hb : b ≠ 0)
    (h : startPhase1 (s.setInst q i c') q i b ps cs = .ok (s', o)) :
    StepI rc κ dg s s' a o (some (q, i)) := by
  obtain ⟨cp, D0, ch, hi, eid, ecrt, hps, hcb, hcm, hne, hlb, hbox, hl0, hD0a, hD0b, hua, rfl, hout⟩ :=
    sp1I h
  have hid : (s.setInst q i c').id = rid32 a := C.id
  obtain ⟨hdle, hlen, hcov⟩ := updAttr_facts hua (by rw [hl0]; decide)
  have hconf1 : ∀ k, (s.setInst q i c').confAt k = s.confAt k := fun k => rfl
  obtain ⟨UC1, UC2, -⟩ := uc_facts ((s.setInst q i c').setInst q i cp) cs q i cp.seq
  have hrec := addRec_self (rc := rc) (a := a) (κ := κ) (q := q) (j := i)
    (fun t ht => C.clock _ _ _ _ ht)
  have hcovA : Cov (addRec rc a κ (some (q, i))) (κ + 1) q i cp.deps a none := by
    refine cov_new C.tab (fun r hr _ hi hh => ?_) ⟨_, hrec.choose_spec.1, hrec.choose_spec.2.1⟩
    exact hcov hne r.val r.isLt (fun ⟨_, e⟩ => hr e) hi (by rw [hconf1]; exact hh)
  obtain ⟨w, hw⟩ := hv hne
  obtain ⟨τ, -, ⟨tw, htw, -⟩, -⟩ := hw
  have hbox' := hbox
  simp only [inBox, decide_eq_true_eq] at hbox'
  obtain ⟨hq0, hq3, hi1, hi2⟩ := hbox'
  have hql : q.toNat < 3 := toNat_lt_of_inBox hbox
  have hsr : SameRow q i cp.deps := by
    unfold SameRow
    by_cases hq : q = (s.setInst q i c').id
    · rw [hid] at hq; subst hq
      obtain ⟨t0, ht0, -⟩ := C.own w a i tw htw
      obtain ⟨hh, e1, l1⟩ := C.tab a _ _ ht0
      have := hcov hne a.val a.isLt (fun ⟨h1, _⟩ => h1 hid) hh (by rw [hconf1]; exact e1)
      dsimp only at this
      rw [rid32_toNat]; omega
    · have := dle_at hdle q.toNat
      dsimp only at this
      rw [hD0a hq, sint_pred hi1 hi2] at this
      omega
  refine ⟨(confLe_of_eq rfl).trans UC1, by rw [uc_crt]; rfl, ?_, ?_, ?_⟩
  · intro q' j e; cases e
    refine ⟨UC2 hne (by show q.toNat < s.conf.length; rw [C.confLen]; exact hql), ?_,
      Or.inr ⟨w, tw, htw⟩⟩
    rw [(updateConflicts_inst _ _ _ _ _).1, setInst_inst, if_pos ⟨rfl, rfl⟩]; simp
  · intro q' j cp' hc
    rw [(updateConflicts_inst _ _ _ _ _).1, setInst_inst] at hc
    split at hc
    · rename_i e; obtain ⟨rfl, rfl⟩ := e; cases hc
      refine Or.inr ⟨fun _ _ => ⟨⟨hsr, ⟨a, hcovA⟩, fun hs => absurd (hps ▸ hs) not_strong_pre⟩,
        fun _ => ⟨hcovA, by rw [hlen, hl0]; decide⟩⟩, fun _ _ hb' _ => absurd (hcb ▸ hb') hb,
        fun lb hl _ => by rw [hlb lb hl]; intro r hr; cases hr⟩
    · rename_i hne'
      rw [setInst_inst, if_neg hne'] at hc; exact Or.inl hc
  · intro d' y hy
    obtain ⟨x, rfl, hxr, hxi, hxb, hxd, -, hd⟩ := hout d' y hy
    have hda : a ≠ d' := fun e => hd (by rw [← e, hid])
    intro _
    rw [hxr, hxi, hxd]
    exact ⟨by rw [hlen, hl0]; decide, hsr, ⟨a, hda, hcovA⟩, fun h0 => absurd (hxb ▸ h0) hb⟩

end Perennial.gryff.pureA.AI
