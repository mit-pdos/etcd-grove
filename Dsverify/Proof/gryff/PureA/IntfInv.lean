/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/IntfInv.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AI, internal: **the interference invariant** `IInv c κ rc dg` (a separate structure, as unit
AW's `WInv`; its preservation uses `CInv` as a helper), and D1 from it (`interf_vals`, used by
`interf` in `GryffProof/Pure/Agree.lean`).

Clauses (see `IntfDefs.lean` for the vocabulary):
* the ghost's laws: records are older than the clock (`clock`), one instance per (replica, time)
  (`inj`), the owner of a row records each of its instances first (`own`), recorded instances are
  created (`born`), a creation deps entry belongs to a recorded instance (`dgRec`);
* the conflict tables (three rows, `confLen`): a recorded instance is below the table's row entry (`tab`); a replica has
  recorded every instance of its own row below its `crt` (`ownRow`);
* copies with commands, not NONE (`CopyI`): `ValI` (same row, a coverer, two if STRONG); a
  PREACCEPTED copy at `a` is covered by `a` (and has its deps' entries); the leader's own PREACCEPTED ballot-0 copy has deps at
  least the creation deps (`own0`); recovery candidates with commands (`CandI`) have `ValI`;
* messages to `d` (`MsgI`): a PreAccept (with its deps' entries) is covered by someone other than `d` (its sender), and at
  ballot 0 carries the creation deps; an OK PreAcceptReply is covered by someone other than `d` (the
  replier); a PreAcceptOK to the leader `d` names a replier `X ≠ d` covering the creation deps;
  Accepts, Commits with commands: same row and `Wp2`; PrepareReplies like copies.
-/
module

public import Dsverify.Proof.gryff.PureA.IntfDefs

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AI

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA
open Perennial.gryff.pureA.AW

/-- Pointwise deps order (signed). -/
def DLe (D D' : Deps) : Prop := ∀ k : Nat, sint.Z (D.at k) ≤ sint.Z (D'.at k)

theorem DLe.refl (D : Deps) : DLe D D := fun _ => Int.le_refl _
theorem DLe.trans {D1 D2 D3 : Deps} (h1 : DLe D1 D2) (h2 : DLe D2 D3) : DLe D1 D3 :=
  fun k => Int.le_trans (h1 k) (h2 k)

/-- A recovery candidate's facts. -/
def CandI (rc : RecG) (κ : Nat) (q i : w32) (ri : Option RecoveryInstance) : Prop :=
  ∀ r, ri = some r → r.cmds ≠ [] → ValI rc κ q i r.deps r.status

/-- Facts about replica `a`'s copy `cp` of instance `(q, i)`. -/
structure CopyI (rc : RecG) (κ : Nat) (dg : DepG) (q i : w32) (a : Fin 3) (cp : Copy) : Prop where
  val : cp.cmds ≠ [] → cp.status ≠ St.NONE → ValI rc κ q i cp.deps cp.status ∧
    (cp.status = St.PREACCEPTED → Cov rc κ q i cp.deps a none ∧ 3 ≤ cp.deps.length)
  own0 : cp.cmds ≠ [] → q = rid32 a → cp.ballot = 0 → cp.status = St.PREACCEPTED →
    ∃ D, dg q i = some D ∧ DLe D cp.deps
  cand : ∀ lb, cp.lb = some lb → ¬ isCommitted cp.status → CandI rc κ q i lb.recoveryInst

/-- Facts about a message in flight to `d`. -/
def MsgI (rc : RecG) (κ : Nat) (dg : DepG) (d : Fin 3) : Msg → Prop
  | .preAccept m => m.cmds ≠ [] → 3 ≤ m.deps.length ∧ SameRow m.replica m.inst m.deps ∧
      (∃ w, w ≠ d ∧ Cov rc κ m.replica m.inst m.deps w none) ∧
      (m.ballot = 0 → dg m.replica m.inst = some m.deps)
  | .preAcceptReply m => m.ok ≠ FALSE → SameRow m.replica m.inst m.deps ∧
      ∃ w, w ≠ d ∧ Cov rc κ m.replica m.inst m.deps w none
  | .preAcceptOK m => ∃ D, dg (rid32 d) m.inst = some D ∧
      ∃ X, X ≠ d ∧ Cov rc κ (rid32 d) m.inst D X none
  | .accept m => m.cmds ≠ [] → SameRow m.replica m.inst m.deps ∧ Wp2 rc κ m.replica m.inst m.deps
  | .commit m => m.cmds ≠ [] → SameRow m.replica m.inst m.deps ∧ Wp2 rc κ m.replica m.inst m.deps
  | .prepareReply m => m.cmds ≠ [] → m.status ≠ St.NONE →
      ValI rc κ m.replica m.inst m.deps m.status
  | _ => True

/-- **The interference invariant.** -/
structure IInv (c : Cfg gNet) (κ : Nat) (rc : RecG) (dg : DepG) : Prop where
  loc : ∀ a : Fin 3, Loc (c.st a)
  clock : ∀ w q j t, rc w q j = some t → t < κ
  inj : ∀ w q j q' j' t, rc w q j = some t → rc w q' j' = some t → q = q' ∧ j = j'
  own : ∀ w r j t, rc w (rid32 r) j = some t → ∃ t0, rc r (rid32 r) j = some t0 ∧ t0 ≤ t
  born : ∀ w q j t, rc w q j = some t → ∃ r : Fin 3, q = rid32 r ∧
    sint.Z j < sint.Z ((c.st r).crt (rid32 r))
  dgRec : ∀ q j D, dg q j = some D → ∃ r : Fin 3, ∃ t, q = rid32 r ∧ rc r q j = some t
  confLen : ∀ a, (c.st a).conf.length = 3
  tab : ∀ (a r : Fin 3) j t, rc a (rid32 r) j = some t →
    ∃ hi, (c.st a).confAt r.val = some hi ∧ sint.Z j ≤ sint.Z hi
  ownRow : ∀ (a : Fin 3) j, 0 ≤ sint.Z j → sint.Z j < sint.Z ((c.st a).crt (rid32 a)) →
    ∃ t, rc a (rid32 a) j = some t
  copies : ∀ a q i cp, cpOf c a q i = some cp → CopyI rc κ dg q i a cp
  msgs : ∀ d m, m ∈ c.inflight d → MsgI rc κ dg d m

/-! ## The initial configuration -/

theorem intf_init : IInv (Cfg.init gNet) 0 (fun _ _ _ => none) (fun _ _ => none) where
  loc a := loc_init a
  clock _ _ _ _ h := by cases h
  inj _ _ _ _ _ _ h := by cases h
  own _ _ _ _ h := by cases h
  born _ _ _ _ h := by cases h
  dgRec _ _ _ h := by cases h
  confLen _ := rfl
  tab _ _ _ _ h := by cases h
  ownRow a j h0 hlt := by
    exfalso
    have e : sint.Z ((Cfg.init gNet).st a |>.crt (rid32 a)) = 0 := by
      obtain ⟨a, ha⟩ := a
      rcases a with _ | _ | _ | a <;> first | omega | rfl
    omega
  copies _ _ _ _ h := by cases h
  msgs _ _ h := by cases h

/-! ## D1 from the invariant -/

/-- Two values with commands, same row and `Wp2`, of distinct instances: one depends on the
other. -/
theorem interf_vals {c : Cfg gNet} {κ : Nat} {rc : RecG} {dg : DepG} (I : IInv c κ rc dg)
    {q i q' i' : w32} {D D' : Deps} (hv : SameRow q i D ∧ Wp2 rc κ q i D)
    (hv' : SameRow q' i' D' ∧ Wp2 rc κ q' i' D') (hne : (q, i) ≠ (q', i')) :
    sint.Z i' ≤ sint.Z (D.at q'.toNat) ∨ sint.Z i ≤ sint.Z (D'.at q.toNat) := by
  have row : ∀ {q i D}, Wp2 rc κ q i D → ∃ r : Fin 3, q = rid32 r := by
    intro q i D h
    obtain ⟨w1, -, -, -, ⟨τ, -, ⟨t, ht, -⟩, -⟩, -⟩ := h
    obtain ⟨r, hr, -⟩ := I.born _ _ _ _ ht
    exact ⟨r, hr⟩
  obtain ⟨L, rfl⟩ := row hv.2
  obtain ⟨R, rfl⟩ := row hv'.2
  by_cases hLR : L = R
  · subst hLR
    have hii : i ≠ i' := fun e => hne (by rw [e])
    have s1 := hv.1; have s2 := hv'.1
    unfold SameRow at s1 s2
    have : sint.Z i ≠ sint.Z i' := fun e => hii (BitVec.toInt_inj.1 e)
    omega
  · rw [rid32_toNat, rid32_toNat]
    exact interf_core I.own I.inj hLR hv.2 hv'.2

/-- A committed copy's value. -/
theorem copy_committed {c : Cfg gNet} {κ : Nat} {rc : RecG} {dg : DepG} (I : IInv c κ rc dg)
    {a : Fin 3} {q i : w32} {cp : Copy} (h : (c.st a).inst q i = some cp)
    (hs : cp.status = St.COMMITTED ∨ cp.status = St.EXECUTED) (hc : cp.cmds ≠ []) :
    SameRow q i cp.deps ∧ Wp2 rc κ q i cp.deps := by
  have hn : cp.status ≠ St.NONE := by rcases hs with e | e <;> rw [e] <;> decide
  obtain ⟨⟨h1, -, h3⟩, -⟩ := (I.copies a q i cp h).val hc hn
  exact ⟨h1, h3 (by unfold Strong; rcases hs with e | e <;> simp [e])⟩

theorem commit_committed {c : Cfg gNet} {κ : Nat} {rc : RecG} {dg : DepG} (I : IInv c κ rc dg)
    {d : Fin 3} {m : ECommitM} (h : Msg.commit m ∈ c.inflight d) (hc : m.cmds ≠ []) :
    SameRow m.replica m.inst m.deps ∧ Wp2 rc κ m.replica m.inst m.deps :=
  I.msgs d _ h hc

theorem reply_committed {c : Cfg gNet} {κ : Nat} {rc : RecG} {dg : DepG} (I : IInv c κ rc dg)
    {d : Fin 3} {m : PrepareReplyM} (h : Msg.prepareReply m ∈ c.inflight d)
    (hs : m.status = St.COMMITTED ∨ m.status = St.EXECUTED) (hc : m.cmds ≠ []) :
    SameRow m.replica m.inst m.deps ∧ Wp2 rc κ m.replica m.inst m.deps := by
  have hn : m.status ≠ St.NONE := by rcases hs with e | e <;> rw [e] <;> decide
  obtain ⟨h1, -, h3⟩ := I.msgs d _ h hc hn
  exact ⟨h1, h3 (by unfold Strong; rcases hs with e | e <;> simp [e])⟩

end Perennial.gryff.pureA.AI
