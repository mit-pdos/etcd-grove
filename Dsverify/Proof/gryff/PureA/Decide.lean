/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/Decide.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1, internal: A3 at a recovery's decision (`handlePrepareReply`, `Model/StepRecovery.lean`
`stepPrepareReply`), the riskiest step of agreement.

The recoverer `R` at ballot `b` keeps a candidate `ri` (`lb.recoveryInst`). Its meaning (`RIOk`):
every *member* of the recovery's quorum so far (`R` itself, its snapshot taken by
`startRecoveryForInstance`) satisfies `MemOk` w.r.t. `ri`: its ballot is `≥ b`, its votes below `b`
are at most `ri`'s vbal (and `ri` is ACCEPTED if it has any), if it pre-accepted `L`'s ballot-0
PreAccept unchanged then `ri` is ACCEPTED or counts an unchanged copy (or a restart below `b`
blocks the fast path), and if it is the leader then `ri` is ACCEPTED or `leaderResponded`; and `ri`
itself is sound (`RICore`). A reply in flight to `R` (`RepOk`) carries its sender's copy as it was
when it promised `b`, with the same kind of facts.

`upd1`/`upd2` are the code's two updates of the candidate by a reply (the ACCEPTED rule, G16; the
pre-accepted rule, G24). `memOk_upd_R`, `memOk_upd_Y`, `riCore_upd` transport the facts; the
decision (`decide_acc`, `decide_eq`, `decide_restart`, `decide_noop`) then follows from two distinct
members (`R` and the replier) with `AInv`.
-/
module

public import Dsverify.Proof.gryff.Pure.Run
public import Dsverify.Proof.gryff.PureA.Abstract

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA

open Perennial Perennial.gryff.model Perennial.gryff.pure

/-- An instance's value `(cmds, seq, deps, base)` (`Pure/Agree.lean`'s `IVal`, as a tuple: this
unit's modules come before `Pure/Agree.lean`, whose proofs use them). -/
abbrev Val := List Cmd × w32 × Deps × ValTag

/-- A recovery candidate's value. -/
def _root_.Perennial.gryff.model.RecoveryInstance.valA (r : RecoveryInstance) : Val :=
  (r.cmds, r.seq, r.deps, r.base)

/-- A prepare reply's value. -/
def _root_.Perennial.gryff.model.PrepareReplyM.valA (m : PrepareReplyM) : Val :=
  (m.cmds, m.seq, m.deps, m.base)

/-- A copy's value. -/
def _root_.Perennial.gryff.model.Copy.valA (c : Copy) : Val := (c.cmds, c.seq, c.deps, c.base)

/-- A commit's value. -/
def _root_.Perennial.gryff.model.ECommitM.valA (m : ECommitM) : Val := (m.cmds, m.seq, m.deps, m.base)

@[simp] theorem riOf_valA (m : PrepareReplyM) (c : w64) (lr : Bool) : (riOf m c lr).valA = m.valA := rfl
@[simp] theorem riOf_status (m : PrepareReplyM) (c : w64) (lr : Bool) : (riOf m c lr).status = m.status := rfl
@[simp] theorem riOf_vbal (m : PrepareReplyM) (c : w64) (lr : Bool) : (riOf m c lr).vbal = m.vbal := rfl
@[simp] theorem riOf_cnt (m : PrepareReplyM) (c : w64) (lr : Bool) :
    (riOf m c lr).preAcceptCount = c := rfl
@[simp] theorem riOf_lr (m : PrepareReplyM) (c : w64) (lr : Bool) :
    (riOf m c lr).leaderResponded = lr := rfl

/-! ## The code's updates of the candidate -/

/-- The ACCEPTED rule (G16): an ACCEPTED reply replaces a candidate that is not ACCEPTED or has a
lower vbal. -/
def upd1 (ri : Option RecoveryInstance) (m : PrepareReplyM) : Option RecoveryInstance :=
  if m.status = St.ACCEPTED then
    let better : Bool := match ri with
      | none => true
      | some ri => (decide (ri.status ≠ St.ACCEPTED)).or (slt ri.vbal m.vbal)
    if better then some (riOf m 0 false) else ri
  else ri

/-- The candidate is below ACCEPTED. -/
def belowB (ri : Option RecoveryInstance) : Bool := match ri with
  | none => true
  | some ri => slt ri.status St.ACCEPTED

/-- The reply reports `L`'s ballot-0 value unchanged (G24). -/
def unchangedB (m : PrepareReplyM) : Bool :=
  ((m.status == St.PREACCEPTED_EQ).and (m.vbal == 0)).and (m.acceptorId != m.replica)

/-- The pre-accepted rule (G24). -/
def upd2 (ri : Option RecoveryInstance) (m : PrepareReplyM) : Option RecoveryInstance :=
  if (m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ) ∧ belowB ri = true then
    let count : w64 := if unchangedB m then 1 else 0
    match ri with
    | none => some (riOf m count false)
    | some r =>
      if (unchangedB m).and (sgt r.preAcceptCount 0) then
        some { r with preAcceptCount := r.preAcceptCount + 1 }
      else if unchangedB m then some (riOf m 1 r.leaderResponded)
      else some r
  else ri

/-! ## The facts -/

variable (g : Gh Val) (bal : Fin 3 → Option Int) (L : Fin 3) (b : Int)

/-- The candidate is ACCEPTED with vbal `≥ b'`. -/
def AccGe (ri : Option RecoveryInstance) (b' : Int) : Prop :=
  ∃ r, ri = some r ∧ r.status = St.ACCEPTED ∧ b' ≤ sint.Z r.vbal

/-- The candidate is ACCEPTED, or counts an unchanged copy. -/
def AccOrCnt (ri : Option RecoveryInstance) : Prop :=
  ∃ r, ri = some r ∧ (r.status = St.ACCEPTED ∨ 1 ≤ sint.Z r.preAcceptCount)

/-- The candidate is ACCEPTED, or the leader responded. -/
def AccOrLr (ri : Option RecoveryInstance) : Prop :=
  ∃ r, ri = some r ∧ (r.status = St.ACCEPTED ∨ r.leaderResponded = true)

/-- A restart at a ballot in `(0, b]` (it blocks the fast path: `rst_safe`). -/
def RstBelow : Prop := ∃ b', 0 < b' ∧ b' ≤ b ∧ g.rst b'

/-- A member `a` of the recovery's quorum, w.r.t. the candidate `ri`. -/
structure MemOk (ri : Option RecoveryInstance) (a : Fin 3) : Prop where
  bal : ∃ B, bal a = some B ∧ b ≤ B
  votes : ∀ b' u, b' < b → g.acc a b' u → AccGe ri b'
  eqd : a ≠ L → g.eq a → AccOrCnt ri ∨ RstBelow g b
  lead : a = L → AccOrLr ri

/-- The candidate's soundness. -/
structure RICore (ri : Option RecoveryInstance) : Prop where
  accd : ∀ r, ri = some r → r.status = St.ACCEPTED →
    g.prop (sint.Z r.vbal) r.valA ∧ 0 ≤ sint.Z r.vbal ∧ sint.Z r.vbal < b
  cnt : ∀ r, ri = some r → 0 ≤ sint.Z r.preAcceptCount ∧ sint.Z r.preAcceptCount ≤ 2
  cntEq : ∀ r, ri = some r → 1 ≤ sint.Z r.preAcceptCount →
    r.status = St.PREACCEPTED_EQ ∧ r.vbal = 0 ∧ g.cre r.valA
  lr : ∀ r, ri = some r → r.leaderResponded = true →
    (∃ B, bal L = some B ∧ 0 < B) ∧ ∀ v, ¬ g.fast v
  stOk : ∀ r, ri = some r →
    r.status = St.PREACCEPTED ∨ r.status = St.PREACCEPTED_EQ ∨ r.status = St.ACCEPTED

/-- A reply `m` (OK, at ballot `b`, not COMMITTED/EXECUTED) from acceptor `Y`: its copy when it
promised `b`. -/
structure RepOk (Y : Fin 3) (m : PrepareReplyM) : Prop where
  bal : ∃ B, bal Y = some B ∧ b ≤ B
  votes : ∀ b' u, b' < b → g.acc Y b' u → m.status = St.ACCEPTED ∧ b' ≤ sint.Z m.vbal
  accd : m.status = St.ACCEPTED → g.acc Y (sint.Z m.vbal) m.valA ∧ sint.Z m.vbal < b
  eqd : Y ≠ L → g.eq Y →
    m.status = St.ACCEPTED ∨ (m.status = St.PREACCEPTED_EQ ∧ m.vbal = 0) ∨ RstBelow g b
  lead : Y = L → m.status ≠ St.NONE ∧ ∀ v, ¬ g.fast v
  cre : m.status = St.PREACCEPTED_EQ → m.vbal = 0 → Y ≠ L → g.cre m.valA
  stOk : m.status = St.NONE ∨ m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ ∨
    m.status = St.ACCEPTED
  /-- `acceptorId = replica` iff the sender is the leader -/
  isL : m.acceptorId = m.replica ↔ Y = L

/-! ## Transport through the updates -/

section upd
variable {g bal L b}

theorem slt_iff {n : Nat} (x y : BitVec n) : slt x y = true ↔ sint.Z x < sint.Z y := by
  simp [slt]

theorem sgt_iff {n : Nat} (x y : BitVec n) : sgt x y = true ↔ sint.Z y < sint.Z x := by
  simp [sgt, slt]

theorem st_ne : St.ACCEPTED ≠ St.PREACCEPTED ∧ St.ACCEPTED ≠ St.PREACCEPTED_EQ ∧
    St.PREACCEPTED ≠ St.PREACCEPTED_EQ ∧ St.NONE ≠ St.ACCEPTED ∧ St.NONE ≠ St.PREACCEPTED ∧
    St.NONE ≠ St.PREACCEPTED_EQ := by decide

/-- `upd1` keeps an ACCEPTED candidate ACCEPTED with a vbal at least as large. -/
theorem upd1_accGe {ri : Option RecoveryInstance} {m : PrepareReplyM} {b' : Int} (h : AccGe ri b') :
    AccGe (upd1 ri m) b' := by
  obtain ⟨r, rfl, hs, hv⟩ := h
  unfold upd1
  split
  · rename_i hm
    simp only [hs, ne_eq, not_true_eq_false, decide_false, Bool.false_or]
    split
    · rename_i hb
      rw [slt_iff] at hb
      exact ⟨_, rfl, by simp [hm], by simp; omega⟩
    · exact ⟨r, rfl, hs, hv⟩
  · exact ⟨r, rfl, hs, hv⟩

/-- `upd2` leaves an ACCEPTED candidate alone. -/
theorem upd2_acc {ri : Option RecoveryInstance} {m : PrepareReplyM} {r : RecoveryInstance}
    (h : ri = some r) (hs : r.status = St.ACCEPTED) : upd2 ri m = ri := by
  subst h
  unfold upd2
  have : belowB (some r) = false := by simp [belowB, hs, slt, St.ACCEPTED]
  simp [this]

theorem upd2_accGe {ri : Option RecoveryInstance} {m : PrepareReplyM} {b' : Int} (h : AccGe ri b') :
    AccGe (upd2 ri m) b' := by
  obtain ⟨r, hr, hs, hv⟩ := h
  rw [upd2_acc hr hs]; exact ⟨r, hr, hs, hv⟩

theorem upd1_not_acc {ri : Option RecoveryInstance} {m : PrepareReplyM}
    (h : m.status ≠ St.ACCEPTED) : upd1 ri m = ri := by
  simp [upd1, h]

/-- An ACCEPTED reply leaves an ACCEPTED candidate of vbal `≥` the reply's: the reply's own copy, or
the old candidate (ACCEPTED). -/
theorem upd1_acc {ri : Option RecoveryInstance} {m : PrepareReplyM} (h : m.status = St.ACCEPTED) :
    ∃ r, upd1 ri m = some r ∧ r.status = St.ACCEPTED ∧ sint.Z m.vbal ≤ sint.Z r.vbal ∧
      (r = riOf m 0 false ∨ ri = some r) := by
  unfold upd1
  simp only [h, ite_true]
  rcases ri with _ | r
  · exact ⟨_, rfl, by simp [h], by simp, Or.inl rfl⟩
  · by_cases hs : r.status = St.ACCEPTED
    · by_cases hv : sint.Z r.vbal < sint.Z m.vbal
      · have : slt r.vbal m.vbal = true := (slt_iff _ _).2 hv
        simp only [hs, ne_eq, not_true_eq_false, decide_false, this, Bool.false_or, ite_true]
        exact ⟨_, rfl, by simp [h], by simp, Or.inl rfl⟩
      · have : slt r.vbal m.vbal = false := by simpa [slt] using hv
        simp only [hs, ne_eq, not_true_eq_false, decide_false, this, Bool.false_or]
        exact ⟨r, rfl, hs, by omega, Or.inr rfl⟩
    · simp only [hs, ne_eq, not_false_eq_true, decide_true, Bool.true_or, ite_true]
      exact ⟨_, rfl, by simp [h], by simp, Or.inl rfl⟩

theorem upd2_not_pre {ri : Option RecoveryInstance} {m : PrepareReplyM}
    (h : ¬ (m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ)) : upd2 ri m = ri := by
  simp only [upd2]; rw [if_neg (fun h' => h h'.1)]

theorem upd2_not_below {ri : Option RecoveryInstance} {m : PrepareReplyM}
    (h : belowB ri = false) : upd2 ri m = ri := by
  simp only [upd2]; rw [if_neg (fun h' => by rw [h] at h'; exact Bool.false_ne_true h'.2)]

theorem belowB_false {r : RecoveryInstance}
    (hs : r.status = St.PREACCEPTED ∨ r.status = St.PREACCEPTED_EQ ∨ r.status = St.ACCEPTED) :
    belowB (some r) = false ↔ r.status = St.ACCEPTED := by
  rcases hs with hs | hs | hs <;> simp [belowB, hs, slt, St.ACCEPTED, St.PREACCEPTED, St.PREACCEPTED_EQ] <;> decide

/-- The pre-accepted rule on no candidate. -/
theorem upd2_pre_none {m : PrepareReplyM}
    (hm : m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ) :
    upd2 none m = some (riOf m (if unchangedB m then 1 else 0) false) := by
  simp only [upd2]; rw [if_pos ⟨hm, rfl⟩]

/-- The pre-accepted rule on a candidate below ACCEPTED. -/
theorem upd2_pre_some {r : RecoveryInstance} {m : PrepareReplyM}
    (hm : m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ) (hb : belowB (some r) = true) :
    upd2 (some r) m =
        if (unchangedB m).and (sgt r.preAcceptCount 0) then
          some { r with preAcceptCount := r.preAcceptCount + 1 }
        else if unchangedB m then some (riOf m 1 r.leaderResponded)
        else some r := by
  simp only [upd2]; rw [if_pos ⟨hm, hb⟩]

theorem unchangedB_iff (m : PrepareReplyM) : unchangedB m = true ↔
    m.status = St.PREACCEPTED_EQ ∧ m.vbal = 0 ∧ m.acceptorId ≠ m.replica := by
  simp [unchangedB, Bool.and_eq_true, and_assoc]

end upd

/-- The candidate's count is at most 1 (between replies: only the deciding reply can add a second
unchanged copy). -/
def Cnt1 (ri : Option RecoveryInstance) : Prop := ∀ r, ri = some r → sint.Z r.preAcceptCount ≤ 1

/-- The recoverer's candidate between replies. -/
structure RIOk (R : Fin 3) (ri : Option RecoveryInstance) : Prop where
  mem : MemOk g bal L b ri R
  core : RICore g bal L b ri
  cnt1 : Cnt1 ri

/-- The combined update. -/
def upd (ri : Option RecoveryInstance) (m : PrepareReplyM) : Option RecoveryInstance :=
  upd2 (upd1 ri m) m

section transport
variable {g bal L b}

theorem accGe_upd {ri : Option RecoveryInstance} {m : PrepareReplyM} {b' : Int} (h : AccGe ri b') :
    AccGe (upd ri m) b' := upd2_accGe (upd1_accGe h)

theorem stOk_cases {r : RecoveryInstance}
    (hs : r.status = St.PREACCEPTED ∨ r.status = St.PREACCEPTED_EQ ∨ r.status = St.ACCEPTED) :
    r.status = St.ACCEPTED ∨ belowB (some r) = true := by
  by_cases h : r.status = St.ACCEPTED
  · exact Or.inl h
  · right
    cases hb : belowB (some r)
    · exact absurd ((belowB_false hs).1 hb) h
    · rfl

/-- `AccOrCnt` survives the updates (a counted candidate is EQ, below ACCEPTED, count `≤ 2`). -/
theorem accOrCnt_upd {ri : Option RecoveryInstance} {m : PrepareReplyM} (hc : RICore g bal L b ri)
    (h : AccOrCnt ri) : AccOrCnt (upd ri m) := by
  obtain ⟨r, rfl, hr⟩ := h
  rcases hr with hs | hcnt
  · obtain ⟨r', h1, h2, _⟩ := upd1_accGe (m := m) (b' := sint.Z r.vbal) ⟨r, rfl, hs, Int.le_refl _⟩
    exact ⟨r', by unfold upd; rw [h1, upd2_acc rfl h2], Or.inl h2⟩
  · obtain ⟨hEq, _, _⟩ := hc.cntEq r rfl hcnt
    have hc2 := hc.cnt r rfl
    by_cases hm : m.status = St.ACCEPTED
    · obtain ⟨r', h1, h2, _⟩ := upd1_acc (ri := some r) hm
      exact ⟨r', by unfold upd; rw [h1, upd2_acc rfl h2], Or.inl h2⟩
    · unfold upd; rw [upd1_not_acc hm]
      by_cases hp : m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ
      · have hb : belowB (some r) = true := by
          rcases stOk_cases (hc.stOk r rfl) with h' | h'
          · rw [hEq] at h'; exact absurd h' (by decide)
          · exact h'
        rw [upd2_pre_some hp hb]
        have hsg : sgt r.preAcceptCount 0 = true := by
          rw [sgt_iff]; simp; omega
        by_cases hu : unchangedB m = true
        · simp only [hu, hsg, Bool.and_self, ite_true]
          refine ⟨_, rfl, Or.inr ?_⟩
          simp only
          word
        · simp only [Bool.not_eq_true] at hu
          simp only [hu, Bool.false_and, Bool.false_eq_true, ite_false]
          exact ⟨r, rfl, Or.inr hcnt⟩
      · rw [upd2_not_pre hp]; exact ⟨r, rfl, Or.inr hcnt⟩

/-- `AccOrLr` survives the updates. -/
theorem accOrLr_upd {ri : Option RecoveryInstance} {m : PrepareReplyM} (hc : RICore g bal L b ri)
    (h : AccOrLr ri) : AccOrLr (upd ri m) := by
  obtain ⟨r, rfl, hr⟩ := h
  rcases hr with hs | hlr
  · obtain ⟨r', h1, h2, _⟩ := upd1_accGe (m := m) (b' := sint.Z r.vbal) ⟨r, rfl, hs, Int.le_refl _⟩
    exact ⟨r', by unfold upd; rw [h1, upd2_acc rfl h2], Or.inl h2⟩
  · by_cases hm : m.status = St.ACCEPTED
    · obtain ⟨r', h1, h2, _⟩ := upd1_acc (ri := some r) hm
      exact ⟨r', by unfold upd; rw [h1, upd2_acc rfl h2], Or.inl h2⟩
    · unfold upd; rw [upd1_not_acc hm]
      by_cases hp : m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ
      · rcases stOk_cases (hc.stOk r rfl) with h' | hb
        · rw [upd2_acc rfl h']; exact ⟨r, rfl, Or.inl h'⟩
        rw [upd2_pre_some hp hb]
        split
        · exact ⟨_, rfl, Or.inr hlr⟩
        · split
          · exact ⟨_, rfl, Or.inr (by simpa using hlr)⟩
          · exact ⟨r, rfl, Or.inr hlr⟩
      · rw [upd2_not_pre hp]; exact ⟨r, rfl, Or.inr hlr⟩

/-- A member stays a member through the updates. -/
theorem memOk_upd {ri : Option RecoveryInstance} {m : PrepareReplyM} {a : Fin 3}
    (hc : RICore g bal L b ri) (h : MemOk g bal L b ri a) : MemOk g bal L b (upd ri m) a where
  bal := h.bal
  votes b' u hb hu := accGe_upd (h.votes b' u hb hu)
  eqd ha he := (h.eqd ha he).imp_left (accOrCnt_upd hc)
  lead ha := accOrLr_upd hc (h.lead ha)

theorem cnt_succ {c : w64} (h0 : 0 ≤ sint.Z c) (h1 : sint.Z c ≤ 2) : sint.Z (c + 1) = sint.Z c + 1 := by
  word

theorem sgt0_iff {c : w64} : sgt c 0 = true ↔ 0 < sint.Z c := by
  rw [sgt_iff]; simp

/-- The replier becomes a member (unless it is the leader reporting a pre-accepted copy below an
ACCEPTED-free candidate: then the code returns early, setting `leaderResponded`). -/
theorem memOk_upd_Y {ri : Option RecoveryInstance} {m : PrepareReplyM} {Y : Fin 3}
    (hr : RepOk g bal L b Y m) (hc : RICore g bal L b ri)
    (hnot : ¬ (Y = L ∧ (m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ) ∧
      belowB (upd1 ri m) = true)) : MemOk g bal L b (upd ri m) Y where
  bal := hr.bal
  votes b' u hb hu := by
    obtain ⟨hm, hle⟩ := hr.votes b' u hb hu
    obtain ⟨r', h1, h2, h3, _⟩ := upd1_acc (ri := ri) hm
    exact ⟨r', by unfold upd; rw [h1, upd2_acc rfl h2], h2, Int.le_trans hle h3⟩
  eqd hY he := by
    rcases hr.eqd hY he with hm | ⟨hm, hv⟩ | hrst
    · obtain ⟨r', h1, h2, _⟩ := upd1_acc (ri := ri) hm
      exact Or.inl ⟨r', by unfold upd; rw [h1, upd2_acc rfl h2], Or.inl h2⟩
    · left
      have hu : unchangedB m = true :=
        (unchangedB_iff m).2 ⟨hm, hv, fun h => hY (hr.isL.1 h)⟩
      have hna : m.status ≠ St.ACCEPTED := by rw [hm]; decide
      have hp : m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ := Or.inr hm
      unfold upd; rw [upd1_not_acc hna]
      rcases ri with _ | r
      · rw [upd2_pre_none hp]; refine ⟨_, rfl, Or.inr ?_⟩; simp [hu]
      · rcases stOk_cases (hc.stOk r rfl) with h' | hb
        · rw [upd2_acc rfl h']; exact ⟨r, rfl, Or.inl h'⟩
        rw [upd2_pre_some hp hb]
        obtain ⟨c0, c2⟩ := hc.cnt r rfl
        by_cases hs : sgt r.preAcceptCount 0 = true
        · simp only [hu, hs, Bool.and_self, ite_true]
          refine ⟨_, rfl, Or.inr ?_⟩
          simp only; rw [cnt_succ c0 c2]; omega
        · simp only [Bool.not_eq_true] at hs
          simp only [hu, hs, Bool.and_false, Bool.false_eq_true, ite_false, ite_true]
          exact ⟨_, rfl, Or.inr (by simp)⟩
    · exact Or.inr hrst
  lead hY := by
    have hn := (hr.lead hY).1
    by_cases hm : m.status = St.ACCEPTED
    · obtain ⟨r', h1, h2, _⟩ := upd1_acc (ri := ri) hm
      exact ⟨r', by unfold upd; rw [h1, upd2_acc rfl h2], Or.inl h2⟩
    · have hp : m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ := by
        rcases hr.stOk with h | h | h | h
        · exact absurd h hn
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hm
      have hb : belowB (upd1 ri m) = false := by
        cases h : belowB (upd1 ri m)
        · rfl
        · exact absurd ⟨hY, hp, h⟩ hnot
      rw [upd1_not_acc hm] at hb
      rcases ri with _ | r
      · simp [belowB] at hb
      · have hs := (belowB_false (hc.stOk r rfl)).1 hb
        unfold upd; rw [upd1_not_acc hm, upd2_acc rfl hs]
        exact ⟨r, rfl, Or.inl hs⟩

/-- The candidate stays sound through the updates (its count may reach 2). -/
theorem riCore_upd {ri : Option RecoveryInstance} {m : PrepareReplyM} {Y : Fin 3}
    (hA : AInv g bal L) (hr : RepOk g bal L b Y m) (hc : RICore g bal L b ri) (hc1 : Cnt1 ri) :
    RICore g bal L b (upd ri m) := by
  by_cases hm : m.status = St.ACCEPTED
  · obtain ⟨r', h1, h2, _, h4⟩ := upd1_acc (ri := ri) hm
    have he : upd ri m = some r' := by unfold upd; rw [h1, upd2_acc rfl h2]
    rw [he]
    rcases h4 with rfl | rfl
    · obtain ⟨hacc, hlt⟩ := hr.accd hm
      have hp := hA.acc_prop _ _ _ hacc
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro r hr' <;> cases hr'
      · intro _; exact ⟨hp, hA.prop_nonneg _ _ hp, hlt⟩
      · simp
      · simp
      · simp
      · simp [hm]
    · exact hc
  · unfold upd; rw [upd1_not_acc hm]
    by_cases hp : m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ
    · have hna : ∀ r : RecoveryInstance, r.status = m.status → r.status ≠ St.ACCEPTED := by
        intro r h; rw [h]; exact hm
      have hcre : unchangedB m = true → g.cre m.valA := by
        intro hu
        obtain ⟨h1, h2, h3⟩ := (unchangedB_iff m).1 hu
        exact hr.cre h1 h2 (fun h => h3 (hr.isL.2 h))
      have hst : ∀ r : RecoveryInstance, r.status = m.status →
          r.status = St.PREACCEPTED ∨ r.status = St.PREACCEPTED_EQ ∨ r.status = St.ACCEPTED := by
        intro r h; rw [h]; rcases hp with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      rcases ri with _ | r
      · rw [upd2_pre_none hp]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro r hr' <;> cases hr'
        · intro h; exact absurd h (hna _ rfl)
        · by_cases hu : unchangedB m = true <;> simp [hu]
        · intro h1
          by_cases hu : unchangedB m = true
          · obtain ⟨e1, e2, _⟩ := (unchangedB_iff m).1 hu
            exact ⟨e1, e2, hcre hu⟩
          · simp [hu] at h1
        · simp
        · exact hst _ rfl
      · rcases stOk_cases (hc.stOk r rfl) with h' | hb
        · rw [upd2_acc rfl h']; exact hc
        rw [upd2_pre_some hp hb]
        obtain ⟨c0, c2⟩ := hc.cnt r rfl
        have c1 := hc1 r rfl
        split
        · rename_i hs
          simp only [Bool.and_eq_true] at hs
          have hpos := sgt0_iff.1 hs.2
          refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro r' hr' <;> cases hr'
          · exact hc.accd r rfl
          · simp only; rw [cnt_succ c0 c2]; omega
          · intro _; exact hc.cntEq r rfl (by omega)
          · exact hc.lr r rfl
          · exact hc.stOk r rfl
        · split
          · rename_i _ hu
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro r' hr' <;> cases hr'
            · intro h; exact absurd h (hna _ rfl)
            · simp
            · intro _
              obtain ⟨e1, e2, _⟩ := (unchangedB_iff m).1 hu
              exact ⟨e1, e2, hcre hu⟩
            · exact hc.lr r rfl
            · exact hst _ rfl
          · exact hc
    · rw [upd2_not_pre hp]; exact hc

end transport

/-! ## The leader's pre-accepted reply: `leaderResponded`, no decision -/

/-- `{ ri with leaderResponded := true }`. -/
def setLr (r : RecoveryInstance) : RecoveryInstance := { r with leaderResponded := true }

section lret
variable {g bal L b}

/-- The leader's pre-accepted reply below an ACCEPTED-free candidate: the candidate (the reply's
copy if there was none) with `leaderResponded` set keeps `RIOk`. -/
theorem riOk_lret {R Y : Fin 3} {ri : Option RecoveryInstance} {m : PrepareReplyM}
    (hA : AInv g bal L) (hb : 0 < b) (hI : RIOk g bal L b R ri) (hr : RepOk g bal L b Y m)
    (hYL : Y = L) (hp : m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ) :
    ∃ r, upd ri m = some r ∧ RIOk g bal L b R (some (setLr r)) := by
  have hna : m.status ≠ St.ACCEPTED := by rcases hp with h | h <;> rw [h] <;> decide
  have hu : unchangedB m = false := by
    cases h : unchangedB m
    · rfl
    · exact absurd (hr.isL.2 hYL) ((unchangedB_iff m).1 h).2.2
  have hmem := memOk_upd (m := m) hI.core hI.mem
  have hcore := riCore_upd hA hr hI.core hI.cnt1
  -- the updated candidate: the reply's copy (count 0) or the old one
  have hex : ∃ r, upd ri m = some r ∧ (ri = none ∨ ri = some r) := by
    unfold upd; rw [upd1_not_acc hna]
    rcases ri with _ | r
    · rw [upd2_pre_none hp]; exact ⟨_, rfl, Or.inl rfl⟩
    · rcases stOk_cases (hI.core.stOk r rfl) with h' | hbl
      · rw [upd2_acc rfl h']; exact ⟨r, rfl, Or.inr rfl⟩
      · rw [upd2_pre_some hp hbl]; simp [hu]
  obtain ⟨r, hr0, hold⟩ := hex
  have hcnt1 : sint.Z r.preAcceptCount ≤ 1 := by
    rcases hold with rfl | rfl
    · unfold upd at hr0; rw [upd1_not_acc hna, upd2_pre_none hp] at hr0
      cases hr0; simp [hu]
    · exact hI.cnt1 r rfl
  refine ⟨r, hr0, ⟨?_, ?_, ?_⟩⟩
  · rw [hr0] at hmem
    refine ⟨hmem.bal, fun b' u h1 h2 => ?_, fun h1 h2 => ?_, fun _ => ⟨_, rfl, Or.inr rfl⟩⟩
    · obtain ⟨r', h', h3, h4⟩ := hmem.votes b' u h1 h2
      cases h'; exact ⟨_, rfl, h3, h4⟩
    · rcases hmem.eqd h1 h2 with ⟨r', h', h3⟩ | h
      · cases h'; exact Or.inl ⟨_, rfl, h3⟩
      · exact Or.inr h
  · rw [hr0] at hcore
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro r' hr' <;> cases hr'
    · exact hcore.accd r rfl
    · exact hcore.cnt r rfl
    · exact hcore.cntEq r rfl
    · intro _
      obtain ⟨B, hB, hle⟩ := hr.bal
      subst hYL
      exact ⟨⟨B, hB, by omega⟩, (hr.lead rfl).2⟩
    · exact hcore.stOk r rfl
  · intro r' hr'; cases hr'; exact hcnt1

end lret

/-! ## The decision (A3) -/

section decide
variable {g bal L b}

theorem blk_of_mem {ri : Option RecoveryInstance} {a : Fin 3} (h : MemOk g bal L b ri a) {b' : Int}
    (hb : b' < b) (hn : ¬ AccGe ri b') (w : Val) : Blk g bal a b' w := by
  obtain ⟨B, hB, hle⟩ := h.bal
  exact ⟨B, hB, by omega, fun hv => hn (h.votes b' w hb hv)⟩

theorem not_accGe {ri : Option RecoveryInstance} (h : ∀ r, ri = some r → r.status ≠ St.ACCEPTED)
    (b' : Int) : ¬ AccGe ri b' := fun ⟨r, hr, hs, _⟩ => h r hr hs

/-- Two distinct members other than the leader are all the acceptors other than the leader. -/
theorem others (L R Y a : Fin 3) (hR : R ≠ L) (hY : Y ≠ L) (hRY : R ≠ Y) (ha : a ≠ L) :
    a = R ∨ a = Y := by
  revert L R Y a; decide

/-- An ACCEPTED candidate (G16): safe to propose. -/
theorem decide_acc {R Y : Fin 3} {ri : Option RecoveryInstance} {ir : RecoveryInstance}
    (hA : AInv g bal L) (hc : RICore g bal L b ri) (hR : MemOk g bal L b ri R)
    (hY : MemOk g bal L b ri Y) (hRY : R ≠ Y) (he : ri = some ir) (hs : ir.status = St.ACCEPTED) :
    SafeAt g bal L b ir.valA := by
  obtain ⟨hp, h0, hlt⟩ := hc.accd ir he hs
  intro b' hb0 hb' w hne
  rcases Int.lt_trichotomy b' (sint.Z ir.vbal) with h | h | h
  · exact hA.prop_safe _ _ hp b' hb0 h w hne
  · subst h
    exact ⟨Or.inl ⟨_, fun h => hne h.symm, hp⟩, fun h0' => Or.inr (Or.inr (Or.inl ⟨_, h0' ▸ hp⟩))⟩
  · have hn : ¬ AccGe ri b' := by
      rintro ⟨r, hr, _, hle⟩; rw [he] at hr; cases hr; omega
    exact ⟨Or.inr ⟨R, Y, hRY, blk_of_mem hR hb' hn w, blk_of_mem hY hb' hn w⟩, fun h' => by omega⟩

/-- An unchanged pre-accepted candidate with no leader reply (G24): safe to propose. -/
theorem decide_eq {R Y : Fin 3} {ri : Option RecoveryInstance} {ir : RecoveryInstance}
    (hc : RICore g bal L b ri) (hR : MemOk g bal L b ri R)
    (hY : MemOk g bal L b ri Y) (hRY : R ≠ Y) (he : ri = some ir)
    (hcnt : 1 ≤ sint.Z ir.preAcceptCount) : SafeAt g bal L b ir.valA := by
  obtain ⟨hs, _, hcre⟩ := hc.cntEq ir he hcnt
  have hn : ∀ b', ¬ AccGe ri b' := not_accGe (fun r hr => by
    rw [he] at hr; cases hr; rw [hs]; decide)
  intro b' _ hb' w hne
  exact ⟨Or.inr ⟨R, Y, hRY, blk_of_mem hR hb' (hn b') w, blk_of_mem hY hb' (hn b') w⟩,
    fun _ => Or.inl ⟨_, hcre, hne⟩⟩

/-- No ACCEPTED candidate and no counted unchanged copy without a leader reply: nothing can have
been chosen below `b` (a restart or a no-op is safe). -/
theorem decide_none {R Y : Fin 3} {ri : Option RecoveryInstance}
    (hA : AInv g bal L) (hb : 0 < b) (hc : RICore g bal L b ri) (hR : MemOk g bal L b ri R)
    (hY : MemOk g bal L b ri Y) (hRY : R ≠ Y)
    (hna : ∀ r, ri = some r → r.status ≠ St.ACCEPTED)
    (hlc : ∀ r, ri = some r → r.leaderResponded = true ∨ sint.Z r.preAcceptCount < 1) :
    SafeAll g bal L b := by
  have hn : ∀ b', ¬ AccGe ri b' := not_accGe hna
  intro b' hb0 hb' w
  refine ⟨Or.inr ⟨R, Y, hRY, blk_of_mem hR hb' (hn b') w, blk_of_mem hY hb' (hn b') w⟩, fun h0 => ?_⟩
  subst h0
  by_cases hlr : ∃ r, ri = some r ∧ r.leaderResponded = true
  · obtain ⟨r, hr, hl⟩ := hlr
    obtain ⟨⟨B, hB, hpos⟩, hnf⟩ := hc.lr r hr hl
    exact Or.inr (Or.inl ⟨B, hB, hpos, hnf⟩)
  by_cases hrst : RstBelow g b
  · obtain ⟨b'', h1, h2, h3⟩ := hrst
    exact (hA.rst_safe b'' h3 0 (Int.le_refl 0) h1 w).2 rfl
  -- neither member is the leader, and neither pre-accepted unchanged
  have hnl : ∀ a, MemOk g bal L b ri a → a ≠ L := by
    intro a ha haL
    obtain ⟨r, hr, h⟩ := ha.lead haL
    rcases h with h | h
    · exact hna r hr h
    · exact hlr ⟨r, hr, h⟩
  have hne : ∀ a, MemOk g bal L b ri a → ¬ g.eq a := by
    intro a ha he
    rcases ha.eqd (hnl a ha) he with ⟨r, hr, h⟩ | h
    · rcases h with h | h
      · exact hna r hr h
      · rcases hlc r hr with h' | h'
        · exact hlr ⟨r, hr, h'⟩
        · omega
    · exact hrst h
  refine Or.inr (Or.inr (Or.inr fun a ha => ?_))
  rcases others L R Y a (hnl R hR) (hnl Y hY) hRY ha with rfl | rfl
  · obtain ⟨B, hB, hle⟩ := hR.bal; exact ⟨B, hB, by omega, hne _ hR⟩
  · obtain ⟨B, hB, hle⟩ := hY.bal; exact ⟨B, hB, by omega, hne _ hY⟩

end decide

/-! ## The facts along a run (`Evolve`) -/

section evolve
variable {g bal L b}
variable {g' : Gh Val} {bal' : Fin 3 → Option Int}

theorem rstBelow_mono (hle : g.Le g') (h : RstBelow g b) : RstBelow g' b := by
  obtain ⟨b', h1, h2, h3⟩ := h; exact ⟨b', h1, h2, hle.rst _ h3⟩

/-- No new fast commit once the leader is past ballot 0. -/
theorem nofast_evolve (E : Evolve L g bal g' bal') (hL : ∃ B, bal L = some B ∧ 0 < B)
    (h : ∀ v, ¬ g.fast v) : ∀ v, ¬ g'.fast v := by
  intro v hv
  obtain ⟨B, hB, hpos⟩ := hL
  have := E.fast_new v hv (h v) B hB
  omega

theorem memOk_evolve (E : Evolve L g bal g' bal') (hb : 0 < b) {ri : Option RecoveryInstance}
    {a : Fin 3} (h : MemOk g bal L b ri a) : MemOk g' bal' L b ri a := by
  obtain ⟨B, hB, hle⟩ := h.bal
  refine ⟨?_, ?_, ?_, h.lead⟩
  · obtain ⟨B', hB', hle'⟩ := E.bal_mono a B hB; exact ⟨B', hB', Int.le_trans hle hle'⟩
  · intro b' u hb' hu
    by_cases ho : g.acc a b' u
    · exact h.votes b' u hb' ho
    · have := E.acc_new a b' u hu ho B hB; omega
  · intro ha he
    by_cases ho : g.eq a
    · exact (h.eqd ha ho).imp_right (rstBelow_mono E.le)
    · have := E.eq_new a he ho B hB; omega

theorem riCore_evolve (E : Evolve L g bal g' bal') {ri : Option RecoveryInstance}
    (h : RICore g bal L b ri) : RICore g' bal' L b ri where
  accd r hr hs := by
    obtain ⟨h1, h2, h3⟩ := h.accd r hr hs; exact ⟨E.le.prop _ _ h1, h2, h3⟩
  cnt := h.cnt
  cntEq r hr hc := by
    obtain ⟨h1, h2, h3⟩ := h.cntEq r hr hc; exact ⟨h1, h2, E.le.cre _ h3⟩
  lr r hr hl := by
    obtain ⟨⟨B, hB, hpos⟩, hf⟩ := h.lr r hr hl
    obtain ⟨B', hB', hle⟩ := E.bal_mono L B hB
    exact ⟨⟨B', hB', by omega⟩, nofast_evolve E ⟨B, hB, hpos⟩ hf⟩
  stOk := h.stOk

theorem riOk_evolve (E : Evolve L g bal g' bal') (hb : 0 < b) {R : Fin 3}
    {ri : Option RecoveryInstance} (h : RIOk g bal L b R ri) : RIOk g' bal' L b R ri :=
  ⟨memOk_evolve E hb h.mem, riCore_evolve E h.core, h.cnt1⟩

theorem repOk_evolve (E : Evolve L g bal g' bal') (hb : 0 < b) {Y : Fin 3} {m : PrepareReplyM}
    (h : RepOk g bal L b Y m) : RepOk g' bal' L b Y m := by
  obtain ⟨B, hB, hle⟩ := h.bal
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h.stOk, h.isL⟩
  · obtain ⟨B', hB', hle'⟩ := E.bal_mono Y B hB; exact ⟨B', hB', Int.le_trans hle hle'⟩
  · intro b' u hb' hu
    by_cases ho : g.acc Y b' u
    · exact h.votes b' u hb' ho
    · have := E.acc_new Y b' u hu ho B hB; omega
  · intro hs; obtain ⟨h1, h2⟩ := h.accd hs; exact ⟨E.le.acc _ _ _ h1, h2⟩
  · intro hY he
    by_cases ho : g.eq Y
    · rcases h.eqd hY ho with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (rstBelow_mono E.le h1))
    · have := E.eq_new Y he ho B hB; omega
  · intro hY
    obtain ⟨h1, h2⟩ := h.lead hY
    subst hY
    exact ⟨h1, nofast_evolve E ⟨B, hB, by omega⟩ h2⟩
  · intro h1 h2 h3; exact E.le.cre _ (h.cre h1 h2 h3)

end evolve

/-! ## The decision keeps `AInv` (the A3 step of the invariant's preservation) -/

section decideInv
variable {g bal L b}

theorem sge_one_iff {c : w64} : sge c NHALF = true ↔ 1 ≤ sint.Z c := by
  simp [sge, sle, NHALF]

/-- The deciding reply `m` from `Y` at the recoverer `R`'s fresh ballot `b` (not the leader's
pre-accepted reply below ACCEPTED, which decides nothing): with the updated candidate `ir`, an
Accept of `ir` (an ACCEPTED candidate, or a counted unchanged one without a leader reply) keeps
`AInv` with the proposal added. -/
theorem decide_accept_ainv {R Y : Fin 3} {ri : Option RecoveryInstance} {m : PrepareReplyM}
    {ir : RecoveryInstance}
    (hA : AInv g bal L) (hb : 0 < b) (hI : RIOk g bal L b R ri) (hr : RepOk g bal L b Y m)
    (hRY : R ≠ Y) (hbal : bal R = some b) (hfresh : ∀ u, ¬ g.prop b u)
    (hnot : ¬ (Y = L ∧ (m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ) ∧
      belowB (upd1 ri m) = true))
    (he : upd ri m = some ir)
    (hacc : ir.status = St.ACCEPTED ∨
      (ir.leaderResponded = false ∧ sge ir.preAcceptCount NHALF = true ∧
        ir.status = St.PREACCEPTED_EQ)) :
    AInv (g.addProp b ir.valA R) bal L ∧ Evolve L g bal (g.addProp b ir.valA R) bal := by
  have hc := riCore_upd hA hr hI.core hI.cnt1
  have hmR := memOk_upd (m := m) hI.core hI.mem
  have hmY := memOk_upd_Y hr hI.core hnot
  have hsafe : SafeAt g bal L b ir.valA := by
    rcases hacc with h | ⟨_, h2, _⟩
    · exact decide_acc hA hc hmR hmY hRY he h
    · exact decide_eq hc hmR hmY hRY he (sge_one_iff.1 h2)
  exact ainv_addProp hA hfresh (by omega) hbal hsafe (fun h => by omega)

/-- The no-op decision (no candidate) keeps `AInv` with the no-op proposal added. -/
theorem decide_noop_ainv {R Y : Fin 3} {ri : Option RecoveryInstance} {m : PrepareReplyM}
    (hA : AInv g bal L) (hb : 0 < b) (hI : RIOk g bal L b R ri) (hr : RepOk g bal L b Y m)
    (hRY : R ≠ Y) (hbal : bal R = some b) (hfresh : ∀ u, ¬ g.prop b u)
    (hnot : ¬ (Y = L ∧ (m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ) ∧
      belowB (upd1 ri m) = true))
    (he : upd ri m = none) (v : Val) :
    AInv (g.addProp b v R) bal L ∧ Evolve L g bal (g.addProp b v R) bal := by
  have hc := riCore_upd hA hr hI.core hI.cnt1
  have hmR := memOk_upd (m := m) hI.core hI.mem
  have hmY := memOk_upd_Y hr hI.core hnot
  have hsafe : SafeAll g bal L b :=
    decide_none hA hb hc hmR hmY hRY (fun r h => by rw [he] at h; cases h)
      (fun r h => by rw [he] at h; cases h)
  exact ainv_addProp hA hfresh (by omega) hbal (hsafe.safeAt v) (fun h => by omega)

/-- The restart decision (a candidate that is neither ACCEPTED nor counted without a leader reply)
keeps `AInv` with the restart added. -/
theorem decide_restart_ainv {R Y : Fin 3} {ri : Option RecoveryInstance} {m : PrepareReplyM}
    {ir : RecoveryInstance}
    (hA : AInv g bal L) (hb : 0 < b) (hI : RIOk g bal L b R ri) (hr : RepOk g bal L b Y m)
    (hRY : R ≠ Y)
    (hnot : ¬ (Y = L ∧ (m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ) ∧
      belowB (upd1 ri m) = true))
    (he : upd ri m = some ir) (hna : ir.status ≠ St.ACCEPTED)
    (hntpa : ¬ (ir.leaderResponded = false ∧ sge ir.preAcceptCount ((NHALF + 1) / 2) = true)) :
    AInv (g.addRst b) bal L ∧ Evolve L g bal (g.addRst b) bal := by
  have hc := riCore_upd hA hr hI.core hI.cnt1
  have hmR := memOk_upd (m := m) hI.core hI.mem
  have hmY := memOk_upd_Y hr hI.core hnot
  have h2 : ((NHALF + 1) / 2 : w64) = NHALF := by decide
  rw [h2, sge_one_iff] at hntpa
  have hsafe : SafeAll g bal L b :=
    decide_none hA hb hc hmR hmY hRY (fun r h => by rw [he] at h; cases h; exact hna)
      (fun r h => by
        rw [he] at h; cases h
        by_cases hl : ir.leaderResponded = true
        · exact Or.inl hl
        · right
          have hl' : ir.leaderResponded = false := by simpa using hl
          have : ¬ (1 ≤ sint.Z ir.preAcceptCount) := fun h1 => hntpa ⟨hl', h1⟩
          omega)
  exact ainv_addRst hA hsafe

end decideInv

end Perennial.gryff.pureA
