/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/WitDefs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AW, internal: **the witness invariant** (`notes/unit-AW.md`; L1 for RMWs, unit L's
`witness_committed`, `GryffProof/PureL/Witness.lean`).

The ghost `S : CSG` records, per instance `(q, i)`, the three replicas' store tags at the instance's
creation (`handlePropose` at `q`, the `rmw` event that takes slot `i` of row `q`). A replica `w`
*witnesses* a base `b` under `f = S q i` when `f w ≤ b.t` (`W1`); `Wit2`: two distinct witnesses.
`WInv c S` is a separate invariant (kept by every step given `CInv`, `WitStep.lean`), not fields of
`CInv`: its clauses only read the copies and messages, and its proof uses `CInv` for ids and ballots.
* every created instance is below its owner's `crt` (`born`), and `f w` is at most `w`'s store now
  (`store`: stores only grow);
* copies with commands (not NONE): STRONG statuses (ACCEPTED, PREACCEPTED_EQ, COMMITTED, EXECUTED)
  are `Wit2`; a PREACCEPTED copy at `a` is witnessed by `a` (its base is at least `a`'s store when it
  was made: the creator's store, a merge, or `handlePreAccept`'s raise to the replier's store);
  a recovery candidate (non-committed copy) with commands of status ACCEPTED/PREACCEPTED_EQ: `Wit2`;
* messages: a PreAccept to `d` is witnessed by someone other than `d` (its sender), a ballot-0
  PreAccept's base is at most the leader's store at creation; an OK PreAcceptReply is `Wit2` (the
  sender's witness and the replier's store); a PreAcceptOK to the leader `d` names a replier `X ≠ d`
  with `f X ≤ f d` (the replier kept the creation base unchanged: its store was below it); Accepts,
  Commits are `Wit2`; PrepareReplies like copies.

Tag order: `TLe` on the model's tags through `tp` (= `Tag.toP` of `Pure/LinDefs.lean`, which
`PureA` cannot import).
-/
module

public import Dsverify.Proof.gryff.PureA.Inv
public import Dsverify.Proof.gryff.Proto.TagOrder

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AW

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA
open Perennial.gryff.proto

/-! ## Tags -/

/-- A model tag as a stage-1 tag (`Tag.toP`). -/
def tp (t : model.Tag) : PTag := (sint.Z t.ts, sint.Z t.cid, sint.Z t.rmwc)

/-- The tag order on model tags. -/
def TLe (x y : model.Tag) : Prop := tagLe (tp x) (tp y)

theorem TLe.refl (x : model.Tag) : TLe x x := tagLe_refl _
theorem TLe.trans {x y z : model.Tag} (h1 : TLe x y) (h2 : TLe y z) : TLe x z := tagLe_trans h1 h2

theorem tag_gt_iff (a b : model.Tag) : Iff (a.gt b = true) (tagLt (tp b) (tp a)) := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
  simp only [model.Tag.gt, model.Tag.cmp, tp, tagLt, slt]
  have e1 : (a1 == b1) = decide (sint.Z a1 = sint.Z b1) := by
    unfold sint.Z; by_cases h : a1 = b1 <;> simp [h, BitVec.toInt_inj]
  have e2 : (a2 == b2) = decide (sint.Z a2 = sint.Z b2) := by
    unfold sint.Z; by_cases h : a2 = b2 <;> simp [h, BitVec.toInt_inj]
  have e3 : (a3 == b3) = decide (sint.Z a3 = sint.Z b3) := by
    unfold sint.Z; by_cases h : a3 = b3 <;> simp [h, BitVec.toInt_inj]
  simp only [e1, e2, e3]
  generalize sint.Z a1 = x1 at *; generalize sint.Z a2 = x2 at *; generalize sint.Z a3 = x3 at *
  generalize sint.Z b1 = y1 at *; generalize sint.Z b2 = y2 at *; generalize sint.Z b3 = y3 at *
  split <;> rename_i h1 <;> (try split) <;> simp_all <;> omega

/-- `x > y` is false: `x ≤ y`. -/
theorem gt_false {x y : model.Tag} (h : x.gt y = false) : TLe x y := by
  have : ¬ tagLt (tp y) (tp x) := fun h' => by rw [(tag_gt_iff x y).2 h'] at h; cases h
  exact (not_tagLt_iff _ _).1 this

theorem gt_true {x y : model.Tag} (h : x.gt y = true) : TLe y x :=
  tagLe_of_lt ((tag_gt_iff x y).1 h)

/-! ## The ghost and the witness predicates -/

/-- The ghost: per instance, the replicas' store tags at its creation. -/
abbrev CSG := w32 → w32 → Option (Fin 3 → model.Tag)

/-- `S'` extends `S`. -/
def SLe (S S' : CSG) : Prop := ∀ q i f, S q i = some f → S' q i = some f

theorem SLe.refl (S : CSG) : SLe S S := fun _ _ _ h => h

/-- `S` with the entry `(q, i) ↦ f`. -/
def CSG.set (S : CSG) (q i : w32) (f : Fin 3 → model.Tag) : CSG :=
  fun q' i' => if q' = q ∧ i' = i then some f else S q' i'

theorem CSG.set_le {S : CSG} {q i : w32} {f : Fin 3 → model.Tag} (h : S q i = none) :
    SLe S (S.set q i f) := fun q' i' g hg => by
  unfold CSG.set
  split
  · rename_i e; obtain ⟨rfl, rfl⟩ := e; rw [h] at hg; cases hg
  · exact hg

/-- Replica `w` witnesses base `b`: its store at the creation is at most `b`. -/
def W1 (f : Fin 3 → model.Tag) (w : Fin 3) (b : ValTag) : Prop := TLe (f w) b.t

/-- Two distinct witnesses. -/
def Wit2 (f : Fin 3 → model.Tag) (b : ValTag) : Prop := ∃ w1 w2, w1 ≠ w2 ∧ W1 f w1 b ∧ W1 f w2 b

theorem W1.mono {f : Fin 3 → model.Tag} {w : Fin 3} {b b' : ValTag} (h : W1 f w b) (e : TLe b.t b'.t) :
    W1 f w b' := TLe.trans h e

theorem Wit2.mono {f : Fin 3 → model.Tag} {b b' : ValTag} (h : Wit2 f b) (e : TLe b.t b'.t) :
    Wit2 f b' :=
  let ⟨w1, w2, hn, h1, h2⟩ := h; ⟨w1, w2, hn, h1.mono e, h2.mono e⟩

/-- The statuses whose copies carry two witnesses. -/
def Strong (st : w8) : Prop :=
  st = St.ACCEPTED ∨ st = St.PREACCEPTED_EQ ∨ st = St.COMMITTED ∨ st = St.EXECUTED

/-- A recovery candidate: with commands, the instance was created, and an ACCEPTED or unchanged
candidate is `Wit2`. -/
def CandOK (S : CSG) (q i : w32) (ri : Option RecoveryInstance) : Prop :=
  ∀ r, ri = some r → r.cmds ≠ [] → ∃ f, S q i = some f ∧
    (r.status = St.ACCEPTED ∨ r.status = St.PREACCEPTED_EQ → Wit2 f r.base)

/-- Facts about replica `a`'s copy `cp` of instance `(q, i)`. -/
structure CopyW (S : CSG) (q i : w32) (a : Fin 3) (cp : Copy) : Prop where
  val : cp.cmds ≠ [] → cp.status ≠ St.NONE → ∃ f, S q i = some f ∧
    (Strong cp.status → Wit2 f cp.base) ∧ (cp.status = St.PREACCEPTED → W1 f a cp.base)
  cand : ∀ lb, cp.lb = some lb → ¬ isCommitted cp.status → CandOK S q i lb.recoveryInst

/-- A PrepareReply's (or a copy's) value facts. -/
def RepW (S : CSG) (m : PrepareReplyM) : Prop :=
  m.cmds ≠ [] → m.status ≠ St.NONE → ∃ f, S m.replica m.inst = some f ∧
    (Strong m.status → Wit2 f m.base)

/-- Facts about a message in flight to `d`. -/
def WMsg (S : CSG) (d : Fin 3) : Msg → Prop
  | .preAccept m => ∃ f, S m.replica m.inst = some f ∧ (∃ w, w ≠ d ∧ W1 f w m.base) ∧
      (m.ballot = 0 → TLe m.base.t (f (rowOf m.replica)))
  | .preAcceptReply m => m.ok ≠ FALSE → ∃ f, S m.replica m.inst = some f ∧ Wit2 f m.base
  | .preAcceptOK m => ∃ f, S (rid32 d) m.inst = some f ∧ ∃ X, X ≠ d ∧ TLe (f X) (f d)
  | .accept m => m.cmds ≠ [] → ∃ f, S m.replica m.inst = some f ∧ Wit2 f m.base
  | .commit m => m.cmds ≠ [] → ∃ f, S m.replica m.inst = some f ∧ Wit2 f m.base
  | .prepareReply m => RepW S m
  | _ => True

/-- **The witness invariant.** -/
structure WInv (c : Cfg gNet) (S : CSG) : Prop where
  loc : ∀ a : Fin 3, Loc (c.st a)
  store : ∀ q i f, S q i = some f → ∀ w, TLe (f w) (c.st w).tag
  born : ∀ q i f, S q i = some f → ∃ r : Fin 3, q = rid32 r ∧
    sint.Z i < sint.Z ((c.st r).crt (rid32 r))
  copies : ∀ (a : Fin 3) q i cp, cpOf c a q i = some cp → CopyW S q i a cp
  msgs : ∀ (d : Fin 3) m, m ∈ c.inflight d → WMsg S d m

/-! ## Monotonicity in the ghost -/

theorem candOK_mono {S S' : CSG} (hS : SLe S S') {q i : w32} {ri : Option RecoveryInstance}
    (h : CandOK S q i ri) : CandOK S' q i ri := fun r hr hc =>
  let ⟨f, hf, k⟩ := h r hr hc; ⟨f, hS _ _ _ hf, k⟩

theorem copyW_mono {S S' : CSG} (hS : SLe S S') {q i : w32} {a : Fin 3} {cp : Copy}
    (h : CopyW S q i a cp) : CopyW S' q i a cp where
  val := fun h1 h2 => let ⟨f, hf, k⟩ := h.val h1 h2; ⟨f, hS _ _ _ hf, k⟩
  cand := fun lb hl hn => candOK_mono hS (h.cand lb hl hn)

theorem wmsg_mono {S S' : CSG} (hS : SLe S S') {d : Fin 3} {m : Msg} (h : WMsg S d m) :
    WMsg S' d m := by
  cases m <;> simp only [WMsg, RepW] at h ⊢
  all_goals first
    | trivial
    | (obtain ⟨f, hf, k⟩ := h; exact ⟨f, hS _ _ _ hf, k⟩)
    | (intro h1; obtain ⟨f, hf, k⟩ := h h1; exact ⟨f, hS _ _ _ hf, k⟩)
    | (intro h1 h2; obtain ⟨f, hf, k⟩ := h h1 h2; exact ⟨f, hS _ _ _ hf, k⟩)

/-! ## The initial configuration -/

theorem wit_init : WInv (Cfg.init gNet) (fun _ _ => none) where
  loc a := loc_init a
  store _ _ _ h := by cases h
  born _ _ _ h := by cases h
  copies _ _ _ _ h := by cases h
  msgs _ _ h := by cases h

/-! ## The frame of a step -/

theorem mem_post {c c1 : Cfg gNet} {a : Fin 3} {e : Ev} {s' : RState} {o : List Out}
    (hp : Post c a e s' o c1) {d : Fin 3} {m : Msg} (h : m ∈ c1.inflight d) :
    m ∈ c.inflight d ∨ m ∈ A1b.sentR d o := by
  have h' : m ∈ (if d = a then consume (gNet.recv e) (c.inflight d) else c.inflight d) ++
      sentTo gNet d o := by rw [hp.2] at h; exact h
  rw [A1b.sentTo_eq] at h'
  rcases List.mem_append.1 h' with h' | h'
  · left
    split at h'
    · unfold consume at h'; split at h'
      · exact List.mem_of_mem_erase h'
      · exact h'
    · exact h'
  · exact Or.inr h'

theorem st_postA {c c1 : Cfg gNet} {a : Fin 3} {e : Ev} {s' : RState} {o : List Out}
    (hp : Post c a e s' o c1) : c1.st a = s' := by rw [hp.1]; exact if_pos rfl

theorem st_postN {c c1 : Cfg gNet} {a : Fin 3} {e : Ev} {s' : RState} {o : List Out}
    (hp : Post c a e s' o c1) {j : Fin 3} (h : j ≠ a) : c1.st j = c.st j := by
  rw [hp.1]; exact if_neg h

/-- The local obligations of a step at replica `a`: every new copy of `a` satisfies `CopyW`, every
sent message `WMsg`. -/
def LocalW (S : CSG) (s s' : RState) (a : Fin 3) (o : List Out) : Prop :=
  (∀ q i cp, s'.inst q i = some cp → s.inst q i = some cp ∨ CopyW S q i a cp) ∧
  (∀ d m, m ∈ A1b.sentR d o → WMsg S d m)

/-- **The frame**: the invariant after a step, from its local obligations and the ghost's facts. -/
theorem wit_post {c c1 : Cfg gNet} {S S' : CSG} {a : Fin 3} {e : Ev} {s' : RState} {o : List Out}
    (W : WInv c S) (hp : Post c a e s' o c1) (hS : SLe S S') (hloc : Loc s')
    (hstore : ∀ q i f, S' q i = some f → ∀ w, TLe (f w) (c1.st w).tag)
    (hborn : ∀ q i f, S' q i = some f → ∃ r : Fin 3, q = rid32 r ∧
      sint.Z i < sint.Z ((c1.st r).crt (rid32 r)))
    (hL : LocalW S' (c.st a) s' a o) : WInv c1 S' where
  loc j := by
    by_cases h : j = a
    · subst h; rw [st_postA hp]; exact hloc
    · rw [st_postN hp h]; exact W.loc j
  store := hstore
  born := hborn
  copies j q i cp hc := by
    unfold cpOf at hc
    by_cases h : j = a
    · subst h; rw [st_postA hp] at hc
      rcases hL.1 q i cp hc with h | h
      · exact copyW_mono hS (W.copies j q i cp h)
      · exact h
    · rw [st_postN hp h] at hc; exact copyW_mono hS (W.copies j q i cp hc)
  msgs d m hm := by
    rcases mem_post hp hm with h | h
    · exact wmsg_mono hS (W.msgs d m h)
    · exact hL.2 d m h

/-! ## Local helpers -/

theorem wmsg_quiet {S : CSG} {d : Fin 3} {m : Msg} (h : isEp m = false) : WMsg S d m := by
  cases m <;> first | trivial | cases h

theorem sentR_quiet {o : List Out} (h : QuietO o) {d : Fin 3} {m : Msg} (hm : m ∈ A1b.sentR d o) :
    isEp m = false := h d m (A1b.mem_sentR hm)

theorem localW_frame {S : CSG} {s s' : RState} {a : Fin 3} {o : List Out} (hf : Frame s s')
    (ho : QuietO o) : LocalW S s s' a o :=
  ⟨fun q i cp h => Or.inl (by rw [← hf.2.1]; exact h),
   fun _ _ hm => wmsg_quiet (sentR_quiet ho hm)⟩

theorem copyW_sim {S : CSG} {q i : w32} {a : Fin 3} {cp cp' : Copy} (h : CopyW S q i a cp)
    (hs : CopySim cp cp') : CopyW S q i a cp' := by
  have hv := hs.valA
  simp only [Copy.valA, Prod.mk.injEq] at hv
  obtain ⟨e1, -, -, e4⟩ := hv
  have hst : cp'.status = cp.status ∨ (cp.status = St.COMMITTED ∧ cp'.status = St.EXECUTED) := hs.st
  refine ⟨fun h1 h2 => ?_, fun lb hl hn => ?_⟩
  · rw [e1] at h1
    rcases hst with e | ⟨e, e'⟩
    · rw [e] at h2 ⊢; rw [e4]; exact h.val h1 h2
    · obtain ⟨f, hf, k1, -⟩ := h.val h1 (by rw [e]; decide)
      refine ⟨f, hf, fun _ => ?_, fun he => ?_⟩
      · rw [e4]; exact k1 (Or.inr (Or.inr (Or.inl e)))
      · rw [e'] at he; exact absurd he (by decide)
  · obtain ⟨l0, hl0, el⟩ := hs.lb_some hl
    have hn' : ¬ isCommitted cp.status := by
      rcases hst with e | ⟨e, e'⟩
      · rw [← e]; exact hn
      · exact absurd (Or.inr e') hn
    have := h.cand l0 hl0 hn'
    rw [← el.2.1]; exact this

theorem localW_sim {S : CSG} {s s' : RState} {a : Fin 3} {o : List Out}
    (hc : ∀ q i cp, s.inst q i = some cp → CopyW S q i a cp) (hf : SimFrame s s')
    (ho : QuietO o) : LocalW S s s' a o := by
  refine ⟨fun q i cp h => Or.inr ?_, fun _ _ hm => wmsg_quiet (sentR_quiet ho hm)⟩
  have hs := hf.2.2 q i
  rw [h] at hs
  obtain ⟨cp0, h0, hsim⟩ := OSim.some_r hs
  exact copyW_sim (hc q i cp0 h0) hsim

/-- A one-copy change: other copies are the old ones. -/
theorem cp_setInst {S : CSG} {s t : RState} {a : Fin 3} {q0 i0 : w32} {cp0 : Copy}
    (ht : t.inst = s.inst) (h : CopyW S q0 i0 a cp0) :
    ∀ q i cp, (t.setInst q0 i0 cp0).inst q i = some cp → s.inst q i = some cp ∨ CopyW S q i a cp := by
  intro q i cp hc
  rw [setInst_inst] at hc
  split at hc
  · rename_i e; obtain ⟨rfl, rfl⟩ := e; cases hc; exact Or.inr h
  · rw [ht] at hc; exact Or.inl hc

theorem st_dec : St.NONE ≠ St.PREACCEPTED ∧ St.PREACCEPTED ≠ St.NONE ∧ St.ACCEPTED ≠ St.NONE ∧
    St.COMMITTED ≠ St.NONE ∧ St.PREACCEPTED_EQ ≠ St.NONE ∧ St.ACCEPTED ≠ St.PREACCEPTED ∧
    St.COMMITTED ≠ St.PREACCEPTED ∧ St.PREACCEPTED_EQ ≠ St.PREACCEPTED ∧
    Strong St.ACCEPTED ∧ Strong St.COMMITTED ∧ Strong St.PREACCEPTED_EQ ∧ ¬ Strong St.PREACCEPTED ∧
    ¬ isCommitted St.ACCEPTED ∧ ¬ isCommitted St.PREACCEPTED ∧ ¬ isCommitted St.PREACCEPTED_EQ ∧
    isCommitted St.COMMITTED := by
  unfold Strong isCommitted; decide

/-- A copy with a `Wit2` value of STRONG status (no candidate needed: committed, or candidate none). -/
theorem copyW_strong {S : CSG} {q i : w32} {a : Fin 3} {cp : Copy} (hs : Strong cp.status)
    (hv : cp.cmds ≠ [] → ∃ f, S q i = some f ∧ Wit2 f cp.base)
    (hc : ∀ lb, cp.lb = some lb → ¬ isCommitted cp.status → CandOK S q i lb.recoveryInst) :
    CopyW S q i a cp where
  val h1 _ := let ⟨f, hf, k⟩ := hv h1
    ⟨f, hf, fun _ => k, fun he => by
      rw [he] at hs; exact absurd hs st_dec.2.2.2.2.2.2.2.2.2.2.2.1⟩
  cand := hc

end Perennial.gryff.pureA.AW
