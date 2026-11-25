/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureL/Witness.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L: the executor's result (`stepExec_res`), and the **witness invariant** behind L1 for RMWs
(`witness_committed`, the riskiest step of unit L).

**The witness invariant** (`notes/stage2-proof.md` §L, L1; `notes/unit-L.md`). For an instance
`x` created at label `g_x` (the RMW request whose `handlePropose` took slot `x.2` of row `x.1`), a
replica `w` *witnesses* a base `b` when `w`'s store at the cut `g_x` is at most `b.t`. Since
stores only grow, a base computed at a time after `g_x` as at least `w`'s current store is
witnessed by `w`. Inductively over the run, for every carrier of a value of `x` with commands:
* the leader's ballot-0 PreAccept and its own copy at ballot 0: base `base0 = ` the leader's store
  at `g_x` (witness: the leader);
* a PreAcceptReply OK / a PreAccepted copy at a non-leader: witnessed by the replier (its
  `handlePreAccept` raises the base to its store) — and an EQ copy at vbal 0 (unchanged) or a
  `PreAcceptOK` carries `base0` witnessed by the leader *and* the replier;
* a restarted phase 1 (`startPhase1` at a recoverer): its base is the recoverer's store (after `g_x`);
* **two distinct witnesses** for every ACCEPTED, COMMITTED or EXECUTED copy, every Accept, Commit,
  PrepareReply of such a status, and every recovery candidate of status ACCEPTED or with
  `preAcceptCount ≥ 1`: the slow paths merge the proposer's own value with ≥ 1 reply
  (`mergeAttributes` keeps the larger base); the fast path commits only when the reply's base is
  at most the leader's; recovery accepts an ACCEPTED candidate's value or an EQ candidate's (the
  leader and the EQ copy's holder); G22 commits a committed reply's value.
Instance numbers of row `q` are created by `q` only (unit A's "rows are created by their owner"),
so every event about `x` is after `g_x`. If unit A1 proves D1's witness quorums (conflict tables)
with the same carriers, the two invariants should be merged into one induction.
-/
module

public import Dsverify.Proof.gryff.PureL.Store
public import Dsverify.Proof.gryff.PureL.Peel
public import Dsverify.Proof.gryff.PureLa.Inv
public import Dsverify.Proof.gryff.PureA.WitRun

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

theorem Tag.gt_iff (a b : model.Tag) : Iff (a.gt b = true) (tagLt b.toP a.toP) := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
  simp only [model.Tag.gt, model.Tag.cmp, model.Tag.toP, tagLt, slt]
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

theorem sendTo_some {q : w32} {m : Msg} {x : Out} (h : sendTo q m = some x) :
    ∃ d, x = .send d m := by
  unfold sendTo at h
  cases hd : dstOf q with
  | none => rw [hd] at h; cases h
  | some d => rw [hd] at h; cases h; exact ⟨d, rfl⟩

theorem stepExec_res {s s' : RState} {q i : w32} {o : List Out} (h : stepExec s q i = .ok (s', o))
    {vt : ValTag} (hv : execRes o = some vt) :
    ∃ c, s.inst q i = some c ∧ c.status = St.COMMITTED ∧ c.cmds ≠ [] ∧
      ∃ t0 : model.Tag, tagLe c.base.t.toP t0.toP ∧ vt.t = { t0 with rmwc := t0.rmwc + 1 } ∧
        (t0 = c.base.t ∨ ∃ pvt, s.prevValTag = some pvt ∧ t0 = pvt.t) := by
  unfold stepExec at h
  peel h
  · cases h; simp [execRes] at hv
  all_goals (
    cases h
    obtain ⟨d, rfl⟩ := sendTo_some ‹sendTo _ _ = some _›
    simp only [execRes, List.findSome?_cons, Option.some.injEq] at hv
    subst hv
    refine ⟨_, ‹s.inst q i = some _›, by simpa using ‹¬ _ ≠ St.COMMITTED›,
      by simp [‹(_ : Copy).cmds = _ :: _›], ?_⟩
    rename Copy => c
    refine ⟨(match s.prevValTag with
      | none => c.base
      | some pvt => if c.base.t.gt pvt.t = true then c.base else pvt).t, ?_,
      by (repeat' split) <;> simp_all, by (repeat' split) <;> simp_all⟩
    split
    · exact tagLe_refl _
    · split
      · exact tagLe_refl _
      · rename_i hg
        rw [← not_tagLt_iff]; intro h'; exact hg ((Tag.gt_iff _ _).2 h'))

/-- **The witness invariant at commit** (L1 for RMWs): a committed copy (with commands) of an RMW's
instance has a base at least two distinct replicas' stores at the RMW's creation.

Proved by unit AW: the invariant `pureA.AW.WInv` (`GryffProof/PureA/WitDefs.lean`, kept by every
step: `WitStep.lean`), its ghost linked to the RMW labels' cuts (`WitRun.lean`, `witness_cut`);
here `ops` / `rmwInst` are unfolded and the stores' growth (`step_tag_mono`) supplied. -/
theorem witness_committed {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {a b : w64} (hi : o.inp = .cas a b) {n : Nat} {r : Fin 3} {cp : Copy}
    (hcp : (cutSt l n r).inst (rmwInst l o).1 (rmwInst l o).2 = some cp)
    (hst : cp.status = St.COMMITTED) (hc : cp.cmds ≠ []) :
    ∃ w1 w2 : Fin 3, w1 ≠ w2 ∧ tagLe (cutSt l o.g w1).tag.toP cp.base.t.toP ∧
      tagLe (cutSt l o.g w2).tag.toP cp.base.t.toP := by
  have hT : pureA.AW.TagMono := fun _ _ _ _ _ hs => step_tag_mono hs
  unfold ops at ho
  obtain ⟨g, -, hx⟩ := List.mem_filterMap.1 ho
  cases hl : l[g]? with
  | none => rw [hl] at hx; cases hx
  | some p =>
    obtain ⟨r0, e⟩ := p
    rw [hl] at hx
    obtain ⟨⟨cid', rid', inp⟩, he, ho'⟩ := Option.map_eq_some_iff.1 hx
    subst ho'
    cases e with
    | rmw rid cid k d oldV newV =>
      unfold rmwInst at hcp
      simp only at hcp
      rw [← pureA.AW.projR_take_prefix] at hcp
      exact pureA.AW.witness_cut hT h hl hcp (Or.inl hst) hc
    | read => simp [Ev.clientReq] at he; obtain ⟨-, -, rfl⟩ := he; cases hi
    | write => simp [Ev.clientReq] at he; obtain ⟨-, -, rfl⟩ := he; cases hi
    | _ => simp [Ev.clientReq] at he

/-- Tags' `rmwc` stay far from the word's maximum (no wrap at `rmwc + 1`). -/
def RmwcBounded (s : RState) : Prop :=
  (∀ pvt, s.prevValTag = some pvt → sint.Z pvt.t.rmwc < 2 ^ 31 - 1) ∧
    ∀ q i cp, s.inst q i = some cp → sint.Z cp.base.t.rmwc < 2 ^ 31 - 1

/-- Every tag's `rmwc` is at most the number of executions with a result so far (each adds 1
to the `rmwc` of a tag carried from a base or a previous result; writes' tags have `rmwc = 0`),
at most `9 · 2^21` (unit A's `exec_nodup`: an instance of the box executes once per replica):
the tag-bound invariant `La.tinv` (unit L-a, `PureLa/Inv.lean`). -/
theorem rmwc_bounded {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (n : Nat)
    (r : Fin 3) : RmwcBounded (cutSt l n r) :=
  La.rmwc_cut h n r

theorem tagLt_rmwc_succ (t : model.Tag) (hb : sint.Z t.rmwc < 2 ^ 31 - 1) :
    tagLt t.toP ({ t with rmwc := t.rmwc + 1 } : model.Tag).toP := by
  have : sint.Z (t.rmwc + 1) = sint.Z t.rmwc + 1 := by
    unfold sint.Z at *
    rw [BitVec.toInt_add_of_not_saddOverflow]
    · simp
    · have := BitVec.le_toInt t.rmwc
      simp [BitVec.saddOverflow]; omega
  unfold tagLt model.Tag.toP
  right; refine ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
  show sint.Z t.rmwc < sint.Z (t.rmwc + 1)
  rw [this]; omega

end Perennial.gryff.pure
