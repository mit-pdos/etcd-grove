/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/Once.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b: **a read or write is replied to at most once** (`reply_once_rw`): its reply's step
deletes its record (`reply_rec`), a deleted record is never re-created (`rec_none_step`: keys are
fresh), and every reply needs the live record.
-/
module

public import Dsverify.Proof.gryff.PureLb.L2W

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-- **No re-creation**: an operation's absent record stays absent through a step at its
coordinator (a new record's key is fresh; the operation's key is used). -/
theorem rec_none_step {l : List Label} {c : Cfg gNet} {i : Fin 3} {e : Ev} {s' : RState}
    {outs : List Out} (hc : ReplyCtx l c i e s' outs) {o : Op} (ho : o ∈ ops l) (hor : o.r = i) :
    ((stR c i).rops.get? o.key = none → s'.rops.get? o.key = none) ∧
    ((stR c i).wops.get? o.key = none → s'.wops.get? o.key = none) := by
  obtain ⟨hM, hR, -⟩ := rinv hc.run
  have hu := (winv hc.run).1.ops o ho
  rw [hor] at hu
  have hstep := hc.ok
  -- the key of a new request differs from `o`'s
  have hfresh : ∀ rid cid, (cid, rid) ∉ (stR c i).used → 0 ≤ sint.Z cid →
      o.key ≠ shiftInts rid cid := by
    intro rid cid hn hcid hk
    obtain ⟨a, b⟩ := shiftInts_inj hu.2 hcid hk
    rw [a, b] at hu; exact hn hu.1
  cases e with
  | read rid cid k d =>
    obtain ⟨hn, hcid, -, ⟨X, rfl⟩, -⟩ := stepClientRead_spec' hstep
    refine ⟨fun h0 => ?_, fun h0 => h0⟩
    show ((stR c i).rops.put _ _).get? _ = none
    rw [AMap.get?_put, if_neg (hfresh rid cid hn hcid)]; exact h0
  | write rid cid k v d =>
    obtain ⟨hn, hcid, -, rfl, -⟩ := stepClientWrite_spec' hstep
    refine ⟨fun h0 => h0, fun h0 => ?_⟩
    show ((stR c i).wops.put _ _).get? _ = none
    rw [AMap.get?_put, if_neg (hfresh rid cid hn hcid)]; exact h0
  | rmw rid cid k d a b =>
    rw [(stepClientRMW_fr hstep).1, (stepClientRMW_spec hstep).2.2.2.2.1]
    exact ⟨id, id⟩
  | msg m =>
    cases m with
    | read1Reply m =>
      rw [(stepRead1Reply_fw hstep).1.1]
      refine ⟨fun h0 => ?_, id⟩
      cases hk : (stR c i).rops.get? (shiftInts m.requestId m.clientId) with
      | none => obtain ⟨rfl, -⟩ := stepRead1Reply_none hk hstep; exact h0
      | some rd =>
        have hfr := (hR.rops i _ rd hk).1
        rw [hfr] at hk
        obtain ⟨rfl, -⟩ := stepRead1Reply_fresh hk hstep
        show ((stR c i).rops.del _).get? _ = none
        rw [AMap.get?_del]; split
        · rfl
        · exact h0
    | read2 m => exact (hM i _ (hc.recv _ rfl)).elim
    | read2Reply m => exact (hM i _ (hc.recv _ rfl)).elim
    | write1Reply m =>
      obtain ⟨-, -, -, hK1, hK2, -⟩ := stepWrite1Reply_spec hstep
      refine ⟨fun h0 => ?_, fun h0 => ?_⟩
      · cases hk : (stR c i).wops.get? (shiftInts m.requestId m.clientId) with
        | none => obtain ⟨rfl, -⟩ := stepWrite1Reply_none hk hstep; exact h0
        | some w =>
          obtain ⟨-, -, -, hwv, hwa⟩ := hR.wops i _ w (AMap.mem_of_get? hk)
          obtain ⟨w', rfl, -⟩ := stepWrite1Reply_some hk hwv hwa (hM i _ (hc.recv _ rfl)) hstep
          exact h0
      · by_cases hk : o.key = shiftInts m.requestId m.clientId
        · rw [hk] at h0 ⊢; exact hK2 h0
        · rw [hK1 _ hk]; exact h0
    | write2Reply m =>
      obtain ⟨-, -, -, hK1, hK2, -⟩ := stepWrite2Reply_spec hstep
      refine ⟨fun h0 => ?_, fun h0 => ?_⟩
      · cases hk : (stR c i).wops.get? (shiftInts m.requestId m.clientId) with
        | none => obtain ⟨rfl, -⟩ := stepWrite2Reply_none hk hstep; exact h0
        | some w =>
          rcases stepWrite2Reply_some hk hstep with ⟨rfl, -⟩ | ⟨wt, s1, outs', -, hsc, rfl, -⟩
          · exact h0
          · show s1.rops.get? _ = none
            rcases hsc with ⟨-, hsc⟩ | ⟨rfl, -⟩
            · obtain ⟨X, Y, rfl, -, hY, -⟩ := shortCircuit_spec hsc
              cases hy : Y.get? o.key with
              | none => rfl
              | some y => rw [hY _ _ hy] at h0; cases h0
            · exact h0
      · by_cases hk : o.key = shiftInts m.requestId m.clientId
        · rw [hk] at h0 ⊢; exact hK2 h0
        · rw [hK1 _ hk]; exact h0
    | write1 m =>
      rw [(stepWrite1_fr hstep).1, (stepWrite1_spec hstep).1.1]; exact ⟨id, id⟩
    | write2 m =>
      obtain ⟨h1, h2, -⟩ := stepWrite2_spec hstep
      rw [h1.1, h2.1]; exact ⟨id, id⟩
    | read1 m =>
      obtain ⟨h1, h2, -⟩ := stepRead1_spec hstep
      rw [h1.1, h2.1]; exact ⟨id, id⟩
    | _ =>
      rw [(step_fr_other hstep rfl).1.1, (step_fw_other hstep rfl).1.1]; exact ⟨id, id⟩
  | _ =>
    rw [(step_fr_other hstep rfl).1.1, (step_fw_other hstep rfl).1.1]; exact ⟨id, id⟩

/-- A property of `o`'s coordinator's state kept by its steps after `o`'s creation persists. -/
theorem cut_persist {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (P : RState → Prop)
    (hP : ∀ k, o.g < k → ∀ e cn s' outs, ReplyCtx (l.take k) cn o.r e s' outs →
      P (stR cn o.r) → P s')
    {n : Nat} (hn : o.g < n) (hP0 : P (cutSt l n o.r)) :
    ∀ d, P (cutSt l (n + d) o.r) := by
  intro d
  induction d with
  | zero => exact hP0
  | succ d ih =>
    rw [← Nat.add_assoc]
    cases hk : l[n + d]? with
    | none =>
      have : l.length ≤ n + d := List.getElem?_eq_none_iff.1 hk
      unfold cutSt at ih ⊢
      rw [List.take_of_length_le (by omega)] at ih ⊢
      exact ih
    | some x =>
      obtain ⟨R, e⟩ := x
      obtain ⟨cn, s', outs, hc, -, hcs, hR1, hR2⟩ := label_ctx h hk
      by_cases hR : R = o.r
      · subst hR
        rw [hR1]; rw [hcs] at ih
        exact hP _ (by omega) e cn s' outs hc ih
      · rw [hR2 _ (Ne.symm hR)]; exact ih

/-- At a reply to a read or write `o`, its record is live before the step and absent after. -/
theorem reply_rec {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {n : Nat} (hr : RepliesTo l n o) :
    (o.inp = .read → (cutSt l n o.r).rops.get? o.key ≠ none ∧
      (cutSt l (n + 1) o.r).rops.get? o.key = none) ∧
    (∀ v, o.inp = .write v → (cutSt l n o.r).wops.get? o.key ≠ none ∧
      (cutSt l (n + 1) o.r).wops.get? o.key = none) := by
  obtain ⟨e, cn, s', outs, x, -, hc, -, hcs, hR1, -, -, hxo, hxk, hfit⟩ := reply_is_own h ho hr
  rw [hcs, hR1]
  cases x with
  | readReply cid rid v f =>
    simp only [Ext.key, Prod.mk.injEq] at hxk
    obtain ⟨rfl, rfl⟩ := hxk
    obtain ⟨-, a, b⟩ := readReply_owner hc hxo
    refine ⟨fun _ => ⟨a, b⟩, fun v hv => ?_⟩
    rw [hv] at hfit; exact hfit.elim
  | writeReply cid rid f =>
    simp only [Ext.key, Prod.mk.injEq] at hxk
    obtain ⟨rfl, rfl⟩ := hxk
    obtain ⟨m, w, wt, -, -, hk, -, -, -, -, hKeq, hnone, -⟩ := writeReply_owner hc hxo
    refine ⟨fun hv => ?_, fun _ _ => ⟨?_, hnone⟩⟩
    · rw [hv] at hfit; exact hfit.elim
    · show (stR cn o.r).wops.get? (shiftInts o.rid o.cid) ≠ none
      rw [← hKeq, hk]; simp
  | rmwReply =>
    refine ⟨fun hv => ?_, fun v hv => ?_⟩ <;> (rw [hv] at hfit; exact hfit.elim)

/-- **A read or write is replied to at most once.** -/
theorem reply_once_rw {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) (hk : o.inp = .read ∨ ∃ v, o.inp = .write v) {n n' : Nat}
    (r1 : RepliesTo l n o) (r2 : RepliesTo l n' o) : n = n' := by
  -- the later reply finds the record deleted by the earlier one
  have key : ∀ {a b}, RepliesTo l a o → RepliesTo l b o → a < b → False := by
    intro a b ra rb hab
    have hga := ra.1
    have hok : ∀ k, o.g < k → o ∈ ops (l.take k) := fun k hk => by
      rw [← ops_take, List.mem_filter]; exact ⟨ho, by simp; omega⟩
    obtain ⟨ra1, ra2⟩ := reply_rec h ho ra
    obtain ⟨rb1, rb2⟩ := reply_rec h ho rb
    rcases hk with hk | ⟨v, hk⟩
    · have hP := cut_persist h (fun s => s.rops.get? o.key = none)
        (fun k hk e cn s' outs hc h0 => (rec_none_step hc (hok k hk) rfl).1 h0)
        (n := a + 1) (by omega) (ra1 hk).2 (b - (a + 1))
      rw [show a + 1 + (b - (a + 1)) = b by omega] at hP
      exact (rb1 hk).1 hP
    · have hP := cut_persist h (fun s => s.wops.get? o.key = none)
        (fun k hk e cn s' outs hc h0 => (rec_none_step hc (hok k hk) rfl).2 h0)
        (n := a + 1) (by omega) (ra2 v hk).2 (b - (a + 1))
      rw [show a + 1 + (b - (a + 1)) = b by omega] at hP
      exact (rb2 v hk).1 hP
  rcases Nat.lt_trichotomy n n' with h1 | h1 | h1
  · exact (key r1 r2 h1).elim
  · exact h1
  · exact (key r2 r1 h1).elim

end Perennial.gryff.pure
