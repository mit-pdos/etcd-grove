/-
**The store's tracked compaction under its steps** (stage 2, the snapshot image's (a), 2026-11-05;
pure). Lean-first (no Rocq counterpart).

`snap.cmpOk L m X rc jc` (`CutDefs`, what the batch lock's resource keeps of a compacting real
backend, `InvStore`'s `cmpTrack`) under each step that moves its arguments:
* `cmpOk_append`: a commit's new revision (`storeTxnWrite.End`: the log and the logical view grow,
  `cutAt_append`, `jobPast_append`; a recorded delete is of an older revision, so no new key is
  recorded deleted);
* `cmpOk_sched`: `Compact`'s scheduled record raised to `rev` (`updateCompactRev`: the compaction
  revision becomes `rev`, `entsCutAt_mono`);
* `cmpOk_fin`: the running job's finished record at its revision (the compaction revision unchanged:
  the job's revision is between the finished record and it);
* `cmpOk_crev`: the compaction revision is `-1` or a revision of the log.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.SnapImage

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace snap

section pure
variable [GooseExts]

/-- The finished record is at most the compaction revision. -/
theorem CmpRecs_finRev_le_crev (r : CmpRecs) : r.finRev ≤ r.crev := by
  unfold CmpRecs.crev CmpRecs.resumes
  split
  · rename_i h; simp only [decide_eq_true_eq] at h; omega
  · omega

/-- The compaction revision is `-1` or a revision of the log. -/
theorem cmpOk_crev {L : Log} {m : Bucket} {X : backend.VData} {rc : CmpRecs} {jc : Int × Rev}
    (h : cmpOk L m X rc jc) (hL : 0 < L.length) : -1 ≤ rc.crev ∧ rc.crev < L.length := by
  obtain ⟨-, -, -, hrec, -⟩ := h
  refine ⟨CmpRecs.crev_ge L rc hrec, ?_⟩
  have hm := CmpRecs.crev_le_max rc
  have hf : rc.finRev < L.length := by
    unfold CmpRecs.finRev
    cases hx : rc.fin with
    | none => simp; omega
    | some x => have := (hrec.1 x hx).2; simpa using this
  have hs : rc.schedRev < L.length := by
    unfold CmpRecs.schedRev
    cases hx : rc.sched with
    | none => simp; omega
    | some x => have := (hrec.2 x hx).2; simpa using this
  omega

/-- **A commit keeps the tracked compaction** (`storeTxnWrite.End`'s new revision `pend`). -/
theorem cmpOk_append {L : Log} {pend : List Change} (hb : LogB (L ++ [pend])) (hne : L ≠ [])
    {m : Bucket} {X : backend.VData} {rc : CmpRecs} {jc : Int × Rev}
    (h : cmpOk L m X rc jc) :
    cmpOk (L ++ [pend]) ((pendPuts L pend).foldl (fun m p => GMap.insert p.1 p.2 m) m) X rc jc := by
  obtain ⟨hc0, hc1⟩ := cmpOk_crev h (List.length_pos_iff.2 hne)
  obtain ⟨ents, hcut, hB, hrec, hpos, hX, hjp, hj0, hj1, hjf⟩ := h
  have hL63 : L.length + 1 < 2 ^ 63 := by have := hb.1; simp at this; omega
  have hXp : ∀ p ∈ pendPuts L pend, X.lookup (keyName, p.1) = none := by
    intro p hp
    cases hx : X.lookup (keyName, p.1) with
    | none => rfl
    | some x =>
      exfalso
      have hd := hX p.1 (by rw [hx]; rfl)
      obtain ⟨-, r, t, hr, -, hrc, -⟩ := hd
      rw [← entsOfRev_pairs L pend hne] at hp
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
      obtain ⟨i, cc, kv, -, -, rfl⟩ := (mem_entsOfRev _ _ _ e).1 he
      simp only [KvEnt.pair] at hr
      obtain ⟨-, hre⟩ := revBytes_inj _ _ _ _ hr
      rw [← hre] at hrc
      simp only at hrc
      have : sint.Z (W64 (L.length : Int)) = L.length := by word
      omega
  obtain ⟨hcut', hB'⟩ := cutAt_append hb hne hc0 hc1 hcut hB hXp
  have hpre : L <+: L ++ [pend] := List.prefix_append _ _
  refine ⟨_, hcut', hB', ⟨fun x hx => ?_, fun x hx => ?_⟩, hpos, fun k hk => ?_,
    jobPast_append hb hne hj0 (by omega) hjp, hj0, hj1, hjf⟩
  · have := hrec.1 x hx; simp; omega
  · have := hrec.2 x hx; simp; omega
  · exact (KeyDel_prefix L (L ++ [pend]) hpre hb rc.crev hc0 hc1 k).2 (hX k hk)

/-- **`Compact`'s scheduled record keeps the tracked compaction**, its revision now `rev` (above
the old one, a revision of the log, past `0`). -/
theorem cmpOk_sched {L : Log} (hb : LogB L) {m : Bucket} {X : backend.VData}
    {rc : CmpRecs} {jc : Int × Rev} (h : cmpOk L m X rc jc) (rev : Int) (h1 : 1 ≤ rev)
    (hcr : rc.crev ≤ rev) (hrl : rev < L.length) :
    cmpOk L m X ⟨rc.fin, some (W64 rev)⟩ jc ∧ CmpRecs.crev ⟨rc.fin, some (W64 rev)⟩ = rev := by
  have hc0 : -1 ≤ rc.crev := by obtain ⟨-, -, -, hrec, -⟩ := h; exact CmpRecs.crev_ge L rc hrec
  have hL63 : L.length < 2 ^ 63 := by have := hb.1; omega
  have hz : sint.Z (W64 rev) = rev := by word
  have hfc := CmpRecs_finRev_le_crev rc
  have hcr' : CmpRecs.crev ⟨rc.fin, some (W64 rev)⟩ = rev := by
    unfold CmpRecs.crev CmpRecs.resumes CmpRecs.schedRev
    have hf : CmpRecs.finRev ⟨rc.fin, some (W64 rev)⟩ = rc.finRev := rfl
    simp only [Option.map_some, Option.getD_some, hz, hf]
    split
    · rfl
    · rename_i hn; simp only [decide_eq_true_eq, not_and, Int.not_lt] at hn
      have := hn (by omega); omega
  obtain ⟨ents, hcut, hB, hrec, hpos, hX, hjp, hj0, hj1, hjf⟩ := h
  refine ⟨⟨ents, ?_, hB, ⟨hrec.1, fun x hx => ?_⟩, ⟨hpos.1, fun x hx => ?_⟩, fun k hk => ?_, hjp,
    hj0, ?_, hjf⟩, hcr'⟩
  · rw [hcr']; exact entsCutAt_mono hb hc0 hcr hrl hcut
  · simp only [Option.some.injEq] at hx; subst hx; rw [hz]; omega
  · simp only [Option.some.injEq] at hx; subst hx; rw [hz]; exact h1
  · rw [hcr']; exact KeyDel_mono hb hc0 hcr hrl (hX k hk)
  · rw [hcr']; omega

/-- **The running job's finished record keeps the tracked compaction**, its revision unchanged
(the job's revision `c₁` is between the finished record and it). -/
theorem cmpOk_fin {L : Log} (hb : LogB L) (hL : 0 < L.length) {m : Bucket} {X : backend.VData}
    {rc : CmpRecs} {c₁ : Int} {p : Rev} (h : cmpOk L m X rc (c₁, p)) (h1 : 1 ≤ c₁) :
    cmpOk L m X ⟨some (W64 c₁), rc.sched⟩ (c₁, p) ∧
      CmpRecs.crev ⟨some (W64 c₁), rc.sched⟩ = rc.crev := by
  obtain ⟨-, hc1⟩ := cmpOk_crev h hL
  have hL63 : L.length < 2 ^ 63 := by have := hb.1; omega
  obtain ⟨ents, hcut, hB, hrec, hpos, hX, hjp, hj0, hj1, hjf⟩ := h
  simp only at hj0 hj1 hjf
  have hz : sint.Z (W64 c₁) = c₁ := by word
  have hcr' : CmpRecs.crev ⟨some (W64 c₁), rc.sched⟩ = rc.crev := by
    have hf : CmpRecs.finRev ⟨some (W64 c₁), rc.sched⟩ = c₁ := by
      unfold CmpRecs.finRev; simp [hz]
    have hs : CmpRecs.schedRev ⟨some (W64 c₁), rc.sched⟩ = rc.schedRev := rfl
    revert hj1 hjf
    unfold CmpRecs.crev CmpRecs.resumes
    rw [hf, hs]
    intro hj1 hjf
    by_cases hr : rc.schedRev ≠ 0 ∧ rc.finRev < rc.schedRev
    · simp only [hr, and_self, decide_true, ↓reduceIte] at hj1 ⊢
      by_cases hc : c₁ < rc.schedRev
      · simp [hr.1, hc]
      · have : c₁ = rc.schedRev := by omega
        simp [hc, this, hr.1]
    · simp only [hr, decide_false, Bool.false_eq_true, ↓reduceIte] at hj1 ⊢
      have hc : c₁ = rc.finRev := by omega
      have : ¬ (rc.schedRev ≠ 0 ∧ c₁ < rc.schedRev) := by rw [hc]; exact hr
      simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact hc
  refine ⟨⟨ents, ?_, hB, ⟨fun x hx => ?_, hrec.2⟩, ⟨fun x hx => ?_, hpos.2⟩, ?_, hjp, hj0, ?_,
    ?_⟩, hcr'⟩
  · rw [hcr']; exact hcut
  · simp only [Option.some.injEq] at hx; subst hx; rw [hz]; omega
  · simp only [Option.some.injEq] at hx; subst hx; rw [hz]; exact h1
  · rw [hcr']; exact hX
  · rw [hcr']; exact hj1
  · show CmpRecs.finRev ⟨some (W64 c₁), rc.sched⟩ ≤ c₁
    unfold CmpRecs.finRev; simp [hz]

end pure

end snap
end mvcc
end EtcdGrove
end Perennial
