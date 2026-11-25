/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/Steps5.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b: `RInv`'s step for client writes and reads (new records, fresh entry numbers).
-/
module

public import Dsverify.Proof.gryff.PureLb.Steps4

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-- The new entry number is above every entry's number and short reads. -/
theorem fresh_n {l : List Label} {c : Cfg gNet} (hr : RRec l c) (i : Fin 3) :
    sint.Z ((stR c i).maxN + 1) = sint.Z (stR c i).maxN + 1 ∧
    ∀ k e, (stR c i).ongoingReqs.get? k = some e → sint.Z k < sint.Z ((stR c i).maxN + 1) ∧
      ∀ x ∈ e.shortReads, sint.Z x < sint.Z ((stR c i).maxN + 1) := by
  have hm := hr.maxN i
  have e1 : sint.Z ((stR c i).maxN + 1) = sint.Z (stR c i).maxN + 1 := Z_succ32 (by omega)
  refine ⟨e1, fun k e he => ?_⟩
  obtain ⟨-, h2, h3, -⟩ := hr.ongoing i k e he
  exact ⟨by omega, fun x hx => by have := h3 x hx; omega⟩

theorem ne_of_Z_lt {a b : w32} (h : sint.Z a < sint.Z b) : a ≠ b := by
  intro e; subst e; omega

/-- Client writes. -/
theorem rinv_write {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {s' : RState} {o : List Out}
    {rid cid : w32} {k v : w64} {d : Dep} (hs : StepAt l c i (.write rid cid k v d) c' s' o)
    (hW : WInv l c) (hi : RInv l c) : RInv (l ++ [(i, .write rid cid k v d)]) c' := by
  obtain ⟨hu0, hcid, hn24, rfl, hnor⟩ := stepClientWrite_spec' hs.ok
  obtain ⟨-, -, -, -, -, m0, -, -, -, hm0⟩ := stepClientWrite_spec hs.ok
  have hops := ops_snoc_req (l := l) (i := i) (e := .write rid cid k v d) rfl
  have hmono : ∀ R, (stR c R).used ⊆ (stR c' R).used := by
    intro R; by_cases hR : R = i
    · subst hR; rw [hs.sti]; exact fun _ h => List.mem_cons_of_mem _ h
    · rw [hs.stj hR]; exact fun _ h => h
  obtain ⟨hm, hr, hw⟩ := hi
  obtain ⟨hops', huniq⟩ := new_op_facts hops hW hu0 hr.uniq
  obtain ⟨hZn, hfr⟩ := fresh_n hr i
  have hsti := hs.sti
  have hsent : ∀ j, sentR j o = [.write1 m0] := by intro j; rw [hm0]; exact sentR_three' _ j
  -- old keys differ from the new one
  have hkne : ∀ cid' rid', (cid', rid') ∈ (stR c i).used → 0 ≤ sint.Z cid' →
      shiftInts rid' cid' ≠ shiftInts rid cid := by
    intro cid' rid' hu hc hk
    obtain ⟨a, b⟩ := shiftInts_inj hc hcid hk
    rw [a, b] at hu; exact hu0 hu
  refine ⟨msgs_step hs hm hmono hops' (fun j x hx => by
      rw [hsent, List.mem_singleton] at hx; subst hx; trivial), ?_, fun ow how v' hv => ?_⟩
  · obtain ⟨g1, g2, g3, g4, g5, -⟩ := hr
    refine ⟨fun R K' rd hr' => ?_, fun R K' w'' hw' => ?_, fun R => ?_, fun R k' e he => ?_,
      fun R => ?_, huniq⟩
    · by_cases hR : R = i
      · subst hR; rw [hsti] at hr' ⊢
        obtain ⟨a, b, ⟨o', ho', dd⟩, ⟨e, he, hea, heb⟩⟩ := g1 R K' rd hr'
        refine ⟨a, b, ⟨o', by rw [hops]; exact List.mem_append_left _ ho', dd⟩, e, ?_, hea, heb⟩
        show ((stR c R).ongoingReqs.put _ _).get? _ = _
        rw [AMap.get?_put, if_neg (ne_of_Z_lt (hfr _ _ he).1)]; exact he
      · rw [hs.stj hR] at hr' ⊢
        obtain ⟨a, b, ⟨o', ho', dd⟩, f⟩ := g1 R K' rd hr'
        exact ⟨a, b, ⟨o', by rw [hops]; exact List.mem_append_left _ ho', dd⟩, f⟩
    · by_cases hR : R = i
      · subst hR; rw [hsti] at hw' ⊢
        change (K', w'') ∈ (stR c R).wops.put _ _ at hw'
        rcases AMap.mem_put hw' with hw' | hw'
        · cases hw'
          refine ⟨rfl, ⟨_, by rw [hops]; exact List.mem_append_right _ (List.mem_singleton_self _),
            rfl, ⟨v, rfl⟩, rfl, rfl⟩,
            ⟨{ requestId := rid, clientId := cid, isRead := false, shortReads := [] }, ?_, rfl, rfl⟩,
            rfl, rfl⟩
          show ((stR c R).ongoingReqs.put _ _).get? _ = _
          rw [AMap.get?_put, if_pos rfl]
        · obtain ⟨a, ⟨o', ho', dd⟩, ⟨e, he, hea, heb⟩, f⟩ := g2 R K' w'' hw'
          refine ⟨a, ⟨o', by rw [hops]; exact List.mem_append_left _ ho', dd⟩, ⟨e, ?_, hea, heb⟩, f⟩
          show ((stR c R).ongoingReqs.put _ _).get? _ = _
          rw [AMap.get?_put, if_neg (ne_of_Z_lt (hfr _ _ he).1)]; exact he
      · rw [hs.stj hR] at hw' ⊢
        obtain ⟨a, ⟨o', ho', dd⟩, f⟩ := g2 R K' w'' hw'
        exact ⟨a, ⟨o', by rw [hops]; exact List.mem_append_left _ ho', dd⟩, f⟩
    · by_cases hR : R = i
      · subst hR; rw [hsti]; exact AMap.sorted_put (g3 R) _ _
      · rw [hs.stj hR]; exact g3 R
    · by_cases hR : R = i
      · subst hR; rw [hsti] at he ⊢
        change ((stR c R).ongoingReqs.put _ _).get? _ = _ at he
        rw [AMap.get?_put] at he
        show _ ∧ _ ≤ sint.Z ((stR c R).maxN + 1) ∧ (∀ x ∈ e.shortReads, _ ≤ sint.Z ((stR c R).maxN + 1)) ∧
          _ ∈ (cid, rid) :: (stR c R).used ∧ _
        split at he
        · cases he; rename_i hk; subst hk
          have := (g5 R).1
          exact ⟨by omega, Int.le_refl _, (fun x hx => by cases hx), List.mem_cons_self, hcid⟩
        · obtain ⟨a, b, f, gg, h⟩ := g4 R k' e he
          exact ⟨a, by omega, fun x hx => by have := f x hx; omega, List.mem_cons_of_mem _ gg, h⟩
      · rw [hs.stj hR] at he ⊢; exact g4 R k' e he
    · by_cases hR : R = i
      · subst hR; rw [hsti]
        show 0 ≤ sint.Z ((stR c R).maxN + 1) ∧ sint.Z ((stR c R).maxN + 1) ≤ (stR c R).nReqs + 1 ∧
          (stR c R).nReqs + 1 ≤ 24
        have := g5 R; omega
      · rw [hs.stj hR]; exact g5 R
  · rw [hops, List.mem_append, List.mem_singleton] at how
    rcases how with how | rfl
    · refine w2rec_frame hs.tag_mono (hw ow how v' hv) ?_ ?_ ?_ (fun sent C h => ?_)
      · exact hs.filter_eq _ _ (fun x hx => by cases hx) (by rw [hsent]; rfl)
      · exact fun q => hs.countP_le q _ (by rw [hsent]; rfl)
      · intro q x hx hxw
        rcases hs.mem hx with h | h
        · exact h
        · rw [hsent, List.mem_singleton] at h; cases h
      · by_cases hR : ow.r = i
        · rw [hR] at h ⊢; rw [hsti]
          intro w hw'
          change ((stR c i).wops.put _ _).get? _ = _ at hw'
          have hu := hW.1.ops ow how
          rw [AMap.get?_put, if_neg (by rw [hR] at hu; exact hkne _ _ hu.1 hu.2)] at hw'
          obtain ⟨a, b, dd, f, nr⟩ := h w hw'
          refine ⟨a, b, dd, fun e he k' hk' e' he' hr' o' ho' hor hoc hoq g2 wt hs' => ?_, nr⟩
          obtain ⟨-, -, ⟨e1, he1, -, -⟩, -⟩ := hr.wops i _ w (AMap.mem_of_get? hw')
          have hwn := ne_of_Z_lt (hfr _ _ he1).1
          change ((stR c i).ongoingReqs.put _ _).get? _ = _ at he he'
          rw [AMap.get?_put, if_neg hwn] at he
          rw [he1] at he; cases he
          rw [AMap.get?_put, if_neg (ne_of_Z_lt ((hfr _ _ he1).2 k' hk'))] at he'
          rcases hops' o' ho' with ho'' | ho''
          · exact f e he1 k' hk' e' he' hr' o' ho'' (by rw [hor, hR]) hoc hoq g2 wt hs'
          · exact absurd (by rw [hoc, hoq, hor, hR]; exact (hr.ongoing i k' e' he').2.2.2.1) ho''
        · rw [hs.stj hR]
          exact w2st_congr ⟨rfl, rfl, rfl⟩ (fun o' ho' => by
            rcases hops' o' ho' with h' | h'
            · exact Or.inl h'
            · exact Or.inr (fun hr' => hr' ▸ h')) (fun k e he => (hr.ongoing _ k e he).2.2.2.1) h
    · -- the new write
      simp only at hv ⊢
      have hc0 : ∀ q, (infR c' q).countP (w2of { g := l.length, r := i, j := (projR l i).length, cid, rid, inp := .write v }) = 0 := by
        intro q; rw [List.countP_eq_zero]; intro x hx hxw
        cases x with
        | write2 x =>
          obtain ⟨a, b, dd⟩ := w2of_eq hxw
          rcases hs.mem hx with hx | hx
          · obtain ⟨R, hR, hRu, -⟩ := hm q _ hx
            rw [hR] at dd; have := rid32_inj dd; subst this
            rw [a, b] at hRu; exact hu0 hRu
          · rw [hsent, List.mem_singleton] at hx; cases hx
        | _ => simp [w2of] at hxw
      refine ⟨none, [], [], List.nodup_nil, ?_, fun q => ⟨by rw [hc0 q]; omega, fun _ => hc0 q⟩,
        fun q x hx hxw => ?_, fun _ => ⟨rfl, rfl⟩, (fun g2 wt h => by cases h), ?_⟩
      · suffices (infR c' i).filter (w2rOf { g := l.length, r := i, j := (projR l i).length, cid, rid, inp := .write v }) = [] by
          rw [this]; exact List.Perm.nil
        rw [List.filter_eq_nil_iff]; intro x hx hxw
        cases x with
        | write2Reply x =>
          obtain ⟨a, b⟩ := w2rOf_eq hxw
          rcases hs.mem hx with hx | hx
          · obtain ⟨hu, -⟩ := hm i _ hx
            rw [a, b] at hu; exact hu0 hu
          · rw [hsent, List.mem_singleton] at hx; cases hx
        | _ => simp [w2rOf] at hxw
      · have := List.countP_pos_iff.2 ⟨_, hx, hxw⟩; rw [hc0 q] at this; cases this
      · intro w hw'
        rw [hsti] at hw'
        change ((stR c i).wops.put _ _).get? (shiftInts rid cid) = _ at hw'
        rw [AMap.get?_put, if_pos rfl] at hw'
        cases hw'
        refine ⟨by simp, (fun g2 wt h => by cases h), by simp [sint.Z], ?_, by simp [sint.Z]⟩
        intro e he k' hk' e' he' hr' o' ho' hor hoc hoq g2 wt h; cases h

end Perennial.gryff.pure
