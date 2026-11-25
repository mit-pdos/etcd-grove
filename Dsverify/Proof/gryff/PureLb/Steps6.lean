/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/Steps6.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b: `RInv`'s step for client reads (a fresh record, `Read1`s carrying the coordinator's
store, the new number joining unsent writes' short reads), and `RInv` along every run.
-/
module

public import Dsverify.Proof.gryff.PureLb.Steps5

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-- Client reads. -/
theorem rinv_read {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {s' : RState} {o : List Out}
    {rid cid : w32} {k : w64} {d : Dep} (hs : StepAt l c i (.read rid cid k d) c' s' o)
    (hW : WInv l c) (hi : RInv l c) : RInv (l ++ [(i, .read rid cid k d)]) c' := by
  obtain ⟨hu0, hcid, hn24, ⟨X, rfl⟩, hL, hout⟩ := stepClientRead_spec' hs.ok
  have hops := ops_snoc_req (l := l) (i := i) (e := .read rid cid k d) rfl
  have hsti := hs.sti
  have hmono : ∀ R, (stR c R).used ⊆ (stR c' R).used := by
    intro R; by_cases hR : R = i
    · subst hR; rw [hsti]; exact fun _ h => List.mem_cons_of_mem _ h
    · rw [hs.stj hR]; exact fun _ h => h
  obtain ⟨hm, hr, hw⟩ := hi
  obtain ⟨hops', huniq⟩ := new_op_facts hops hW hu0 hr.uniq
  obtain ⟨hZn, hfr⟩ := fresh_n hr i
  have hid := hW.1.id i
  have hkne : ∀ cid' rid', (cid', rid') ∈ (stR c i).used → 0 ≤ sint.Z cid' →
      shiftInts rid' cid' ≠ shiftInts rid cid := by
    intro cid' rid' hu hc hk
    obtain ⟨a, b⟩ := shiftInts_inj hc hcid hk
    rw [a, b] at hu; exact hu0 hu
  -- the entries after the loop
  have hX : ∀ k' e, X.get? k' = some e → ∃ e0, (k' = (stR c i).maxN + 1 ∧ e0 =
      { requestId := rid, clientId := cid, isRead := true, shortReads := [] } ∨
      k' ≠ (stR c i).maxN + 1 ∧ (stR c i).ongoingReqs.get? k' = some e0) ∧
      e.requestId = e0.requestId ∧ e.clientId = e0.clientId ∧
      (e.shortReads = e0.shortReads ∨
        ((∃ K w, (K, w) ∈ (stR c i).wops ∧ w.sentWrite2Round = false ∧ w.n = k') ∧
          ∀ x ∈ e.shortReads, x ∈ e0.shortReads ∨ x = (stR c i).maxN + 1)) := by
    intro k' e he
    obtain ⟨e0, he0, h1, h2, h3⟩ := (hL k').2 e he
    rw [AMap.get?_put] at he0
    refine ⟨e0, ?_, h1, h2, h3⟩
    split at he0
    · cases he0; exact Or.inl ⟨by assumption, rfl⟩
    · exact Or.inr ⟨by assumption, he0⟩
  have hXold : ∀ k' e0, (stR c i).ongoingReqs.get? k' = some e0 → ∃ e, X.get? k' = some e ∧
      e.requestId = e0.requestId ∧ e.clientId = e0.clientId := by
    intro k' e0 he0
    have hne := ne_of_Z_lt (hfr _ _ he0).1
    have h1 := (hL k').1
    rw [AMap.get?_put, if_neg hne, he0] at h1
    cases hx : X.get? k' with
    | none => rw [hx] at h1; cases h1
    | some e =>
      obtain ⟨e0', he0', a, b, -⟩ := (hL k').2 e hx
      rw [AMap.get?_put, if_neg hne, he0] at he0'; cases he0'
      exact ⟨e, rfl, a, b⟩
  refine ⟨msgs_step hs hm hmono hops' (fun j x hx => ?_), ?_, fun ow how v' hv => ?_⟩
  · -- the `Read1`s
    unfold sentR at hx
    obtain ⟨y, hy, hy'⟩ := List.mem_filterMap.1 hx
    obtain ⟨dd, rfl, q, hq, hdq⟩ := hout y hy
    simp only at hy'
    split at hy'
    · rename_i hdj; subst hdj; cases hy'
      have hq' := dstOf_eq hdq
      refine ⟨i, hid, fun hdi => hq (by rw [hq', hdi, hid]), ?_, hcid, fun o' ho' hor hoc hoq => ?_⟩
      · rw [hsti]; exact List.mem_cons_self
      · rw [hops, List.mem_append, List.mem_singleton] at ho'
        rcases ho' with ho' | rfl
        · have := (hW.1.ops o' ho').1
          rw [hoc, hoq, hor] at this; exact absurd this hu0
        · simp only
          rw [cutSt_snoc (Nat.le_refl _), cutSt_len hs.run]; exact tagLe_refl _
    · cases hy'
  · obtain ⟨g1, g2, g3, g4, g5, -⟩ := hr
    have hnewmem : ({ g := l.length, r := i, j := (projR l i).length, cid := cid, rid := rid, inp := RegInput.read } : Op) ∈ ops (l ++ [(i, .read rid cid k d)]) := by
      rw [hops]; exact List.mem_append_right _ (List.mem_singleton_self _)
    have hmemops : ∀ o' ∈ ops l, o' ∈ ops (l ++ [(i, .read rid cid k d)]) := fun o' ho' => by
      rw [hops]; exact List.mem_append_left _ ho'
    refine ⟨fun R K' rd hr' => ?_, fun R K' w'' hw' => ?_, fun R => ?_, fun R k' e he => ?_,
      fun R => ?_, huniq⟩
    · by_cases hR : R = i
      · subst hR; rw [hsti] at hr' ⊢
        change ((stR c R).rops.put _ _).get? K' = some rd at hr'
        show _ ∧ _ ∧ _ ∧ ∃ e, X.get? rd.n = some e ∧ _
        rw [AMap.get?_put] at hr'
        split at hr'
        · rename_i hK; subst hK; cases hr'
          refine ⟨rfl, rfl, ⟨_, hnewmem, rfl, rfl, rfl, rfl⟩, ?_⟩
          have h1 := (hL ((stR c R).maxN + 1)).1
          rw [AMap.get?_put, if_pos rfl] at h1
          cases hx : X.get? ((stR c R).maxN + 1) with
          | none => rw [hx] at h1; cases h1
          | some e =>
            obtain ⟨e0, he0, a, b, -⟩ := hX _ e hx
            rcases he0 with ⟨-, rfl⟩ | ⟨hne, -⟩
            · exact ⟨e, hx, a, b⟩
            · exact absurd rfl hne
        · obtain ⟨a, b, ⟨o', ho', dd⟩, ⟨e0, he0, hea, heb⟩⟩ := g1 R K' rd hr'
          obtain ⟨e, he, ha, hb⟩ := hXold _ _ he0
          exact ⟨a, b, ⟨o', hmemops o' ho', dd⟩, e, he, ha.trans hea, hb.trans heb⟩
      · rw [hs.stj hR] at hr' ⊢
        obtain ⟨a, b, ⟨o', ho', dd⟩, f⟩ := g1 R K' rd hr'
        exact ⟨a, b, ⟨o', hmemops o' ho', dd⟩, f⟩
    · by_cases hR : R = i
      · subst hR; rw [hsti] at hw' ⊢
        obtain ⟨a, ⟨o', ho', dd⟩, ⟨e0, he0, hea, heb⟩, f⟩ := g2 R K' w'' hw'
        obtain ⟨e, he, ha, hb⟩ := hXold _ _ he0
        exact ⟨a, ⟨o', hmemops o' ho', dd⟩, ⟨e, he, ha.trans hea, hb.trans heb⟩, f⟩
      · rw [hs.stj hR] at hw' ⊢
        obtain ⟨a, ⟨o', ho', dd⟩, f⟩ := g2 R K' w'' hw'
        exact ⟨a, ⟨o', hmemops o' ho', dd⟩, f⟩
    · by_cases hR : R = i
      · subst hR; rw [hsti]; exact g3 R
      · rw [hs.stj hR]; exact g3 R
    · by_cases hR : R = i
      · subst hR; rw [hsti] at he ⊢
        show _ ∧ _ ≤ sint.Z ((stR c R).maxN + 1) ∧
          (∀ x ∈ e.shortReads, _ ≤ sint.Z ((stR c R).maxN + 1)) ∧
          _ ∈ (cid, rid) :: (stR c R).used ∧ _
        obtain ⟨e0, he0, ha, hb, hsr⟩ := hX k' e he
        have hsr' : ∀ x ∈ e.shortReads, x ∈ e0.shortReads ∨ x = (stR c R).maxN + 1 := by
          rcases hsr with hsr | ⟨-, hsr⟩
          · rw [hsr]; exact fun x hx => Or.inl hx
          · exact hsr
        have hm0 := (g5 R).1
        rcases he0 with ⟨rfl, rfl⟩ | ⟨hne, he0⟩
        · refine ⟨by omega, Int.le_refl _, fun x hx => ?_, by rw [ha, hb]; exact List.mem_cons_self,
            by rw [hb]; exact hcid⟩
          rcases hsr' x hx with hx | rfl
          · cases hx
          · exact Int.le_refl _
        · obtain ⟨a1, a2, a3, a4, a5⟩ := g4 R k' e0 he0
          refine ⟨a1, by omega, fun x hx => ?_, by rw [ha, hb]; exact List.mem_cons_of_mem _ a4,
            by rw [hb]; exact a5⟩
          rcases hsr' x hx with hx | rfl
          · have := a3 x hx; omega
          · exact Int.le_refl _
      · rw [hs.stj hR] at he ⊢; exact g4 R k' e he
    · by_cases hR : R = i
      · subst hR; rw [hsti]
        show 0 ≤ sint.Z ((stR c R).maxN + 1) ∧ sint.Z ((stR c R).maxN + 1) ≤ (stR c R).nReqs + 1 ∧
          (stR c R).nReqs + 1 ≤ 24
        have := g5 R; omega
      · rw [hs.stj hR]; exact g5 R
  · rw [hops, List.mem_append, List.mem_singleton] at how
    rcases how with how | rfl
    · have hnoW2 : ∀ j, ∀ x ∈ sentR j o, isW2 x = false := by
        intro j x hx
        unfold sentR at hx
        obtain ⟨y, hy, hy'⟩ := List.mem_filterMap.1 hx
        obtain ⟨dd, rfl, -⟩ := hout y hy
        simp only at hy'
        split at hy'
        · cases hy'; rfl
        · cases hy'
      refine w2rec_frame hs.tag_mono (hw ow how v' hv) ?_ ?_ ?_ (fun sent C h => ?_)
      · exact hs.filter_eq _ _ (fun x hx => by cases hx)
          (filter_sentTo_nilW2 (hnoW2 _) _ (fun _ => w2rOf_isW2))
      · exact fun q => hs.countP_le q _ (countP_sentTo_zeroW2 (hnoW2 q) _ (fun _ => w2of_isW2))
      · intro q x hx hxw
        rcases hs.mem hx with h | h
        · exact h
        · have := hnoW2 q _ h; simp [isW2] at this
      · by_cases hR : ow.r = i
        · rw [hR] at h ⊢; rw [hsti]
          intro w hw'
          change (stR c i).wops.get? _ = _ at hw'
          obtain ⟨a, b, dd, f, nr⟩ := h w hw'
          refine ⟨a, b, dd, fun e he k' hk' e' he' hr' o' ho' hor hoc hoq g2 wt hs' => ?_, nr⟩
          change X.get? w.n = some e at he
          change X.get? k' = some e' at he'
          change (((stR c i).rops.put _ _).get? _).isSome = true at hr'
          have hwm := AMap.mem_of_get? hw'
          obtain ⟨hK1, -, ⟨e1, he1, he1a, he1b⟩, -⟩ := hr.wops i _ w hwm
          obtain ⟨e0, he0, ha, hb, hsr⟩ := hX _ e he
          rcases he0 with ⟨hn, -⟩ | ⟨-, he0⟩
          · exact absurd hn (ne_of_Z_lt (hfr _ _ he1).1)
          rw [he1] at he0; cases he0
          -- a sent write's short reads are unchanged
          have hsw : w.sentWrite2Round = true := by
            cases hsw : w.sentWrite2Round
            · rw [a.2 hsw] at hs'; cases hs'
            · rfl
          have hsr2 : e.shortReads = e1.shortReads := by
            rcases hsr with hsr | ⟨⟨K2, w2, hw2, hw2s, hw2n⟩, -⟩
            · exact hsr
            · exfalso
              obtain ⟨hK2, -, ⟨e2, he2, he2a, he2b⟩, -⟩ := hr.wops i _ w2 hw2
              rw [hw2n, he1] at he2; cases he2
              have hK : K2 = ow.key := by
                rw [hK2, ← he2a, ← he2b, he1a, he1b, ← hK1]
              rw [hK] at hw2
              have := AMap.get?_of_mem (hr.sorted i) hw2
              rw [hw'] at this; cases this
              rw [hsw] at hw2s; cases hw2s
          rw [hsr2] at hk'
          have hk'n := ne_of_Z_lt ((hfr _ _ he1).2 k' hk')
          obtain ⟨e0', he0', ha', hb', -⟩ := hX _ e' he'
          rcases he0' with ⟨hn, -⟩ | ⟨-, he0'⟩
          · exact absurd hn hk'n
          obtain ⟨-, -, -, hu', hc'⟩ := hr.ongoing i k' e0' he0'
          rw [AMap.get?_put, if_neg (by rw [ha', hb']; exact hkne _ _ hu' hc')] at hr'
          rw [ha', hb'] at hr'
          rw [hops, List.mem_append, List.mem_singleton] at ho'
          rcases ho' with ho' | rfl
          · exact f e1 he1 k' hk' e0' he0' hr' o' ho' hor (hoc.trans hb') (hoq.trans ha') g2 wt hs'
          · simp only at hoc hoq
            rw [hb'] at hoc; rw [ha'] at hoq
            rw [← hoc, ← hoq] at hu'; exact absurd hu' hu0
        · rw [hs.stj hR]
          exact w2st_congr ⟨rfl, rfl, rfl⟩ (fun o' ho' => by
            rcases hops' o' ho' with h' | h'
            · exact Or.inl h'
            · exact Or.inr (fun hr' => hr' ▸ h')) (fun k e he => (hr.ongoing _ k e he).2.2.2.1) h
    · cases hv

end Perennial.gryff.pure
