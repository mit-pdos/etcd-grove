/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/Steps3.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b: `RInv`'s step for `Write1Reply`s and `Write2Reply`s.
-/
module

public import Dsverify.Proof.gryff.PureLb.Steps2

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-- The records after replacing one write record by one with the same ids and number. -/
theorem rrec_wput {l l' : List Label} {c c' : Cfg gNet} {i : Fin 3} {K : w64} {w w' : WriteOp}
    (hr : RRec l c) (hops : ops l' = ops l)
    (hst : stR c' i = { stR c i with wops := (stR c i).wops.put K w' })
    (hstj : ∀ j, j ≠ i → stR c' j = stR c j)
    (hmem : (K, w) ∈ (stR c i).wops)
    (e1 : w'.requestId = w.requestId) (e2 : w'.clientId = w.clientId) (e3 : w'.n = w.n)
    (e4 : w'.maxValTag.v = -1) (e5 : w'.numWrite1Applies = 0) : RRec l' c' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
  refine ⟨fun R K' rd hr' => ?_, fun R K' w'' hw' => ?_, fun R => ?_, fun R k e he => ?_,
    fun R => ?_, by rw [hops]; exact h6⟩
  · by_cases hR : R = i
    · subst hR; rw [hst] at hr' ⊢
      obtain ⟨a, b, ⟨o', ho', d⟩, f⟩ := h1 R K' rd hr'
      exact ⟨a, b, ⟨o', hops ▸ ho', d⟩, f⟩
    · rw [hstj R hR] at hr' ⊢
      obtain ⟨a, b, ⟨o', ho', d⟩, f⟩ := h1 R K' rd hr'
      exact ⟨a, b, ⟨o', hops ▸ ho', d⟩, f⟩
  · by_cases hR : R = i
    · subst hR; rw [hst] at hw' ⊢
      rcases AMap.mem_put hw' with hw' | hw'
      · cases hw'
        obtain ⟨a, ⟨o', ho', d⟩, f, g⟩ := h2 R K w hmem
        refine ⟨by rw [e1, e2]; exact a, ⟨o', hops ▸ ho', by rw [e1, e2]; exact d⟩,
          by rw [e1, e2, e3]; exact f, e4, e5⟩
      · obtain ⟨a, ⟨o', ho', d⟩, f⟩ := h2 R K' w'' hw'
        exact ⟨a, ⟨o', hops ▸ ho', d⟩, f⟩
    · rw [hstj R hR] at hw' ⊢
      obtain ⟨a, ⟨o', ho', d⟩, f⟩ := h2 R K' w'' hw'
      exact ⟨a, ⟨o', hops ▸ ho', d⟩, f⟩
  · by_cases hR : R = i
    · subst hR; rw [hst]; exact AMap.sorted_put (h3 R) _ _
    · rw [hstj R hR]; exact h3 R
  · by_cases hR : R = i
    · subst hR; rw [hst] at he ⊢; exact h4 R k e he
    · rw [hstj R hR] at he ⊢; exact h4 R k e he
  · by_cases hR : R = i
    · subst hR; rw [hst]; exact h5 R
    · rw [hstj R hR]; exact h5 R

theorem sentR_three' (w : Msg) (j : Fin 3) :
    sentR j [.send 0 w, .send 1 w, .send 2 w] = [w] := sentR_three w j

/-- `Write1Reply`s: a record's counters, possibly the `Write2`s (never a short-circuit). -/
theorem rinv_write1Reply {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {s' : RState}
    {o : List Out} {m : Write1ReplyM} (hs : StepAt l c i (.msg (.write1Reply m)) c' s' o)
    (hW : WInv l c) (hi : RInv l c) : RInv (l ++ [(i, .msg (.write1Reply m))]) c' := by
  have hops := ops_snoc_none (l := l) (i := i) (e := .msg (.write1Reply m)) rfl
  have hmm : Msg.write1Reply m ∈ infR c i := hs.recv _ rfl
  cases hk : (stR c i).wops.get? (shiftInts m.requestId m.clientId) with
  | none =>
    obtain ⟨rfl, rfl⟩ := stepWrite1Reply_none hk hs.ok
    exact rinv_frame hs ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ hops (fun x hx => by cases hx; rfl)
      (fun j x hx => by cases hx) (fun j x hx => by cases hx) hi
  | some w =>
    obtain ⟨hm, hr, hw⟩ := hi
    have hmv : m.vt.v = -1 := hm i _ hmm
    have hmem := AMap.mem_of_get? hk
    obtain ⟨hK, ⟨ow, how, howr, ⟨v0, howv⟩, howc, howq⟩, -, hwv, hwa⟩ := hr.wops i _ w hmem
    obtain ⟨w', rfl, ew1, ew2, ew3, ew4, ew5, ew6, hbr⟩ := stepWrite1Reply_some hk hwv hwa hmv hs.ok
    have hnw2 := stepWrite1Reply_nw2r hk hwv hwa hmv hs.ok (w' := w')
      (by show ((stR c i).wops.put _ w').get? _ = _; rw [AMap.get?_put, if_pos rfl])
    have hkey : ow.key = shiftInts m.requestId m.clientId := by
      unfold Op.key; rw [howc, howq, hK]
    have hsti := hs.sti
    have hrr := rrec_wput (l' := l ++ [(i, .msg (.write1Reply m))]) hr hops hsti
      (fun j hj => hs.stj hj) hmem ew1 ew2 ew3 ew5 ew6
    -- other writes keep their records
    have hother : ∀ ow' ∈ ops l, ∀ v', ow'.inp = .write v' → ow' ≠ ow →
        (stR c' ow'.r).wops.get? ow'.key = (stR c ow'.r).wops.get? ow'.key ∧
        (stR c' ow'.r).ongoingReqs = (stR c ow'.r).ongoingReqs ∧
        (stR c' ow'.r).rops = (stR c ow'.r).rops := by
      intro ow' how' v' hv' hne
      by_cases hR : ow'.r = i
      · rw [hR, hsti]
        refine ⟨?_, rfl, rfl⟩
        show ((stR c i).wops.put _ w').get? _ = _
        rw [AMap.get?_put, if_neg]
        intro hk'
        rw [← hkey] at hk'
        obtain ⟨a, b⟩ := shiftInts_inj (hW.1.ops ow' how').2 (hW.1.ops ow how).2 hk'
        exact hne (hr.uniq ow' how' ow how (by rw [hR, howr]) b a)
      · rw [hs.stj hR]; exact ⟨rfl, rfl, rfl⟩
    rcases hbr with ⟨es1, es2, rfl⟩ | ⟨hsw, hsw', wt, hwt, m2, hm2a, hm2b, hm2c, hm2d, rfl⟩
    · -- no `Write2`s
      refine ⟨msgs_step hs hm (fun R => ?_) (fun o ho => Or.inl (hops ▸ ho))
        (fun j x hx => by cases hx), hrr, fun ow' how' v' hv' => ?_⟩
      · by_cases hR : R = i
        · subst hR; rw [hsti]; exact fun _ h => h
        · rw [hs.stj hR]; exact fun _ h => h
      rw [hops] at how'
      refine w2rec_frame hs.tag_mono (hw ow' how' v' hv') ?_ (fun q => hs.countP_le q _ rfl) ?_ ?_
      · exact hs.filter_eq _ _ (fun x hx => by cases hx; rfl) rfl
      · intro q x hx hxw
        rcases hs.mem hx with h | h
        · exact h
        · cases h
      · intro sent C h
        by_cases hne : ow' = ow
        · subst hne
          intro w'' hw''
          rw [howr, hsti, hkey] at hw''
          change ((stR c i).wops.put _ w').get? _ = _ at hw''
          rw [AMap.get?_put, if_pos rfl] at hw''
          cases hw''
          obtain ⟨a, b, d, f, nr⟩ := h w (by rw [howr, hkey]; exact hk)
          refine ⟨by rw [es1]; exact a, by rw [es2]; exact b, by rw [ew4]; exact d, ?_,
            by rw [hnw2]; exact nr⟩
          intro e he k hk' e' he' hr' o' ho' hor hoc hoq g2 wt hs'
          rw [howr, hsti] at he he' hr'
          rw [hops] at ho'
          rw [howr, ew3] at *
          exact f e he k hk' e' he' hr' o' ho' (by rw [hor, howr]) hoc hoq g2 wt hs'
        · obtain ⟨a, b, d⟩ := hother ow' how' v' hv' hne
          exact w2st_shrink a (by rw [b]; exact Shrinks.rfl') (by rw [d]; exact Shrinks.rfl') hops h
    · -- the `Write2`s are sent
      have hid : m2.replicaId = rid32 i := by rw [hm2c]; exact hW.1.id i
      have hsent : ∀ j, sentR j [.send 0 (.write2 m2), .send 1 (.write2 m2), .send 2 (.write2 m2)]
          = [.write2 m2] := fun j => sentR_three' _ j
      have hu := (hW.1.ops ow how)
      refine ⟨msgs_step hs hm (fun R => ?_) (fun o ho => Or.inl (hops ▸ ho)) (fun j x hx => ?_),
        hrr, fun ow' how' v' hv' => ?_⟩
      · by_cases hR : R = i
        · subst hR; rw [hsti]; exact fun _ h => h
        · rw [hs.stj hR]; exact fun _ h => h
      · rw [hsent j, List.mem_singleton] at hx; subst hx
        refine ⟨i, hid, ?_, by rw [hm2b, ← howc]; exact hu.2⟩
        rw [hsti]; show _ ∈ (stR c i).used
        rw [hm2a, hm2b, ← howc, ← howq, ← howr]; exact hu.1
      rw [hops] at how'
      by_cases hne : ow' = ow
      · subst hne
        obtain ⟨sent, C, I, h1, h2, h3, h4, h5, h6, h7⟩ := hw ow' how' v' hv'
        obtain ⟨a, -, d, -, nr⟩ := h7 w (by rw [howr, hkey]; exact hk)
        have hsn : sent = none := a.2 hsw
        obtain ⟨rfl, rfl⟩ := h5 hsn
        subst hsn
        have hw2 : w2of ow' (.write2 m2) = true := by
          simp [w2of, hm2a, hm2b, howc, howq, hid, howr]
        have hc0 : ∀ q, (infR c q).countP (w2of ow') = 0 := by
          intro q; rw [List.countP_eq_zero]
          intro x hx hxw
          cases x with
          | write2 x => obtain ⟨g2, hg2⟩ := h4 q x hx hxw; cases hg2
          | _ => simp [w2of] at hxw
        refine ⟨some (l.length, wt), [], [], List.nodup_nil, ?_, fun q => ?_, fun q x hx hxw => ?_,
          (fun h => by cases h), fun g2 wt' hs' => ?_, ?_⟩
        · have h2' : (infR c ow'.r).filter (w2rOf ow') = [] := h2.eq_nil
          suffices (infR c' ow'.r).filter (w2rOf ow') = [] by rw [this]; exact List.Perm.nil
          rw [List.filter_eq_nil_iff]; intro x hx hxw
          rcases hs.mem hx with hx | hx
          · have := List.mem_filter.2 ⟨hx, hxw⟩; rw [h2'] at this; cases this
          · rw [hsent, List.mem_singleton] at hx; subst hx; cases hxw
        · rw [hs.inf q, List.countP_append, hsent]
          have : (if q = i then consume (Ev.msg (.write1Reply m)).recv (infR c q) else infR c q).countP
              (w2of ow') = 0 := by
            split
            · exact Nat.le_zero.1 (Nat.le_trans (consume_countP_le _ _ _) (Nat.le_of_eq (hc0 q)))
            · exact hc0 q
          rw [this]; simp [hw2]
        · rcases hs.mem hx with hx | hx
          · have := List.countP_pos_iff.2 ⟨_, hx, hxw⟩; rw [hc0 q] at this; cases this
          · rw [hsent, List.mem_singleton] at hx; cases hx
            exact ⟨l.length, by rw [hm2d]⟩
        · cases hs'; exact ⟨by simp, fun p hp => by cases hp⟩
        · intro w'' hw''
          rw [howr, hsti, hkey] at hw''
          change ((stR c i).wops.put _ w').get? _ = _ at hw''
          rw [AMap.get?_put, if_pos rfl] at hw''
          cases hw''
          refine ⟨by simp [hsw'], fun g2 wt' hs' => by cases hs'; exact hwt, by rw [ew4]; exact d, ?_,
            by rw [hnw2]; exact nr⟩
          intro e he k hk' e' he' hr' o' ho' hor hoc hoq g2 wt' hs'
          cases hs'
          rw [hops] at ho'; exact (mem_ops.1 ho').1
      · obtain ⟨a, b, d⟩ := hother ow' how' v' hv' hne
        refine w2rec_frame hs.tag_mono (hw ow' how' v' hv') ?_ ?_ ?_
          (fun sent C h => w2st_shrink a (by rw [b]; exact Shrinks.rfl')
            (by rw [d]; exact Shrinks.rfl') hops h)
        · refine hs.filter_eq _ _ (fun x hx => by cases hx; rfl) ?_
          rw [hsent]; rfl
        · intro q; refine hs.countP_le q _ ?_
          rw [hsent]
          have : w2of ow' (.write2 m2) = false := by
            cases h : w2of ow' (.write2 m2)
            · rfl
            · obtain ⟨x1, x2, x3⟩ := w2of_eq h
              rw [hid] at x3
              have hR := rid32_inj x3
              exact absurd (hr.uniq ow' how' ow how (by rw [← hR, howr])
                (by rw [← x2, hm2b, howc]) (by rw [← x1, hm2a, howq])) hne
          simp [this]
        · intro q x hx hxw
          rcases hs.mem hx with h | h
          · exact h
          · rw [hsent, List.mem_singleton] at h; cases h
            obtain ⟨x1, x2, x3⟩ := w2of_eq hxw
            rw [hid] at x3
            have hR := rid32_inj x3
            exact absurd (hr.uniq ow' how' ow how (by rw [← hR, howr])
              (by rw [← x2, hm2b, howc]) (by rw [← x1, hm2a, howq])) hne

end Perennial.gryff.pure
