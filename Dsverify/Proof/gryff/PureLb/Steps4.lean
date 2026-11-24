/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/Steps4.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b: `RInv`'s step for `Write2Reply`s (the record counts an applier; at completion, the
short-circuit deletes reads' records and entries).
-/
module

public import Dsverify.Proof.gryff.PureLb.Steps3

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

theorem sentR_exts {o : List Out} (h : ∀ x ∈ o, ∃ e, x = .ext e) (j : Fin 3) : sentR j o = [] := by
  rw [sentR, List.filterMap_eq_nil_iff]
  intro x hx
  obtain ⟨e, rfl⟩ := h x hx; rfl

/-- The state after a completed write's short-circuit (or none). -/
theorem w2r_complete {s s1 : RState} {outs : List Out} {n : w32} {v : ValTag} {c : Prop}
    [Decidable c]
    (h : (c ∧ shortCircuit s n v false = some (s1, outs)) ∨ (s1 = s ∧ outs = [])) :
    ∃ X Y, s1 = { s with ongoingReqs := X, rops := Y } ∧ Shrinks s.ongoingReqs (X.del n) ∧
      Shrinks s.rops Y ∧
      (∀ k e, k ≠ n → s.ongoingReqs.get? k = some e → X.get? k = none →
        Y.get? (shiftInts e.requestId e.clientId) = none ∧
        (s.rops.get? (shiftInts e.requestId e.clientId)).isSome) ∧
      ∀ x ∈ outs, ∃ e, x = .ext e := by
  rcases h with ⟨-, h⟩ | ⟨h1, h2⟩
  · obtain ⟨X, Y, rfl, h1, h2, h3, h4⟩ := shortCircuit_spec h
    refine ⟨X, Y, rfl, h1, h2, h3, fun x hx => ?_⟩
    obtain ⟨cid, rid, rfl, -⟩ := h4 x hx
    exact ⟨_, rfl⟩
  · subst h2; rw [h1]
    exact ⟨s.ongoingReqs, s.rops, rfl, Shrinks.del _ _, Shrinks.rfl',
      (fun k e _ h h' => by rw [h] at h'; cases h'), (fun x hx => by cases hx)⟩

theorem sgt_applied (b : Bool) : sgt (if b then (1 : w32) else 0) 0 = b := by
  cases b <;> decide

/-- The replied write's accounting at a `Write2Reply` that sends nothing: the reply moves from the
in-flight list to the consumed one. -/
theorem w2r_own {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {s' : RState} {o : List Out}
    {m : Write2ReplyM} (hs : StepAt l c i (.msg (.write2Reply m)) c' s' o)
    (hno : ∀ j, sentR j o = []) {ow : Op} (hw : W2Rec l c ow) (howr : ow.r = i)
    (hwr : w2rOf ow (.write2Reply m) = true)
    (hst : ∀ sent C (p : Fin 3 × Bool), ((C ++ [p]).map Prod.fst).Nodup →
      m.applied = (if p.2 then 1 else 0) → W2St l ow sent C (stR c ow.r) →
      W2St (l ++ [(i, .msg (.write2Reply m))]) ow sent (C ++ [p]) (stR c' ow.r)) :
    W2Rec (l ++ [(i, .msg (.write2Reply m))]) c' ow := by
  have hmm : Msg.write2Reply m ∈ infR c i := hs.recv _ rfl
  obtain ⟨sent, C, I, h1, h2, h3, h4, h5, h6, h7⟩ := hw
  have hmf : Msg.write2Reply m ∈ (infR c ow.r).filter (w2rOf ow) :=
    List.mem_filter.2 ⟨howr ▸ hmm, hwr⟩
  obtain ⟨p, hpI, hpg⟩ := List.mem_map.1 (h2.mem_iff.1 hmf)
  have happ : m.applied = if p.2 then 1 else 0 := by
    unfold w2rep at hpg; cases hpg; rfl
  have hperm : (C ++ [p] ++ I.erase p).Perm (C ++ I) := by
    rw [List.append_assoc]
    exact List.Perm.append_left C (List.perm_cons_erase hpI).symm
  have hsentN : sent ≠ none := fun hn => by
    obtain ⟨-, hI⟩ := h5 hn; rw [hI] at hpI; cases hpI
  have hn3 : ((C ++ [p] ++ I.erase p).map Prod.fst).Nodup := (hperm.map Prod.fst).nodup_iff.2 h1
  rw [List.map_append] at hn3
  refine ⟨sent, C ++ [p], I.erase p, (hperm.map Prod.fst).nodup_iff.2 h1, ?_, fun q => ?_,
    fun q x hx hxw => ?_, fun hn => absurd hn hsentN, fun g2 wt hs2 => ?_,
    hst sent C p (hn3.sublist (List.sublist_append_left _ _)) happ h7⟩
  · rw [hs.inf ow.r, if_pos howr, hno, List.append_nil]
    show ((infR c ow.r).erase (.write2Reply m)).filter (w2rOf ow) |>.Perm _
    have p1 : ((infR c ow.r).filter (w2rOf ow)).Perm (.write2Reply m ::
        ((infR c ow.r).erase (.write2Reply m)).filter (w2rOf ow)) := by
      have := (List.perm_cons_erase (howr ▸ hmm)).filter (w2rOf ow)
      rwa [List.filter_cons_of_pos hwr] at this
    have p2 := h2.trans (perm_map_erase (f := fun p => w2rep ow p.2) hpI)
    rw [hpg] at p2
    exact (p1.symm.trans p2).cons_inv
  · have hle := hs.countP_le q (w2of ow) (by rw [hno]; rfl)
    exact ⟨Nat.le_trans hle (h3 q).1,
      fun hq => Nat.le_zero.1 (((h3 q).2 ((hperm.map Prod.fst).subset hq)) ▸ hle)⟩
  · rcases hs.mem hx with h | h
    · exact h4 q x h hxw
    · rw [hno] at h; cases h
  · obtain ⟨a, b⟩ := h6 g2 wt hs2
    exact ⟨by simp; omega, fun q hq => ⟨fun hq2 => by
      rw [cutSt_snoc a]; exact (b q (hperm.subset hq)).1 hq2,
      tagLe_trans (b q (hperm.subset hq)).2 (hs.tag_mono _)⟩⟩

/-- Another write's accounting at a `Write2Reply` that sends nothing. -/
theorem w2r_other {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {s' : RState} {o : List Out}
    {m : Write2ReplyM} (hs : StepAt l c i (.msg (.write2Reply m)) c' s' o)
    (hno : ∀ j, sentR j o = []) {ow : Op} (hw : W2Rec l c ow)
    (hnot : ow.r = i → w2rOf ow (.write2Reply m) = false)
    (hst : ∀ sent C, W2St l ow sent C (stR c ow.r) →
      W2St (l ++ [(i, .msg (.write2Reply m))]) ow sent C (stR c' ow.r)) :
    W2Rec (l ++ [(i, .msg (.write2Reply m))]) c' ow := by
  refine w2rec_frame hs.tag_mono hw ?_ (fun q => hs.countP_le q _ (by rw [hno]; rfl)) ?_ hst
  · rw [hs.inf ow.r, hno, List.append_nil]
    split
    · rename_i hR
      exact filter_erase_of_false _ _ _ (hnot hR)
    · rfl
  · intro q x hx hxw
    rcases hs.mem hx with h | h
    · exact h
    · rw [hno] at h; cases h

/-- `Write2Reply`s. -/
theorem rinv_write2Reply {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {s' : RState}
    {o : List Out} {m : Write2ReplyM} (hs : StepAt l c i (.msg (.write2Reply m)) c' s' o)
    (hW : WInv l c) (hi : RInv l c) : RInv (l ++ [(i, .msg (.write2Reply m))]) c' := by
  have hops := ops_snoc_none (l := l) (i := i) (e := .msg (.write2Reply m)) rfl
  have hmm : Msg.write2Reply m ∈ infR c i := hs.recv _ rfl
  cases hk : (stR c i).wops.get? (shiftInts m.requestId m.clientId) with
  | none =>
    obtain ⟨rfl, rfl⟩ := stepWrite2Reply_none hk hs.ok
    obtain ⟨hm, hr, hw⟩ := hi
    obtain ⟨hmu, hmc⟩ := hm i _ hmm
    have hS : ∀ R, SameRec (stR c R) (stR c' R) := by
      intro R; rw [hs.st R]; split
      · subst_vars; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨msgs_step hs hm (fun R => by rw [(hS R).2.2.2.2.2]; exact fun _ h => h)
      (fun o ho => Or.inl (hops ▸ ho)) (fun j x hx => by cases hx),
      rrec_frame hr (fun R => ⟨(hS R).1, (hS R).2.1, (hS R).2.2.1, (hS R).2.2.2.1⟩)
        (fun R => by rw [(hS R).2.2.2.2.2]; exact fun _ h => h)
        (fun R => by rw [(hS R).2.2.2.2.1]; exact ⟨Nat.le_refl _, (hr.maxN R).2.2⟩)
        (fun o ho => hops ▸ ho) (by rw [hops]; exact hr.uniq), fun ow how v hv => ?_⟩
    rw [hops] at how
    have hst : ∀ sent C, W2St l ow sent C (stR c ow.r) →
        W2St (l ++ [(i, .msg (.write2Reply m))]) ow sent C (stR c' ow.r) := fun sent C h =>
      w2st_congr ⟨(hS ow.r).1, (hS ow.r).2.1, (hS ow.r).2.2.1⟩ (fun o ho => Or.inl (hops ▸ ho))
        (fun k e he => (hr.ongoing _ k e he).2.2.2.1) h
    by_cases hA : ow.r = i ∧ w2rOf ow (.write2Reply m) = true
    · refine w2r_own hs (fun _ => rfl) (hw ow how v hv) hA.1 hA.2 (fun sent C p _ _ _ => ?_)
      intro w' hw'
      obtain ⟨a, b⟩ := w2rOf_eq hA.2
      have : ow.key = shiftInts m.requestId m.clientId := by unfold Op.key; rw [a, b]
      rw [this, hA.1, hs.sti, hk] at hw'; cases hw'
    · refine w2r_other hs (fun _ => rfl) (hw ow how v hv) (fun hR => ?_) hst
      cases h : w2rOf ow (.write2Reply m)
      · rfl
      · exact absurd ⟨hR, h⟩ hA
  | some w =>
    obtain ⟨hm, hr, hw⟩ := hi
    obtain ⟨hmu, hmc⟩ := hm i _ hmm
    have hmem := AMap.mem_of_get? hk
    obtain ⟨hK, ⟨ow, how, howr, ⟨v0, howv⟩, howc, howq⟩, -, hwv, hwa⟩ := hr.wops i _ w hmem
    have hkey : ow.key = shiftInts m.requestId m.clientId := by
      unfold Op.key; rw [howc, howq, hK]
    obtain ⟨ea, eb⟩ := shiftInts_inj hmc (hW.1.ops ow how).2 (by rw [← hkey]; rfl)
    have hwr : w2rOf ow (.write2Reply m) = true := by simp [w2rOf, ea, eb]
    have hsti := hs.sti
    -- other writes
    have hotherK : ∀ ow' ∈ ops l, ∀ v', ow'.inp = .write v' → ow' ≠ ow → ow'.r = i →
        ow'.key ≠ shiftInts m.requestId m.clientId := by
      intro ow' how' v' hv' hne hR hk'
      rw [← hkey] at hk'
      obtain ⟨a, b⟩ := shiftInts_inj (hW.1.ops ow' how').2 (hW.1.ops ow how).2 hk'
      exact hne (hr.uniq ow' how' ow how (by rw [hR, howr]) b a)
    have hnot : ∀ ow' ∈ ops l, ∀ v', ow'.inp = .write v' → ow' ≠ ow → ow'.r = i →
        w2rOf ow' (.write2Reply m) = false := by
      intro ow' how' v' hv' hne hR
      cases h : w2rOf ow' (.write2Reply m)
      · rfl
      · obtain ⟨a, b⟩ := w2rOf_eq h
        exact absurd (hr.uniq ow' how' ow how (by rw [hR, howr]) (by rw [← b, eb])
          (by rw [← a, ea])) hne
    rcases stepWrite2Reply_some hk hs.ok with ⟨rfl, rfl⟩ | ⟨wt, s1, outs, hwt, hsc, rfl, rfl⟩
    · -- the record counts the reply
      have hrr := rrec_wput (l' := l ++ [(i, .msg (.write2Reply m))]) hr hops hsti
        (fun j hj => hs.stj hj) hmem rfl rfl rfl hwv hwa
      refine ⟨msgs_step hs hm (fun R => ?_) (fun o ho => Or.inl (hops ▸ ho))
        (fun j x hx => by cases hx), hrr, fun ow' how' v' hv' => ?_⟩
      · by_cases hR : R = i
        · subst hR; rw [hsti]; exact fun _ h => h
        · rw [hs.stj hR]; exact fun _ h => h
      rw [hops] at how'
      by_cases hne : ow' = ow
      · subst hne
        refine w2r_own hs (fun _ => rfl) (hw ow' how' v' hv') howr hwr (fun sent C p hn3 happ h7 => ?_)
        intro w'' hw''
        rw [howr, hsti, hkey] at hw''
        change ((stR c i).wops.put _ _).get? _ = _ at hw''
        rw [AMap.get?_put, if_pos rfl] at hw''
        cases hw''
        obtain ⟨a, b, d, f, nr⟩ := h7 w (by rw [howr, hkey]; exact hk)
        have hClen : C.length ≤ 3 := by
          have := nodup_fin3_len hn3; simp at this; omega
        have hCl2 : C.length ≤ 2 := by
          have := nodup_fin3_len hn3; simp at this; omega
        have hCf : (C.filter (·.2)).length ≤ 3 := Nat.le_trans (List.length_filter_le _ _) hClen
        refine ⟨a, b, ?_, ?_, ?_⟩
        · show sint.Z (if sgt m.applied 0 = true then _ else _) = _
          rw [happ, sgt_applied, List.filter_append]
          cases hp2 : p.2
          · simp [hp2, d]
          · simp only [if_true]
            rw [Z_succ64 d (by omega) (by omega)]
            simp [hp2]
        · intro e he k hk' e' he' hr' o' ho' hor hoc hoq g2 wt' hs'
          rw [howr, hsti] at he he' hr'
          rw [hops] at ho'
          rw [howr] at *
          exact f e he k hk' e' he' hr' o' ho' (by rw [hor, howr]) hoc hoq g2 wt' hs'
        · show sint.Z (w.numWrite2Replies + 1) = _
          rw [Z_succ64 nr (by omega) (by omega)]
          simp
      · refine w2r_other hs (fun _ => rfl) (hw ow' how' v' hv') (hnot ow' how' v' hv' hne)
          (fun sent' C' h => ?_)
        by_cases hR : ow'.r = i
        · refine w2st_shrink ?_ (by rw [hR, hsti]; exact Shrinks.rfl')
            (by rw [hR, hsti]; exact Shrinks.rfl') hops h
          rw [hR, hsti]
          show ((stR c i).wops.put _ _).get? _ = _
          rw [AMap.get?_put, if_neg (hotherK ow' how' v' hv' hne hR)]
        · rw [hs.stj hR]; exact w2st_shrink rfl Shrinks.rfl' Shrinks.rfl' hops h
    · -- completion: the record and its entry are deleted (after the short-circuit)
      obtain ⟨X, Y, rfl, hX, hY, hXY, hext⟩ := w2r_complete hsc
      have hno : ∀ j, sentR j (outs ++ [.ext (.writeReply w.clientId w.requestId 1)]) = [] := by
        intro j; apply sentR_exts
        intro x hx; rcases List.mem_append.1 hx with hx | hx
        · exact hext x hx
        · rw [List.mem_singleton.1 hx]; exact ⟨_, rfl⟩
      have hstR : ∀ R, R ≠ i → stR c' R = stR c R := fun R hR => hs.stj hR
      refine ⟨msgs_step hs hm (fun R => ?_) (fun o ho => Or.inl (hops ▸ ho))
        (fun j x hx => by rw [hno] at hx; cases hx), ?_, fun ow' how' v' hv' => ?_⟩
      · by_cases hR : R = i
        · subst hR; rw [hsti]; exact fun _ h => h
        · rw [hs.stj hR]; exact fun _ h => h
      · obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hr
        -- no read record nor other write record shares the write's entry
        have hrd_ne : ∀ K' rd', (stR c i).rops.get? K' = some rd' → rd'.n ≠ w.n := by
          intro K' rd' h' hn
          obtain ⟨-, -, ⟨orr, horr, horr1, horr2, horr3, horr4⟩, ⟨e1, he1, he1a, he1b⟩⟩ :=
            g1 i K' rd' h'
          obtain ⟨-, -, ⟨e0, he0, he0a, he0b⟩, -⟩ := g2 i _ w hmem
          rw [hn, he0] at he1; cases he1
          have := g6 ow how orr horr (by rw [howr, horr1]) (by rw [howc, horr3, ← he1b, he0b])
            (by rw [howq, horr4, ← he1a, he0a])
          subst this; rw [howv] at horr2; cases horr2
        refine ⟨fun R K' rd hr' => ?_, fun R K' w'' hw' => ?_, fun R => ?_, fun R k e he => ?_,
          fun R => ?_, by rw [hops]; exact g6⟩
        · by_cases hR : R = i
          · subst hR; rw [hsti] at hr' ⊢
            change Y.get? K' = some rd at hr'
            have hr0 := hY _ _ hr'
            obtain ⟨a, b, ⟨o', ho', d⟩, ⟨e, he, hea, heb⟩⟩ := g1 R K' rd hr0
            refine ⟨a, b, ⟨o', hops ▸ ho', d⟩, ?_⟩
            show ∃ e, (X.del w.n).get? rd.n = some e ∧ e.requestId = rd.requestId ∧
              e.clientId = rd.clientId
            rw [AMap.get?_del, if_neg (hrd_ne K' rd hr0)]
            cases hx : X.get? rd.n with
            | none =>
              have := (hXY _ _ (hrd_ne K' rd hr0) he hx).1
              rw [hea, heb, ← b, hr'] at this; cases this
            | some e'' =>
              have := hX _ _ (by rw [AMap.get?_del, if_neg (hrd_ne K' rd hr0)]; exact hx)
              rw [he] at this; cases this
              exact ⟨e, rfl, hea, heb⟩
          · rw [hs.stj hR] at hr' ⊢
            obtain ⟨a, b, ⟨o', ho', d⟩, f⟩ := g1 R K' rd hr'
            exact ⟨a, b, ⟨o', hops ▸ ho', d⟩, f⟩
        · by_cases hR : R = i
          · subst hR; rw [hsti] at hw' ⊢
            change (K', w'') ∈ (stR c R).wops.del _ at hw'
            obtain ⟨hw0, hK'⟩ := List.mem_filter.1 hw'
            simp only [bne_iff_ne, ne_eq] at hK'
            obtain ⟨a, ⟨o', ho', d⟩, ⟨e, he, hea, heb⟩, f⟩ := g2 R K' w'' hw0
            refine ⟨a, ⟨o', hops ▸ ho', d⟩, ?_, f⟩
            show ∃ e, (X.del w.n).get? w''.n = some e ∧ e.requestId = w''.requestId ∧
              e.clientId = w''.clientId
            obtain ⟨-, -, ⟨e0, he0, he0a, he0b⟩, -⟩ := g2 R _ w hmem
            have hne : w''.n ≠ w.n := by
              intro hn; rw [hn, he0] at he; cases he
              exact hK' (by rw [a, ← hea, ← heb, he0a, he0b, hK])
            rw [AMap.get?_del, if_neg hne]
            cases hx : X.get? w''.n with
            | none =>
              have := (hXY _ _ hne he hx).2
              cases hrd : (stR c R).rops.get? (shiftInts e.requestId e.clientId) with
              | none => rw [hrd] at this; cases this
              | some rd =>
                obtain ⟨-, b, ⟨orr, horr, horr1, horr2, horr3, horr4⟩, -⟩ := g1 R _ rd hrd
                obtain ⟨o1, o2⟩ := shiftInts_inj (g4 R _ e he).2.2.2.2 (by
                  rw [← horr3]; exact (hW.1.ops orr horr).2) b
                obtain ⟨how''r, ⟨v'', how''v⟩, how''c, how''q⟩ := d
                have := g6 o' ho' orr horr (by rw [how''r, horr1])
                  (by rw [how''c, horr3, ← o2, heb]) (by rw [how''q, horr4, ← o1, hea])
                rw [this] at how''v; rw [how''v] at horr2; cases horr2
            | some e'' =>
              have := hX _ _ (by rw [AMap.get?_del, if_neg hne]; exact hx)
              rw [he] at this; cases this
              exact ⟨e, rfl, hea, heb⟩
          · rw [hs.stj hR] at hw' ⊢
            obtain ⟨a, ⟨o', ho', d⟩, f⟩ := g2 R K' w'' hw'
            exact ⟨a, ⟨o', hops ▸ ho', d⟩, f⟩
        · by_cases hR : R = i
          · subst hR; rw [hsti]; exact AMap.sorted_del (g3 R) _
          · rw [hs.stj hR]; exact g3 R
        · by_cases hR : R = i
          · subst hR; rw [hsti] at he ⊢
            change (X.del w.n).get? k = some e at he
            exact g4 R k e (hX _ _ he)
          · rw [hs.stj hR] at he ⊢; exact g4 R k e he
        · by_cases hR : R = i
          · subst hR; rw [hsti]; exact g5 R
          · rw [hs.stj hR]; exact g5 R
      · rw [hops] at how'
        by_cases hne : ow' = ow
        · subst hne
          refine w2r_own hs hno (hw ow' how' v' hv') howr hwr (fun sent C p _ _ _ => ?_)
          intro w'' hw''
          rw [howr, hsti, hkey] at hw''
          change ((stR c i).wops.del _).get? _ = _ at hw''
          rw [AMap.get?_del, if_pos rfl] at hw''
          cases hw''
        · refine w2r_other hs hno (hw ow' how' v' hv') (hnot ow' how' v' hv' hne)
            (fun sent' C' h => ?_)
          by_cases hR : ow'.r = i
          · refine w2st_shrink ?_ ?_ ?_ hops h
            · rw [hR, hsti]
              show ((stR c i).wops.del _).get? _ = _
              rw [AMap.get?_del, if_neg (hotherK ow' how' v' hv' hne hR)]
            · rw [hR, hsti]; exact hX
            · rw [hR, hsti]; exact hY
          · rw [hs.stj hR]; exact w2st_shrink rfl Shrinks.rfl' Shrinks.rfl' hops h

end Perennial.gryff.pure
