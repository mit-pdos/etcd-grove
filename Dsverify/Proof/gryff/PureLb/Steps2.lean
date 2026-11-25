/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/Steps2.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b: `RInv`'s step for `Write2`s, `Write1Reply`s and `Write2Reply`s (the `Write2`
accounting).
-/
module

public import Dsverify.Proof.gryff.PureLb.Steps1

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

theorem w2of_eq {o : Op} {m : Write2ProxiedM} (h : w2of o (.write2 m) = true) :
    m.requestId = o.rid ∧ m.clientId = o.cid ∧ m.replicaId = rid32 o.r := by
  simpa [w2of, and_assoc] using h

theorem w2rOf_eq {o : Op} {m : Write2ReplyM} (h : w2rOf o (.write2Reply m) = true) :
    m.requestId = o.rid ∧ m.clientId = o.cid := by
  simpa [w2rOf] using h

/-- `Write2`s: the reply joins the write's in-flight replies, an applier's store below the tag. -/
theorem rinv_write2 {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {s' : RState} {o : List Out}
    {m : Write2ProxiedM} (hs : StepAt l c i (.msg (.write2 m)) c' s' o)
    (hi : RInv l c) : RInv (l ++ [(i, .msg (.write2 m))]) c' := by
  obtain ⟨hfr, hfw, htg, x, hx, rfl⟩ := stepWrite2_spec hs.ok
  have hmm : Msg.write2 m ∈ infR c i := hs.recv _ rfl
  obtain ⟨R, hR, hRu, hRc⟩ := hi.1 i _ hmm
  have hops := ops_snoc_none (l := l) (i := i) (e := .msg (.write2 m)) rfl
  obtain ⟨d, hd, rfl⟩ := sendTo_out hx
  rw [hR, dstOf_rid32] at hd; cases hd
  generalize hb : (stR c i).tag.lt m.vt.t = b at hs hx
  have hsent : ∀ j, sentR j [.send R (.write2Reply ⟨m.requestId, m.clientId,
      if b then 1 else 0⟩)] =
      if R = j then [.write2Reply ⟨m.requestId, m.clientId, if b then 1 else 0⟩] else [] :=
    fun j => sentR_single R j _
  have hS : ∀ R', SameRec (stR c R') (stR c' R') := by
    intro R'; rw [hs.st R']; split
    · subst_vars; exact SameRec.of hfr hfw
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hm, hr, hw⟩ := hi
  have hinf : ∀ j, infR c' j = (if j = i then (infR c j).erase (.write2 m) else infR c j) ++
      (if R = j then [.write2Reply ⟨m.requestId, m.clientId, if b then 1 else 0⟩] else []) := by
    intro j; rw [hs.inf j, hsent j]; rfl
  refine ⟨msgs_step hs hm (fun R' => by rw [(hS R').2.2.2.2.2]; exact fun _ h => h)
    (fun o ho => Or.inl (hops ▸ ho)) (fun j y hy => ?_),
    rrec_frame hr (fun R' => ⟨(hS R').1, (hS R').2.1, (hS R').2.2.1, (hS R').2.2.2.1⟩)
      (fun R' => by rw [(hS R').2.2.2.2.2]; exact fun _ h => h)
      (fun R' => by rw [(hS R').2.2.2.2.1]; exact ⟨Nat.le_refl _, (hr.maxN R').2.2⟩)
      (fun o ho => hops ▸ ho) (by rw [hops]; exact hr.uniq), fun ow how v hv => ?_⟩
  · rw [hsent j] at hy
    split at hy
    · rename_i hRj; subst hRj
      rw [List.mem_singleton.1 hy]
      exact ⟨by rw [(hS R).2.2.2.2.2]; exact hRu, hRc⟩
    · cases hy
  · rw [hops] at how
    have hg := ops_g_le how
    have hW2 : ∀ sent C, W2St l ow sent C (stR c ow.r) → W2St (l ++ [(i, .msg (.write2 m))]) ow
        sent C (stR c' ow.r) := fun sent C h =>
      w2st_congr ⟨(hS ow.r).1, (hS ow.r).2.1, (hS ow.r).2.2.1⟩ (fun o ho => Or.inl (hops ▸ ho))
        (fun k e he => (hr.ongoing _ k e he).2.2.2.1) h
    by_cases hwo : w2of ow (.write2 m) = true
    · obtain ⟨ea, eb, ed⟩ := w2of_eq hwo
      rw [hR] at ed
      have hRo := rid32_inj ed
      subst hRo
      obtain ⟨sent, C, I, h1, h2, h3, h4, h5, h6, h7⟩ := hw ow how v hv
      obtain ⟨g2, hg2⟩ := h4 i m hmm hwo
      have hpos : 0 < (infR c i).countP (w2of ow) := List.countP_pos_iff.2 ⟨_, hmm, hwo⟩
      have hiC : i ∉ (C ++ I).map Prod.fst := fun hc => by
        have := (h3 i).2 hc; omega
      have hcnt : (infR c' i).countP (w2of ow) = 0 := by
        rw [hinf i, if_pos rfl, List.countP_append]
        have e1 := countP_erase_true (w2of ow) hmm hwo
        have e2 : (if ow.r = i then [Msg.write2Reply ⟨m.requestId, m.clientId,
            if b then 1 else 0⟩] else []).countP (w2of ow) = 0 := by
          split <;> simp [w2of]
        have := (h3 i).1
        omega
      have hrp : Msg.write2Reply ⟨m.requestId, m.clientId, if b then 1 else 0⟩ = w2rep ow b := by
        unfold w2rep; rw [ea, eb]
      refine ⟨sent, C, I ++ [(i, b)], ?_, ?_, fun q => ?_, fun q y hy hyw => ?_, fun hn => ?_,
        fun g2' wt hs' => ?_, hW2 sent C h7⟩
      · rw [← List.append_assoc, List.map_append, List.nodup_append]
        refine ⟨h1, by simp, ?_⟩
        intro a ha b' hb'; simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb'
        rw [hb']; rintro rfl; exact hiC ha
      · rw [hinf ow.r, List.filter_append]
        have ef : (if ow.r = i then (infR c ow.r).erase (.write2 m) else infR c ow.r).filter
            (w2rOf ow) = (infR c ow.r).filter (w2rOf ow) := by
          split
          · exact filter_erase_of_false _ _ _ rfl
          · rfl
        rw [ef, if_pos rfl]
        simp only [List.filter_cons, List.filter_nil, List.map_append, List.map_cons, List.map_nil]
        rw [show w2rOf ow (.write2Reply ⟨m.requestId, m.clientId, if b then 1 else 0⟩) = true by
          rw [hrp]; simp [w2rOf, w2rep]]
        simp only [if_true, hrp]
        exact h2.append_right _
      · by_cases hq : q = i
        · subst hq; exact ⟨by omega, fun _ => hcnt⟩
        · have e : (infR c' q).countP (w2of ow) = (infR c q).countP (w2of ow) := by
            rw [hinf q, if_neg hq, List.countP_append]
            have : (if ow.r = q then [Msg.write2Reply ⟨m.requestId, m.clientId,
                if b then 1 else 0⟩] else []).countP (w2of ow) = 0 := by
              split <;> simp [w2of]
            omega
          rw [e]
          refine ⟨(h3 q).1, fun hq' => (h3 q).2 ?_⟩
          rw [← List.append_assoc, List.map_append, List.mem_append] at hq'
          rcases hq' with hq' | hq'
          · exact hq'
          · simp at hq'; exact absurd hq' hq
      · rcases hs.mem hy with hy | hy
        · exact h4 q y hy hyw
        · rw [hsent q] at hy; split at hy
          · simp at hy
          · cases hy
      · obtain ⟨-, hI⟩ := h5 hn
        rw [hn] at hg2; cases hg2
      · rw [hg2] at hs'; cases hs'
        obtain ⟨a1, a2⟩ := h6 g2 m.vt.t hg2
        refine ⟨by simp; omega, fun p hp => ?_⟩
        rw [← List.append_assoc, List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact ⟨fun hp2 => by rw [cutSt_snoc a1]; exact (a2 p hp).1 hp2,
            tagLe_trans (a2 p hp).2 (hs.tag_mono _)⟩
        · refine ⟨fun hp2 => ?_, by rw [hs.sti]; exact htg⟩
          rw [cutSt_snoc a1]
          simp only at hp2
          subst hp2
          exact tagLt_of_le_of_lt (hs.cut_le a1 _) ((Tag.lt_iff _ _).1 hb)
    · refine w2rec_frame hs.tag_mono (hw ow how v hv) ?_ ?_ ?_ (fun sent C h => hW2 sent C h)
      · rw [hinf ow.r, List.filter_append]
        have e2 : (if R = ow.r then [Msg.write2Reply ⟨m.requestId, m.clientId,
            if b then 1 else 0⟩] else []).filter (w2rOf ow) = [] := by
          split
          · rename_i hRo
            simp only [List.filter_cons, List.filter_nil]
            have : w2rOf ow (.write2Reply ⟨m.requestId, m.clientId, if b then 1 else 0⟩) =
                false := by
              cases h : w2rOf ow (.write2Reply ⟨m.requestId, m.clientId, if b then 1 else 0⟩)
              · rfl
              · obtain ⟨a, b'⟩ := w2rOf_eq h
                have : w2of ow (.write2 m) = true := by
                  simp only at a b'
                  simp [w2of, a, b', hR, hRo]
                rw [this] at hwo; exact absurd rfl hwo
            rw [this]; rfl
          · rfl
        rw [e2, List.append_nil]
        split
        · exact filter_erase_of_false _ _ _ rfl
        · rfl
      · intro q
        rw [hinf q, List.countP_append]
        have e2 : (if R = q then [Msg.write2Reply ⟨m.requestId, m.clientId,
            if b then 1 else 0⟩] else []).countP (w2of ow) = 0 := by
          split <;> simp [w2of]
        rw [e2, Nat.add_zero]
        split
        · exact countP_erase_le _ _ _
        · exact Nat.le_refl _
      · intro q y hy hyw
        rcases hs.mem hy with hy | hy
        · exact hy
        · rw [hsent q] at hy; split at hy
          · simp at hy
          · cases hy

end Perennial.gryff.pure
