/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/Frames.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b: frame lemmas for `RInv`'s parts, and the step for the events that keep the read
accounting (`rinv_other`).
-/
module

public import Dsverify.Proof.gryff.PureLb.Inv

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-- The fields `RInv` reads are equal. -/
def SameRec (s s' : RState) : Prop :=
  s'.rops = s.rops ∧ s'.wops = s.wops ∧ s'.ongoingReqs = s.ongoingReqs ∧ s'.maxN = s.maxN ∧
    s'.nReqs = s.nReqs ∧ s'.used = s.used

theorem SameRec.of {s s' : RState} (h1 : FR s s') (h2 : FW s s') : SameRec s s' :=
  ⟨h1.1, h2.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.2.2⟩

theorem rrec_frame {l l' : List Label} {c c' : Cfg gNet} (h : RRec l c)
    (hS : ∀ R, (stR c' R).rops = (stR c R).rops ∧ (stR c' R).wops = (stR c R).wops ∧
      (stR c' R).ongoingReqs = (stR c R).ongoingReqs ∧ (stR c' R).maxN = (stR c R).maxN)
    (hU : ∀ R, (stR c R).used ⊆ (stR c' R).used)
    (hN : ∀ R, (stR c R).nReqs ≤ (stR c' R).nReqs ∧ (stR c' R).nReqs ≤ 24)
    (hops : ∀ o ∈ ops l, o ∈ ops l')
    (huniq : ∀ o ∈ ops l', ∀ o' ∈ ops l', o.r = o'.r → o.cid = o'.cid → o.rid = o'.rid → o = o') :
    RRec l' c' := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := h
  refine ⟨fun R K rd hr => ?_, fun R K w hw => ?_, fun R => ?_, fun R k e he => ?_, fun R => ?_,
    huniq⟩
  all_goals (obtain ⟨e1, e2, e3, e4⟩ := hS R)
  · rw [e1] at hr; rw [e3]
    obtain ⟨a, b, ⟨o, ho, d⟩, f⟩ := h1 R K rd hr
    exact ⟨a, b, ⟨o, hops o ho, d⟩, f⟩
  · rw [e2] at hw; rw [e3]
    obtain ⟨a, ⟨o, ho, d⟩, f⟩ := h2 R K w hw
    exact ⟨a, ⟨o, hops o ho, d⟩, f⟩
  · rw [e2]; exact h3 R
  · rw [e3] at he; rw [e4]
    obtain ⟨a, b, d, f, g⟩ := h4 R k e he
    exact ⟨a, b, d, hU R f, g⟩
  · rw [e4]; have := h5 R; have := hN R; omega

theorem w2st_congr {l l' : List Label} {ow : Op} {sent : Option (Nat × model.Tag)}
    {C : List (Fin 3 × Bool)} {s s' : RState}
    (hS : s'.rops = s.rops ∧ s'.wops = s.wops ∧ s'.ongoingReqs = s.ongoingReqs)
    (hops : ∀ o ∈ ops l', o ∈ ops l ∨ (o.r = ow.r → (o.cid, o.rid) ∉ s.used))
    (hon : ∀ k e, s.ongoingReqs.get? k = some e → (e.clientId, e.requestId) ∈ s.used)
    (h : W2St l ow sent C s) : W2St l' ow sent C s' := by
  obtain ⟨e1, e2, e3⟩ := hS
  intro w hw
  rw [e2] at hw
  obtain ⟨a, b, d, f, nr⟩ := h w hw
  refine ⟨a, b, d, fun e he k hk e' he' hr o ho hor hoc hor' g2 wt hs => ?_, nr⟩
  rw [e3] at he he'; rw [e1] at hr
  rcases hops o ho with ho | ho
  · exact f e he k hk e' he' hr o ho hor hoc hor' g2 wt hs
  · exact absurd (by rw [hoc, hor']; exact hon k e' he') (ho hor)

theorem w2rec_frame {l : List Label} {x : Label} {c c' : Cfg gNet} {ow : Op}
    (hT : ∀ q, tagLe (stR c q).tag.toP (stR c' q).tag.toP) (hw : W2Rec l c ow)
    (hF : (infR c' ow.r).filter (w2rOf ow) = (infR c ow.r).filter (w2rOf ow))
    (hC : ∀ q, (infR c' q).countP (w2of ow) ≤ (infR c q).countP (w2of ow))
    (hM : ∀ q m, Msg.write2 m ∈ infR c' q → w2of ow (.write2 m) = true → Msg.write2 m ∈ infR c q)
    (hS : ∀ sent C, W2St l ow sent C (stR c ow.r) → W2St (l ++ [x]) ow sent C (stR c' ow.r)) :
    W2Rec (l ++ [x]) c' ow := by
  obtain ⟨sent, C, I, h1, h2, h3, h4, h5, h6, h7⟩ := hw
  refine ⟨sent, C, I, h1, hF ▸ h2, fun q => ?_, fun q m hm hw => h4 q m (hM q m hm hw) hw, h5,
    fun g2 wt hs => ?_, hS sent C h7⟩
  · have := hC q
    exact ⟨Nat.le_trans this (h3 q).1, fun hq => Nat.le_zero.1 ((h3 q).2 hq ▸ this)⟩
  · obtain ⟨a, b⟩ := h6 g2 wt hs
    refine ⟨by simp; omega, fun p hp => ⟨fun hp2 => ?_, tagLe_trans (b p hp).2 (hT _)⟩⟩
    rw [cutSt_snoc a]; exact (b p hp).1 hp2

theorem w2of_isR {o : Op} {m : Msg} (h : w2of o m = true) : isRMsg m = true := by
  cases m <;> simp_all [w2of, isRMsg]
theorem w2rOf_isR {o : Op} {m : Msg} (h : w2rOf o m = true) : isRMsg m = true := by
  cases m <;> simp_all [w2rOf, isRMsg]

theorem noR_sentTo {o : List Out} (h : NoR o) (j : Fin 3) :
    ∀ m ∈ sentR j o, isRMsg m = false := by
  intro m hm
  unfold sentR at hm
  obtain ⟨y, hy, hy'⟩ := List.mem_filterMap.1 hm
  have := h y hy
  cases y with
  | send d m' =>
    simp only at hy'
    split at hy'
    · cases hy'; exact this
    · cases hy'
  | ext _ => cases hy'

theorem filter_sentTo_nilR {o : List Out} (h : NoR o) (j : Fin 3) (f : Msg → Bool)
    (hf : ∀ m, f m = true → isRMsg m = true) : (sentR j o).filter f = [] := by
  rw [List.filter_eq_nil_iff]
  intro m hm hfm
  have := noR_sentTo h j m hm
  rw [hf m hfm] at this; cases this

theorem countP_sentTo_zeroR {o : List Out} (h : NoR o) (j : Fin 3) (f : Msg → Bool)
    (hf : ∀ m, f m = true → isRMsg m = true) : (sentR j o).countP f = 0 := by
  rw [List.countP_eq_length_filter, filter_sentTo_nilR h j f hf]; rfl

theorem mok_of_noRW {l : List Label} {c : Cfg gNet} {j : Fin 3} {m : Msg}
    (h1 : isRMsg m = false) (h2 : isWMsg m = false) : MOk l c j m := by
  cases m <;> simp_all [isRMsg, isWMsg, MOk]

/-- The ops of a step that is not a client request. -/
theorem ops_snoc_none {l : List Label} {i : Fin 3} {e : Ev} (h : e.clientReq = none) :
    ops (l ++ [(i, e)]) = ops l := by
  rw [ops_snoc, opAt_snoc_new, h]; simp

theorem StepAt.tag_mono {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c i e c' s' o) (q : Fin 3) :
    tagLe (stR c q).tag.toP (stR c' q).tag.toP := by
  rw [hs.st q]; split
  · subst_vars; exact step_tag_mono hs.ok
  · exact tagLe_refl _

/-- The `MOk` part, for a step whose new messages are accounted for. -/
theorem msgs_step {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c i e c' s' o) (hm : ∀ j m, m ∈ infR c j → MOk l c j m)
    (hU : ∀ R, (stR c R).used ⊆ (stR c' R).used)
    (hops : ∀ o ∈ ops (l ++ [(i, e)]), o ∈ ops l ∨ (o.cid, o.rid) ∉ (stR c o.r).used)
    (hnew : ∀ j m, m ∈ sentR j o → MOk (l ++ [(i, e)]) c' j m) :
    ∀ j m, m ∈ infR c' j → MOk (l ++ [(i, e)]) c' j m := by
  intro j m hmem
  rcases hs.mem hmem with h | h
  · exact mok_mono hU hops (fun o ho q => cutSt_snoc (ops_g_le ho) q) hs.tag_mono (hm j m h)
  · exact hnew j m h

def isW2 : Msg → Bool
  | .write2 _ => true
  | .write2Reply _ => true
  | _ => false

theorem w2of_isW2 {o : Op} {m : Msg} (h : w2of o m = true) : isW2 m = true := by
  cases m <;> simp_all [w2of, isW2]
theorem w2rOf_isW2 {o : Op} {m : Msg} (h : w2rOf o m = true) : isW2 m = true := by
  cases m <;> simp_all [w2rOf, isW2]

theorem filter_sentTo_nilW2 {o : List Out} {j : Fin 3} (h : ∀ m ∈ sentR j o, isW2 m = false)
    (f : Msg → Bool) (hf : ∀ m, f m = true → isW2 m = true) : (sentR j o).filter f = [] := by
  rw [List.filter_eq_nil_iff]
  intro m hm hfm
  have := h m hm
  rw [hf m hfm] at this; cases this

theorem countP_sentTo_zeroW2 {o : List Out} {j : Fin 3} (h : ∀ m ∈ sentR j o, isW2 m = false)
    (f : Msg → Bool) (hf : ∀ m, f m = true → isW2 m = true) : (sentR j o).countP f = 0 := by
  rw [List.countP_eq_length_filter, filter_sentTo_nilW2 h f hf]; rfl

theorem StepAt.sti {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c i e c' s' o) : stR c' i = s' := by
  rw [hs.st i, if_pos rfl]
theorem StepAt.stj {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c i e c' s' o) {j : Fin 3} (hj : j ≠ i) : stR c' j = stR c j := by
  rw [hs.st j, if_neg hj]

/-- Steps that keep the records (`SameRec`), the ops, and send no `Write2`-path message. -/
theorem rinv_frame {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c i e c' s' o) (hS0 : SameRec (stR c i) s')
    (hops : ops (l ++ [(i, e)]) = ops l)
    (hrecv : ∀ m, e.recv = some m → isW2 m = false)
    (hsent : ∀ j, ∀ m ∈ sentR j o, isW2 m = false)
    (hnew : ∀ j m, m ∈ sentR j o → MOk (l ++ [(i, e)]) c' j m)
    (hi : RInv l c) : RInv (l ++ [(i, e)]) c' := by
  have hS : ∀ R, SameRec (stR c R) (stR c' R) := by
    intro R; rw [hs.st R]; split
    · subst_vars; exact hS0
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hm, hr, hw⟩ := hi
  refine ⟨msgs_step hs hm (fun R => by rw [(hS R).2.2.2.2.2]; exact fun _ h => h)
    (fun o ho => Or.inl (hops ▸ ho)) hnew,
    rrec_frame hr (fun R => ⟨(hS R).1, (hS R).2.1, (hS R).2.2.1, (hS R).2.2.2.1⟩)
      (fun R => by rw [(hS R).2.2.2.2.2]; exact fun _ h => h)
      (fun R => by rw [(hS R).2.2.2.2.1]; exact ⟨Nat.le_refl _, (hr.maxN R).2.2⟩)
      (fun o ho => hops ▸ ho) (by rw [hops]; exact hr.uniq), fun ow hw' v hv => ?_⟩
  rw [hops] at hw'
  refine w2rec_frame hs.tag_mono (hw ow hw' v hv) ?_ ?_ ?_ ?_
  · exact hs.filter_eq _ _ (fun m hm => by
      cases h : w2rOf ow m
      · rfl
      · have := w2rOf_isW2 h; rw [hrecv m hm] at this; cases this)
      (filter_sentTo_nilW2 (hsent _) _ (fun _ => w2rOf_isW2))
  · exact fun q => hs.countP_le q _ (countP_sentTo_zeroW2 (hsent q) _ (fun _ => w2of_isW2))
  · intro q m hm hw2
    rcases hs.mem hm with h | h
    · exact h
    · have := hsent q _ h; simp [isW2] at this
  · intro sent C h
    exact w2st_congr ⟨(hS ow.r).1, (hS ow.r).2.1, (hS ow.r).2.2.1⟩
      (fun o ho => Or.inl (hops ▸ ho)) (fun k e he => (hr.ongoing _ k e he).2.2.2.1) h

theorem isW2_of_isR {m : Msg} (h : isRMsg m = false) : isW2 m = false := by
  cases m <;> simp_all [isRMsg, isW2]

/-- Events that keep the read accounting. -/
theorem rinv_other {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c i e c' s' o) (he : Ev.rspecial e = false)
    (hi : RInv l c) : RInv (l ++ [(i, e)]) c' := by
  have hwe : Ev.wspecial e = false := by
    cases e with
    | msg m => cases m <;> simp_all [Ev.rspecial, Ev.wspecial]
    | _ => simp_all [Ev.rspecial, Ev.wspecial]
  obtain ⟨hfw, hnw⟩ := step_fw_other hs.ok hwe
  obtain ⟨hfr, hnr⟩ := step_fr_other hs.ok he
  have hcr : e.clientReq = none := by
    cases e <;> simp_all [Ev.rspecial, Ev.clientReq]
  refine rinv_frame hs (SameRec.of hfr hfw) (ops_snoc_none hcr) (fun m hm => ?_)
    (fun j m hm => isW2_of_isR (noR_sentTo hnr j m hm))
    (fun j m hm' => mok_of_noRW (noR_sentTo hnr j m hm') (noW_sentTo hnw j m hm')) hi
  cases e with
  | msg m' =>
    cases hm
    cases m <;> simp_all [Ev.rspecial, isW2]
  | _ => cases hm

end Perennial.gryff.pure
