/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/Steps1.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b: `RInv`'s step for client RMWs, `Write1`s, `Read1`s and `Read1Reply`s.
-/
module

public import Dsverify.Proof.gryff.PureLb.Frames

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

theorem dstOf_eq {q : w32} {d : Fin 3} (h : dstOf q = some d) : q = rid32 d := by
  unfold dstOf at h
  split at h
  · rename_i hq
    cases h
    have h3 : sint.Z q = 0 ∨ sint.Z q = 1 ∨ sint.Z q = 2 := by omega
    rcases h3 with h0 | h0 | h0
    · have : q = 0 := BitVec.eq_of_toInt_eq (by simpa [sint.Z] using h0)
      subst this; simp [rid32, sint.Z]
    · have : q = 1 := BitVec.eq_of_toInt_eq (by simpa [sint.Z] using h0)
      subst this; simp [rid32, sint.Z]
    · have : q = 2 := BitVec.eq_of_toInt_eq (by simpa [sint.Z] using h0)
      subst this; simp [rid32, sint.Z]
  · cases h

theorem sentR_sendTo {q : w32} {msg : Msg} {x : Out} (hx : sendTo q msg = some x) {j : Fin 3}
    {m : Msg} (h : m ∈ sentR j [x]) : m = msg ∧ q = rid32 j := by
  obtain ⟨d, hd, rfl⟩ := sendTo_out hx
  rw [sentR_single] at h
  split at h
  · rename_i hdj; subst hdj; exact ⟨List.mem_singleton.1 h, dstOf_eq hd⟩
  · cases h

theorem sentR_ext (x : Ext) (j : Fin 3) : sentR j [.ext x] = [] := rfl

theorem AMap.mem_of_get? {n : Nat} {V : Type} {m : model.AMap n V} {K : BitVec n} {v : V}
    (h : m.get? K = some v) : (K, v) ∈ m := by
  induction m with
  | nil => cases h
  | cons a t ih =>
    obtain ⟨k0, v0⟩ := a
    simp only [model.AMap.get?, List.lookup] at h ih
    split at h
    · rename_i hk; cases h; simp at hk; subst hk; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- The store now is at least the store at an earlier cut. -/
theorem StepAt.cut_le {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c i e c' s' o) {g : Nat} (hg : g ≤ l.length) (q : Fin 3) :
    tagLe (cutSt l g q).tag.toP (stR c q).tag.toP := by
  have e1 := cut_tag_mono hs.run q hg
  rwa [cutSt_len hs.run] at e1

/-- A new operation (fresh key at its coordinator). -/
theorem new_op_facts {l : List Label} {c : Cfg gNet} {onew : Op} {l' : List Label}
    (hops : ops l' = ops l ++ [onew]) (hW : WInv l c)
    (hfresh : (onew.cid, onew.rid) ∉ (stR c onew.r).used)
    (hu : ∀ o ∈ ops l, ∀ o' ∈ ops l, o.r = o'.r → o.cid = o'.cid → o.rid = o'.rid → o = o') :
    (∀ o ∈ ops l', o ∈ ops l ∨ (o.cid, o.rid) ∉ (stR c o.r).used) ∧
    (∀ o ∈ ops l', ∀ o' ∈ ops l', o.r = o'.r → o.cid = o'.cid → o.rid = o'.rid → o = o') := by
  refine ⟨fun o ho => ?_, fun o ho o' ho' h1 h2 h3 => ?_⟩
  · rw [hops, List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · exact Or.inl ho
    · exact Or.inr hfresh
  · rw [hops, List.mem_append, List.mem_singleton] at ho ho'
    rcases ho with ho | rfl <;> rcases ho' with ho' | rfl
    · exact hu o ho o' ho' h1 h2 h3
    · have := (hW.1.ops o ho).1; rw [h1, h2, h3] at this; exact absurd this hfresh
    · have := (hW.1.ops o' ho').1; rw [← h1, ← h2, ← h3] at this; exact absurd this hfresh
    · rfl

/-- Client RMWs. -/
theorem rinv_rmw {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {s' : RState} {o : List Out}
    {rid cid : w32} {k : w64} {d : Dep} {a b : w64}
    (hs : StepAt l c i (.rmw rid cid k d a b) c' s' o) (hW : WInv l c)
    (hi : RInv l c) : RInv (l ++ [(i, .rmw rid cid k d a b)]) c' := by
  obtain ⟨hu0, hcid, hu, hid, hwops, hnow⟩ := stepClientRMW_spec hs.ok
  obtain ⟨e1, e2, e3, e4, e5, hnor⟩ := stepClientRMW_fr hs.ok
  have hops := ops_snoc_req (l := l) (i := i) (e := .rmw rid cid k d a b) rfl
  have hmono := hs.used_of_cons hu
  obtain ⟨hm, hr, hw⟩ := hi
  obtain ⟨hops', huniq⟩ := new_op_facts hops hW hu0 hr.uniq
  have hS : ∀ R, (stR c' R).rops = (stR c R).rops ∧ (stR c' R).wops = (stR c R).wops ∧
      (stR c' R).ongoingReqs = (stR c R).ongoingReqs ∧ (stR c' R).maxN = (stR c R).maxN := by
    intro R; rw [hs.st R]; split
    · subst_vars; exact ⟨e1, hwops, e2, e3⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨msgs_step hs hm hmono hops' (fun j m hm' => mok_of_noRW (noR_sentTo hnor j m hm')
      (noW_sentTo hnow j m hm')),
    rrec_frame hr hS hmono (fun R => ?_) (fun o ho => by rw [hops]; exact List.mem_append_left _ ho)
      huniq, fun ow hw' v hv => ?_⟩
  · rw [hs.st R]; split
    · subst_vars; rw [e4]; omega
    · exact ⟨Nat.le_refl _, (hr.maxN R).2.2⟩
  · rw [hops, List.mem_append, List.mem_singleton] at hw'
    rcases hw' with hw' | rfl
    · refine w2rec_frame hs.tag_mono (hw ow hw' v hv) ?_ ?_ ?_ ?_
      · exact hs.filter_eq _ _ (fun m hm => by cases hm)
          (filter_sentTo_nilR hnor _ _ (fun _ => w2rOf_isR))
      · exact fun q => hs.countP_le q _ (countP_sentTo_zeroR hnor q _ (fun _ => w2of_isR))
      · intro q m hm hw2
        rcases hs.mem hm with h | h
        · exact h
        · cases noR_sentTo hnor q _ h
      · intro sent C h
        refine w2st_congr ⟨(hS ow.r).1, (hS ow.r).2.1, (hS ow.r).2.2.1⟩ (fun o ho => ?_)
          (fun k e he => (hr.ongoing _ k e he).2.2.2.1) h
        rcases hops' o ho with h' | h'
        · exact Or.inl h'
        · exact Or.inr (fun hr' => hr' ▸ h')
    · cases hv

/-- `Write1`s. -/
theorem rinv_write1 {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {s' : RState} {o : List Out}
    {m : Write1ProxiedM} (hs : StepAt l c i (.msg (.write1 m)) c' s' o)
    (hi : RInv l c) : RInv (l ++ [(i, .msg (.write1 m))]) c' := by
  obtain ⟨hfw, hout⟩ := stepWrite1_spec hs.ok
  have hfr := stepWrite1_fr hs.ok
  have hsent : ∀ j, ∀ x ∈ sentR j o, x = .write1Reply ⟨m.requestId, m.clientId, ⟨-1, s'.tag⟩⟩ := by
    intro j x hx
    rcases hout with rfl | ⟨y, hy, rfl⟩
    · cases hx
    · exact (sentR_sendTo hy hx).1
  refine rinv_frame hs (SameRec.of hfr hfw) (ops_snoc_none rfl) (fun x hx => by cases hx; rfl)
    (fun j x hx => by rw [hsent j x hx]; rfl) (fun j x hx => ?_) hi
  rw [hsent j x hx]; rfl

/-- `Read1`s: the reply carries the replier's store, after the overwrite with the coordinator's. -/
theorem rinv_read1 {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {s' : RState} {o : List Out}
    {m : Read1ProxiedM} (hs : StepAt l c i (.msg (.read1 m)) c' s' o)
    (hi : RInv l c) : RInv (l ++ [(i, .msg (.read1 m))]) c' := by
  obtain ⟨hfr, hfw, htag, x, hx, rfl⟩ := stepRead1_spec hs.ok
  have hmono := step_tag_mono hs.ok
  have hmm : Msg.read1 m ∈ infR c i := hs.recv _ rfl
  obtain ⟨R, hR, hiR, hRu, hRc, hRt⟩ := hi.1 i _ hmm
  have hops := ops_snoc_none (l := l) (i := i) (e := .msg (.read1 m)) rfl
  refine rinv_frame hs (SameRec.of hfr hfw) hops (fun x hx => by cases hx; rfl)
    (fun j y hy => by rw [(sentR_sendTo hx hy).1]; rfl) (fun j y hy => ?_) hi
  obtain ⟨rfl, hj⟩ := sentR_sendTo hx hy
  rw [hR] at hj; have hjR := rid32_inj hj; subst hjR
  have hsR : stR c' R = stR c R := hs.stj (Ne.symm hiR)
  refine ⟨by rw [hsR]; exact hRu, hRc, fun o ho hor hoc hoq => ⟨i, hiR, ?_, ?_⟩,
    i, hiR, by rw [hs.sti]; exact tagLe_refl _⟩
  · rw [hops] at ho
    rw [cutSt_snoc (ops_g_le ho)]
    exact tagLe_trans (hs.cut_le (ops_g_le ho) i) hmono
  · rw [hops] at ho
    rw [cutSt_snoc (ops_g_le ho)]
    exact tagLe_trans (hRt o ho hor hoc hoq) htag

/-- Shrinking the ongoing requests and read records keeps a write's record facts. -/
theorem w2st_shrink {l l' : List Label} {ow : Op} {sent : Option (Nat × model.Tag)}
    {C : List (Fin 3 × Bool)} {s s' : RState} (hW : s'.wops.get? ow.key = s.wops.get? ow.key)
    (hO : Shrinks s.ongoingReqs s'.ongoingReqs) (hR : Shrinks s.rops s'.rops)
    (hops : ops l' = ops l) (h : W2St l ow sent C s) : W2St l' ow sent C s' := by
  intro w hw
  rw [hW] at hw
  obtain ⟨a, b, d, f, nr⟩ := h w hw
  refine ⟨a, b, d, fun e he k hk e' he' hr o ho => ?_, nr⟩
  rw [hops] at ho
  refine f e (hO _ _ he) k hk e' (hO _ _ he') ?_ o ho
  cases h' : s'.rops.get? (shiftInts e'.requestId e'.clientId) with
  | none => rw [h'] at hr; cases hr
  | some v => rw [hR _ _ h']; rfl

/-- `Read1Reply`s: a fresh record is completed and deleted. -/
theorem rinv_read1Reply {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {s' : RState}
    {o : List Out} {m : Read1ReplyM} (hs : StepAt l c i (.msg (.read1Reply m)) c' s' o)
    (hi : RInv l c) : RInv (l ++ [(i, .msg (.read1Reply m))]) c' := by
  have hops := ops_snoc_none (l := l) (i := i) (e := .msg (.read1Reply m)) rfl
  cases hk : (stR c i).rops.get? (shiftInts m.requestId m.clientId) with
  | none =>
    obtain ⟨rfl, rfl⟩ := stepRead1Reply_none hk hs.ok
    exact rinv_frame hs ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ hops (fun x hx => by cases hx; rfl)
      (fun j x hx => by cases hx) (fun j x hx => by cases hx) hi
  | some rd =>
    obtain ⟨hm, hr, hw⟩ := hi
    obtain ⟨hfresh, hK, ⟨orr, horr, horr1, horr2, horr3, horr4⟩, ⟨e0, he0, he1, he2⟩⟩ :=
      hr.rops i _ rd hk
    rw [hfresh] at hk
    obtain ⟨rfl, rfl⟩ := stepRead1Reply_fresh hk hs.ok
    have hsti := hs.sti
    have hfrw := overwrite_fr (stR c i) m.vt.v m.vt.t
    have hfww := overwrite_fw (stR c i) m.vt.v m.vt.t
    have hU : ∀ R, (stR c R).used ⊆ (stR c' R).used := by
      intro R; by_cases hR : R = i
      · subst hR; rw [hsti]; show _ ⊆ (RState.overwrite _ _ _).used; rw [hfww.2.2]
        exact fun _ h => h
      · rw [hs.stj hR]; exact fun _ h => h
    -- the deleted entry is the record's own
    have hne_r : ∀ K' rd', (stR c i).rops.get? K' = some rd' → K' ≠ shiftInts m.requestId m.clientId →
        rd'.n ≠ rd.n := by
      intro K' rd' h' hK' hn
      obtain ⟨-, hK'', -, ⟨e1, he1', he1a, he1b⟩⟩ := hr.rops i K' rd' h'
      rw [hn, he0] at he1'; cases he1'
      apply hK'; rw [hK'', hK, ← he1a, ← he1b, he1, he2]
    have hne_w : ∀ K' w, (K', w) ∈ (stR c i).wops → w.n ≠ rd.n := by
      intro K' w h' hn
      obtain ⟨-, ⟨ow, how, how1, ⟨v, how2⟩, how3, how4⟩, ⟨e1, he1', he1a, he1b⟩, -⟩ :=
        hr.wops i K' w h'
      rw [hn, he0] at he1'; cases he1'
      have := hr.uniq ow how orr horr (by rw [how1, horr1])
        (by rw [how3, horr3, ← he1b, he2]) (by rw [how4, horr4, ← he1a, he1])
      subst this; rw [how2] at horr2; cases horr2
    refine ⟨msgs_step hs hm hU (fun o ho => Or.inl (hops ▸ ho)) (fun j x hx => by cases hx), ?_,
      fun ow how v hv => ?_⟩
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
      refine ⟨fun R K' rd' hr' => ?_, fun R K' w hw' => ?_, fun R => ?_, fun R k e he => ?_,
        fun R => ?_, by rw [hops]; exact h6⟩
      · by_cases hR : R = i
        · subst hR
          rw [hsti] at hr' ⊢
          simp only [AMap.get?_del] at hr' ⊢
          split at hr'
          · cases hr'
          · rename_i hK'
            obtain ⟨a, b, ⟨o', ho', d⟩, f⟩ := h1 R K' rd' hr'
            refine ⟨a, b, ⟨o', hops ▸ ho', d⟩, ?_⟩
            rw [if_neg (hne_r K' rd' hr' hK')]; exact f
        · rw [hs.stj hR] at hr' ⊢
          obtain ⟨a, b, ⟨o', ho', d⟩, f⟩ := h1 R K' rd' hr'
          exact ⟨a, b, ⟨o', hops ▸ ho', d⟩, f⟩
      · by_cases hR : R = i
        · subst hR
          rw [hsti] at hw' ⊢
          change (K', w) ∈ (RState.overwrite _ _ _).wops at hw'
          rw [hfww.1] at hw'
          obtain ⟨a, ⟨o', ho', d⟩, f, g⟩ := h2 R K' w hw'
          refine ⟨a, ⟨o', hops ▸ ho', d⟩, ?_, g⟩
          simp only [AMap.get?_del]
          rw [if_neg (hne_w K' w hw')]; exact f
        · rw [hs.stj hR] at hw' ⊢
          obtain ⟨a, ⟨o', ho', d⟩, f⟩ := h2 R K' w hw'
          exact ⟨a, ⟨o', hops ▸ ho', d⟩, f⟩
      · by_cases hR : R = i
        · subst hR; rw [hsti]; change KSorted (RState.overwrite _ _ _).wops; rw [hfww.1]
          exact h3 R
        · rw [hs.stj hR]; exact h3 R
      · by_cases hR : R = i
        · subst hR
          rw [hsti] at he ⊢
          simp only [AMap.get?_del] at he
          split at he
          · cases he
          · change _ ∧ _ ≤ sint.Z (RState.overwrite _ _ _).maxN ∧
              (∀ x ∈ e.shortReads, _ ≤ sint.Z (RState.overwrite _ _ _).maxN) ∧
              _ ∈ (RState.overwrite _ _ _).used ∧ _
            rw [hfrw.2.2.1, hfww.2.2]; exact h4 R k e he
        · rw [hs.stj hR] at he ⊢; exact h4 R k e he
      · by_cases hR : R = i
        · subst hR; rw [hsti]
          change 0 ≤ sint.Z (RState.overwrite _ _ _).maxN ∧
            sint.Z (RState.overwrite _ _ _).maxN ≤ (RState.overwrite _ _ _).nReqs ∧
            (RState.overwrite _ _ _).nReqs ≤ 24
          rw [hfrw.2.2.1, hfrw.2.2.2]; exact h5 R
        · rw [hs.stj hR]; exact h5 R
    · rw [hops] at how
      refine w2rec_frame hs.tag_mono (hw ow how v hv) ?_ ?_ ?_ ?_
      · exact hs.filter_eq _ _ (fun x hx => by cases hx; rfl) rfl
      · exact fun q => hs.countP_le q _ rfl
      · intro q x hx hw2
        rcases hs.mem hx with h | h
        · exact h
        · cases h
      · intro sent C h
        by_cases hR : ow.r = i
        · rw [hR] at h ⊢; rw [hsti]
          refine w2st_shrink ?_ (Shrinks.del _ _) (Shrinks.del _ _) hops h
          change (RState.overwrite _ _ _).wops.get? _ = _; rw [hfww.1]
        · rw [hs.stj hR]
          exact w2st_shrink rfl Shrinks.rfl' Shrinks.rfl' hops h

end Perennial.gryff.pure
