/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureT/StepCoord.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A2 (totality): the coordinator's steps (client reads and writes, `Read1Reply`,
`Write1Reply`, `Write2Reply`; `Read2`, `Read2Reply` are never sent).
-/
module

public import Dsverify.Proof.gryff.PureT.Coord

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.tot

open model kahn

theorem SI.ofCoord {P : Fin 3 → Nat} {r : Fin 3} {s s' : RState} (h : SI P r s) (he : EqE s s')
    (hn : s'.nReqs ≤ 24) (hb : s'.maxN.toNat + (s.crt (rid32 r)).toNat ≤ s'.nReqs)
    (hu : ∀ p ∈ s'.used, 0 ≤ p.1.toInt)
    (hc : CoordOK s'.maxN s'.ongoingReqs s'.wops s'.rops s'.used) : SI P r s' := by
  have hcrt : ∀ q, s'.crt q = s.crt q := fun q => by simp [RState.crt, he.crtInstance]
  have hcut : ∀ q, s'.cut q = s.cut q := fun q => by simp [RState.cut, he.committedUpTo]
  have hconf : ∀ q, s'.confAt q = s.confAt q := fun q => by simp [RState.confAt, he.conf]
  exact {
    id := he.id.trans h.id
    lcrt := he.crtInstance ▸ h.lcrt
    lcut := he.committedUpTo ▸ h.lcut
    lconf := he.conf ▸ h.lconf
    nreq := hn
    budget := by rw [hcrt]; exact hb
    crt := fun q => by rw [hcrt]; exact h.crt q
    inst := fun q i c hc => h.inst q i c (by rw [← he.inst]; exact hc)
    own := fun i hi => by rw [he.inst]; exact h.own i (by rw [← hcrt]; exact hi)
    ownOK := fun i c hc => h.ownOK i c (by rw [← he.inst]; exact hc)
    cut := fun q => by rw [hcut]; exact h.cut q
    conf := fun q hi hh => by rw [he.inst]; exact h.conf q hi (by rw [← hconf]; exact hh)
    propQ := by rw [he.proposeQ]; exact h.propQ
    usedPos := hu
    coord := hc }

theorem Mono.ofCoord {r : Fin 3} {s s' : RState} (he : EqE s s') (hu : ∀ p ∈ s.used, p ∈ s'.used)
    (hw : ∀ rid cid, (cid, rid) ∈ s.used →
      (∀ w, s.wops.get? (shiftInts rid cid) = some w → w.writeTag ≠ none) →
      (∀ w, s'.wops.get? (shiftInts rid cid) = some w → w.writeTag ≠ none)) : Mono r s s' where
  id := he.id
  used := hu
  crt := by simp [RState.crt, he.crtInstance]
  inst := fun q i c h => ⟨c, by rw [he.inst]; exact h, fun x => x, fun x => ⟨x, rfl⟩⟩
  wt := hw

section ow
variable (s : RState) (v : w64) (t : model.Tag)
@[simp] theorem ow_id : (s.overwrite v t).id = s.id := by unfold RState.overwrite; split <;> rfl
@[simp] theorem ow_inst : (s.overwrite v t).inst = s.inst := by unfold RState.overwrite; split <;> rfl
@[simp] theorem ow_crtInstance : (s.overwrite v t).crtInstance = s.crtInstance := by
  unfold RState.overwrite; split <;> rfl
@[simp] theorem ow_committedUpTo : (s.overwrite v t).committedUpTo = s.committedUpTo := by
  unfold RState.overwrite; split <;> rfl
@[simp] theorem ow_conf : (s.overwrite v t).conf = s.conf := by unfold RState.overwrite; split <;> rfl
@[simp] theorem ow_proposeQ : (s.overwrite v t).proposeQ = s.proposeQ := by
  unfold RState.overwrite; split <;> rfl
@[simp] theorem ow_maxN : (s.overwrite v t).maxN = s.maxN := by unfold RState.overwrite; split <;> rfl
@[simp] theorem ow_rops : (s.overwrite v t).rops = s.rops := by unfold RState.overwrite; split <;> rfl
@[simp] theorem ow_wops : (s.overwrite v t).wops = s.wops := by unfold RState.overwrite; split <;> rfl
@[simp] theorem ow_ongoingReqs : (s.overwrite v t).ongoingReqs = s.ongoingReqs := by
  unfold RState.overwrite; split <;> rfl
@[simp] theorem ow_nReqs : (s.overwrite v t).nReqs = s.nReqs := by unfold RState.overwrite; split <;> rfl
@[simp] theorem ow_used : (s.overwrite v t).used = s.used := by unfold RState.overwrite; split <;> rfl
@[simp] theorem ow_maxSeqK0 : (s.overwrite v t).maxSeqK0 = s.maxSeqK0 := by
  unfold RState.overwrite; split <;> rfl
@[simp] theorem ow_prevValTag : (s.overwrite v t).prevValTag = s.prevValTag := by
  unfold RState.overwrite; split <;> rfl
end ow

theorem stepRead1Reply_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (m : Read1ReplyM) :
    Ok (stepRead1Reply (st r) m) (Post st r) := by
  cases hr : (st r).rops.get? (shiftInts m.requestId m.clientId) with
  | none =>
    tsimp [stepRead1Reply, hr]
    exact Ok.ret (Post.of_eq (hI r) (EqE.refl _) (EqG.refl _) (by simp))
  | some read =>
    obtain ⟨⟨h1, h2, h3, h4⟩, -, -⟩ := (hI r).coord.rops _ _ hr
    have e1 : sge ((1 : w64) + 1) (NHALF + 1) = true := by decide
    tsimp [stepRead1Reply, hr, h1, h2, h3, h4, e1]
    simp only [ow_id, ow_inst, ow_crtInstance, ow_committedUpTo, ow_conf, ow_proposeQ, ow_maxN,
      ow_rops, ow_wops, ow_ongoingReqs, ow_nReqs, ow_used]
    refine Ok.ret (Post.of (Mono.ofCoord ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun p h => h)
      (fun _ _ _ h => h)) rfl
      (SI.ofCoord (hI r) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (hI r).nreq (hI r).budget (hI r).usedPos
        ((hI r).coord.delRead hr)) (by simp [OutOk]))

end Perennial.gryff.pure.tot

namespace Perennial.gryff.pure.tot
open model kahn

theorem mapM_sendTo_all (msg : Msg) :
    ([0, 1, 2] : List w32).mapM (fun q => sendTo q msg) =
      some [Out.send 0 msg, Out.send 1 msg, Out.send 2 msg] := by
  rfl

theorem wt_put {ws : AMap 64 WriteOp} {K id : w64} {w0 w' : WriteOp}
    (h : ∀ w, ws.get? K = some w → w.writeTag ≠ none) (h0 : ws.get? id = some w0)
    (h' : w'.writeTag = w0.writeTag ∨ w'.writeTag ≠ none) :
    ∀ w, (ws.put id w').get? K = some w → w.writeTag ≠ none := by
  intro w hw
  rw [AMap.get?_put] at hw
  split at hw
  · next heq =>
    cases hw; subst heq
    rcases h' with h' | h'
    · rw [h']; exact h w0 h0
    · exact h'
  · exact h w hw

theorem wt_del {ws : AMap 64 WriteOp} {K id : w64}
    (h : ∀ w, ws.get? K = some w → w.writeTag ≠ none) :
    ∀ w, (ws.del id).get? K = some w → w.writeTag ≠ none := by
  intro w hw
  rw [AMap.get?_del] at hw
  split at hw
  · cases hw
  · exact h w hw

theorem w1post_core (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) {id : w64} {w w' : WriteOp}
    (hw : (st r).wops.get? id = some w) (hn : w'.n = w.n) (hv : w'.maxValTag.v = -1)
    (ha : w'.numWrite1Applies = 0) (hr : w'.requestId = w.requestId) (hc : w'.clientId = w.clientId)
    (hwt : w'.writeTag = w.writeTag ∨ w'.writeTag ≠ none) :
    Mono r (st r) { st r with wops := (st r).wops.put id w' } ∧
      SI (Pf st) r { st r with wops := (st r).wops.put id w' } :=
  ⟨Mono.ofCoord ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ h => h)
      (fun _ _ _ h => wt_put h hw hwt),
    SI.ofCoord (hI r) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (hI r).nreq (hI r).budget (hI r).usedPos
      ((hI r).coord.updWrite hw hn hv ha hr hc)⟩

theorem w1postA (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) {id : w64} {w w' : WriteOp}
    (hw : (st r).wops.get? id = some w) (hn : w'.n = w.n) (hv : w'.maxValTag.v = -1)
    (ha : w'.numWrite1Applies = 0) (hr : w'.requestId = w.requestId) (hc : w'.clientId = w.clientId)
    (hwt : w'.writeTag = w.writeTag ∨ w'.writeTag ≠ none) :
    Post st r ({ st r with wops := (st r).wops.put id w' }, []) := by
  obtain ⟨h1, h2⟩ := w1post_core st r hI hw hn hv ha hr hc hwt
  exact Post.of h1 rfl h2 (by simp)

theorem w1postB (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) {id : w64} {w w' : WriteOp}
    (hw : (st r).wops.get? id = some w) (hn : w'.n = w.n) (hv : w'.maxValTag.v = -1)
    (ha : w'.numWrite1Applies = 0) (hr : w'.requestId = w.requestId) (hc : w'.clientId = w.clientId)
    (hwt : w'.writeTag ≠ none) (M : Write2ProxiedM) (hMk : M.k = 0) (hMr : M.replicaId = (st r).id)
    (hMrid : M.requestId = w.requestId) (hMcid : M.clientId = w.clientId) :
    Post st r ({ st r with wops := (st r).wops.put id w' },
      [Out.send 0 (.write2 M), Out.send 1 (.write2 M), Out.send 2 (.write2 M)]) := by
  obtain ⟨h1, h2⟩ := w1post_core st r hI hw hn hv ha hr hc (Or.inr hwt)
  refine Post.of h1 rfl h2 ?_
  obtain ⟨-, -, -, -, hk, hu⟩ := (hI r).coord.wops _ (AMap.mem_of_get? hw)
  simp only at hk hu
  have hwk : WK (upd st r { st r with wops := (st r).wops.put id w' }) r M.requestId M.clientId := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hMcid]; exact (hI r).usedPos _ hu
    · rw [upd_self, hMcid, hMrid]; exact hu
    · rw [upd_self, hMcid, hMrid, ← hk]
      intro w'' hw''
      rw [AMap.get?_put] at hw''; simp at hw''; subst hw''; exact hwt
  have : OutOk (Pf st) (upd st r { st r with wops := (st r).wops.put id w' }) (.send 0 (.write2 M)) ∧
      OutOk (Pf st) (upd st r { st r with wops := (st r).wops.put id w' }) (.send 1 (.write2 M)) ∧
      OutOk (Pf st) (upd st r { st r with wops := (st r).wops.put id w' }) (.send 2 (.write2 M)) := by
    simp only [OutOk, MInv]
    exact ⟨⟨hMk, r, by rw [hMr, (hI r).id], hwk⟩, ⟨hMk, r, by rw [hMr, (hI r).id], hwk⟩,
      ⟨hMk, r, by rw [hMr, (hI r).id], hwk⟩⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact this.1
  · exact this.2.1
  · exact this.2.2

theorem stepWrite1Reply_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (m : Write1ReplyM)
    (hm : MInv (Pf st) st r (.write1Reply m)) : Ok (stepWrite1Reply (st r) m) (Post st r) := by
  simp only [MInv] at hm
  cases hw : (st r).wops.get? (shiftInts m.requestId m.clientId) with
  | none =>
    tsimp [stepWrite1Reply, hw]
    exact Ok.ret (Post.of_eq (hI r) (EqE.refl _) (EqG.refl _) (by simp))
  | some w =>
    obtain ⟨-, -, h1, h2, -, -⟩ := (hI r).coord.wops _ (AMap.mem_of_get? hw)
    simp only at h1 h2
    obtain ⟨wr, wc, wn, wv, wd, ⟨mv, mt⟩, wa, w1, w2a, w2r, ws2, wt⟩ := w
    simp only at h1 h2; subst h1 h2
    have e1 : sge (-1 : w64) 0 = false := by decide
    have e2 : sge (0 : w64) (NHALF + 1) = false := by decide
    have e3 : ((-1 : w64) == -1) = true := by decide
    tsimp [stepWrite1Reply, hw, hm, e1, e2, e3, mapM_sendTo_all]
    repeat' split
    all_goals
      apply Ok.ret
      first
        | apply w1postA st r hI hw
        | apply w1postB st r hI hw
      all_goals first | rfl | exact hm | simp | exact Or.inl rfl

theorem CoordOK.delReadKey {mx : w32} {oq : AMap 32 OngoingOp} {ws : AMap 64 WriteOp}
    {rs : AMap 64 ReadOp} {u : List (w32 × w32)} (h : CoordOK mx oq ws rs u) {k : w32} {o : OngoingOp}
    (hk : oq.get? k = some o) (hr : o.isRead = true) (id : w64) :
    CoordOK mx (oq.del k) ws (rs.del id) u where
  oreq := by
    intro k' o' hk'
    rw [AMap.get?_del] at hk'; split at hk'; · cases hk'
    obtain ⟨a, b⟩ := h.oreq k' o' hk'
    refine ⟨a, fun k'' hk'' => ⟨(b k'' hk'').1, fun o'' ho'' => ?_⟩⟩
    rw [AMap.get?_del] at ho''; split at ho''; · cases ho''
    exact (b k'' hk'').2 o'' ho''
  wops := by
    intro e he
    obtain ⟨a, ⟨o', ho', hro⟩, c⟩ := h.wops e he
    refine ⟨a, ⟨o', ?_, hro⟩, c⟩
    rw [AMap.get?_del]; split
    · next heq => rw [heq, hk] at ho'; cases ho'; rw [hr] at hro; cases hro
    · exact ho'
  wopsN := h.wopsN
  rops := by
    intro id' rop' hr'
    rw [AMap.get?_del] at hr'; split at hr'; · cases hr'
    obtain ⟨a, b, c⟩ := h.rops id' rop' hr'
    refine ⟨a, b, fun o'' ho => ?_⟩
    rw [AMap.get?_del] at ho; split at ho; · cases ho
    exact c o'' ho

/-- An `OngoingReqs` entry rewritten with the same kind and a permutation of its reads. -/
theorem CoordOK.putSame {mx : w32} {oq : AMap 32 OngoingOp} {ws : AMap 64 WriteOp}
    {rs : AMap 64 ReadOp} {u : List (w32 × w32)} (h : CoordOK mx oq ws rs u) {n : w32}
    {op op' : OngoingOp} (hn : oq.get? n = some op) (hr : op'.isRead = op.isRead)
    (hs : ∀ x, x ∈ op'.shortReads → x ∈ op.shortReads) : CoordOK mx (oq.put n op') ws rs u := by
  have hget : ∀ k o, (oq.put n op').get? k = some o → ∃ o0, oq.get? k = some o0 ∧
      o.isRead = o0.isRead ∧ ∀ x ∈ o.shortReads, x ∈ o0.shortReads := by
    intro k o hk
    rw [AMap.get?_put] at hk
    split at hk
    · next he => cases hk; subst he; exact ⟨op, hn, hr, hs⟩
    · exact ⟨o, hk, rfl, fun x hx => hx⟩
  refine ⟨?_, ?_, h.wopsN, ?_⟩
  · intro k o hk
    obtain ⟨o0, h0, -, h2⟩ := hget k o hk
    obtain ⟨a, b⟩ := h.oreq k o0 h0
    refine ⟨a, fun k' hk' => ⟨(b k' (h2 k' hk')).1, fun o' ho' => ?_⟩⟩
    obtain ⟨o1, h1, e1, -⟩ := hget k' o' ho'
    rw [e1]; exact (b k' (h2 k' hk')).2 o1 h1
  · intro e he
    obtain ⟨a, ⟨o, ho, hro⟩, c⟩ := h.wops e he
    refine ⟨a, ?_, c⟩
    rw [AMap.get?_put]
    split
    · next heq => subst heq; rw [hn] at ho; cases ho; exact ⟨op', rfl, by rw [hr, hro]⟩
    · exact ⟨o, ho, hro⟩
  · intro id rop hrop
    obtain ⟨a, b, c⟩ := h.rops id rop hrop
    refine ⟨a, b, fun o ho => ?_⟩
    obtain ⟨o0, h0, e0, -⟩ := hget _ o ho
    rw [e0]; exact c o0 h0

theorem shortCircuit_ok (s : RState) (hc : CoordOK s.maxN s.ongoingReqs s.wops s.rops s.used)
    (n : w32) (op : OngoingOp) (hn : s.ongoingReqs.get? n = some op) (hw : op.isRead = false)
    (value : ValTag) (fo : Bool) :
    OkO (shortCircuit s n value fo) (fun res => ∃ oq rs,
      res.1 = { s with ongoingReqs := oq, rops := rs } ∧ CoordOK s.maxN oq s.wops rs s.used ∧
      ∀ x ∈ res.2, ∃ e, x = Out.ext e) := by
  have hsr := (hc.oreq n op hn).2
  have hnn : n ∉ op.shortReads := by
    intro h; have := (hsr n h).2 op hn; rw [hw] at this; cases this
  have hc0 := hc.putSame (op' := { op with shortReads := op.shortReads.mergeSort (fun a b => sle a b) })
    hn rfl (fun x hx => (List.mem_mergeSort).1 hx)
  simp only [shortCircuit, hn]
  apply OkO.bind
  refine (OkO.loop _ _ _ (fun _ b => ∃ oq rs, b.1 = { s with ongoingReqs := oq, rops := rs } ∧
      CoordOK s.maxN oq s.wops rs s.used ∧
      (∀ k o, oq.get? k = some o → k ≠ n → s.ongoingReqs.get? k = some o) ∧
      (∃ o, oq.get? n = some o) ∧ ∀ x ∈ b.2, ∃ e, x = Out.ext e) ?_ ?_).mono ?_
  · refine ⟨_, s.rops, rfl, hc0, ?_, ?_, by simp⟩
    · intro k o hk hkn
      rw [AMap.get?_put, if_neg hkn] at hk; exact hk
    · exact ⟨{ op with shortReads := op.shortReads.mergeSort (fun a b => sle a b) },
        by rw [AMap.get?_put]; simp⟩
  · intro pre k post b hl hb
    obtain ⟨oq, rs, hb1, hb2, hb3, hbn, hb4⟩ := hb
    have hk : k ∈ op.shortReads := by
      have : k ∈ op.shortReads.mergeSort (fun a b => sle a b) := by rw [hl]; simp
      exact (List.mem_mergeSort).1 this
    have hkn : k ≠ n := fun h => hnn (h ▸ hk)
    obtain ⟨b1, b2⟩ := b
    simp only at hb1 hb4
    subst hb1
    split
    · exact OkO.some (fun _ => ⟨oq, rs, rfl, hb2, hb3, hbn, hb4⟩)
    · split
      · next o ho =>
        split
        · refine OkO.some ⟨oq.del k, rs.del (shiftInts o.requestId o.clientId), rfl,
            hb2.delReadKey ho ((hsr k hk).2 o (hb3 k o ho hkn)) _, ?_, ?_, ?_⟩
          · intro k' o' h' hk'n; rw [AMap.get?_del] at h'; split at h'; · cases h'
            exact hb3 k' o' h' hk'n
          · obtain ⟨o1, h1⟩ := hbn; exact ⟨o1, by rw [AMap.get?_del, if_neg (Ne.symm hkn)]; exact h1⟩
          · intro x hx; simp at hx; rcases hx with hx | hx
            · exact hb4 x hx
            · exact ⟨_, hx⟩
        · exact OkO.some ⟨oq, rs, rfl, hb2, hb3, hbn, hb4⟩
      · exact OkO.some ⟨oq, rs, rfl, hb2, hb3, hbn, hb4⟩
  · intro b hb
    obtain ⟨pre, ⟨oq, rs, h1, h2, -, ⟨o1, hon⟩, h4⟩, -⟩ := hb
    split
    · rw [h1]; simp only [hon]; exact OkO.some ⟨oq, rs, rfl, h2, h4⟩
    · rw [h1]; exact OkO.some ⟨oq, rs, rfl, h2, h4⟩

theorem stepWrite2Reply_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (m : Write2ReplyM)
    (hm : MInv (Pf st) st r (.write2Reply m)) : Ok (stepWrite2Reply (st r) m) (Post st r) := by
  simp only [MInv] at hm
  cases hw : (st r).wops.get? (shiftInts m.requestId m.clientId) with
  | none =>
    tsimp [stepWrite2Reply, hw]
    exact Ok.ret (Post.of_eq (hI r) (EqE.refl _) (EqG.refl _) (by simp))
  | some w =>
    have hwt := hm.2.2 w hw
    obtain ⟨wt, hwt'⟩ := Option.ne_none_iff_exists'.1 hwt
    obtain ⟨-, ⟨op, hop, hopw⟩, -⟩ := (hI r).coord.wops _ (AMap.mem_of_get? hw)
    simp only at hop
    have hsc := shortCircuit_ok (st r) (hI r).coord w.n op hop hopw ⟨w.writeValue, wt⟩ false
    have hP : ∀ (b : Bool), OkO (if b = true then shortCircuit (st r) w.n ⟨w.writeValue, wt⟩ false
        else some (st r, [])) (fun res => ∃ oq rs,
          res.1 = { st r with ongoingReqs := oq, rops := rs } ∧
          CoordOK (st r).maxN oq (st r).wops rs (st r).used ∧ ∀ x ∈ res.2, ∃ e, x = Out.ext e) := by
      intro b; split
      · exact hsc
      · exact OkO.some ⟨_, _, rfl, (hI r).coord, by simp⟩
    have hA : ∀ (b : Bool) s1 outs, (if b = true then shortCircuit (st r) w.n ⟨w.writeValue, wt⟩ false
        else some (st r, [])) = some (s1, outs) →
        Post st r ({ s1 with
            wops := s1.wops.del (shiftInts m.requestId m.clientId),
            ongoingReqs := s1.ongoingReqs.del w.n },
          outs ++ [Out.ext (Ext.writeReply w.clientId w.requestId 1)]) := by
      intro b s1 outs heq
      obtain ⟨res, h1, oq, rs, h2, h3, h4⟩ := hP b
      rw [heq] at h1; cases h1
      simp only at h2 h4; subst h2
      refine Post.of (Mono.ofCoord ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ h => h)
        (fun _ _ _ h => wt_del h)) rfl
        (SI.ofCoord (hI r) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (hI r).nreq (hI r).budget (hI r).usedPos
          (h3.delWrite hw)) ?_
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · obtain ⟨e, rfl⟩ := h4 x hx; trivial
      · subst hx; trivial
    have hB : ∀ (b : Bool), (∀ s1 outs, (if b = true then shortCircuit (st r) w.n ⟨w.writeValue, wt⟩ false
        else some (st r, [])) = some (s1, outs) → False) → False := by
      intro b h
      obtain ⟨⟨s1, outs⟩, h1, -⟩ := hP b
      exact h s1 outs h1
    unfold stepWrite2Reply
    simp only [hw, hwt']
    split
    · split
      · next s1 outs heq => exact Ok.ret (hA _ s1 outs heq)
      · exact absurd (hB _ (by assumption)) id
    · apply Ok.ret
      have hw1 := (hI r).coord.wops _ (AMap.mem_of_get? hw)
      simp only at hw1
      apply w1postA st r hI hw
      all_goals first | rfl | exact hw1.2.2.1 | exact hw1.2.2.2.1 | exact Or.inl rfl | exact Or.inr (by simp)

theorem budget_lt {P : Fin 3 → Nat} {r : Fin 3} {s : RState} (h : SI P r s) (hn : s.nReqs < 24) :
    s.maxN.toNat < 24 := by
  have := h.budget; omega

theorem mx_succ {mx : w32} (h : mx.toNat < 24) : (mx + 1).toNat = mx.toNat + 1 := by
  rw [BitVec.toNat_add]; simp; omega

theorem wt_newKey {s : RState} (hpos : ∀ p ∈ s.used, 0 ≤ p.1.toInt) {rid cid : w32}
    (hc : 0 ≤ cid.toInt) (hu : (cid, rid) ∉ s.used) (w : WriteOp) :
    ∀ rid0 cid0, (cid0, rid0) ∈ s.used →
      (∀ w', s.wops.get? (shiftInts rid0 cid0) = some w' → w'.writeTag ≠ none) →
      (∀ w', (s.wops.put (shiftInts rid cid) w).get? (shiftInts rid0 cid0) = some w' →
        w'.writeTag ≠ none) := by
  intro rid0 cid0 h0 hw w' hw'
  rw [AMap.get?_put] at hw'
  split at hw'
  · next heq =>
    obtain ⟨e1, e2⟩ := shiftInts_inj (hpos _ h0) hc heq
    subst e1 e2; exact absurd h0 hu
  · exact hw w' hw'

theorem stepClientWrite_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (rid cid : w32)
    (k v : w64) (d : Dep) (hk : k = 0) (hd : slt d.key 0 = true) (hc : sge cid 0 = true)
    (hn : (st r).nReqs < 24) (hu : (cid, rid) ∉ (st r).used) :
    Ok (stepClientWrite (st r) rid cid k v d) (Post st r) := by
  have hc' : 0 ≤ cid.toInt := by simpa [sge, sle] using hc
  have hmx := budget_lt (hI r) hn
  have hn' : ¬ (24 ≤ (st r).nReqs) := by omega
  tsimp [stepClientWrite, hk, hd, hc, hn', hu, mapM_sendTo_all, beq_self_eq_true, Bool.and_self,
    decide_false, decide_true]
  apply Ok.ret
  refine Post.of (Mono.ofCoord ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ h => List.mem_cons_of_mem _ h)
    (wt_newKey (hI r).usedPos hc' hu _)) rfl
    (SI.ofCoord (hI r) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (by simp; omega)
      (by have := (hI r).budget; simp only; rw [mx_succ hmx]; omega)
      (by intro p hp; simp at hp; rcases hp with rfl | hp
          · exact hc'
          · exact (hI r).usedPos _ hp)
      ((hI r).coord.newWrite hmx rid cid _ rfl rfl rfl rfl rfl)) ?_
  have hm : ∀ (j : Fin 3) (M : Write1ProxiedM) (P : Fin 3 → Nat) (st' : Fin 3 → RState),
      M.k = 0 → slt M.d.key 0 = true → M.forceWrite = 1 → M.replicaId = (st r).id →
      OutOk P st' (Out.send j (Msg.write1 M)) := by
    intro j M P st' h1 h2 h3 h4; simp only [OutOk, MInv]; exact ⟨h1, h2, h3, r, h4.trans (hI r).id⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact hm _ _ _ _ rfl hd rfl rfl

/-- The replicas other than `r`, in increasing order. -/
def others (r : Fin 3) : List (Fin 3) := [0, 1, 2].filter (fun i => i ≠ r)

theorem others_ne {r q : Fin 3} (h : q ∈ others r) : q ≠ r := by
  simp [others] at h; exact h.2

theorem mapM_sendPeer_others {s : RState} {r : Fin 3} (hs : s.id = rid32 r) (msg : Msg) :
    (([0, 1, 2] : List w32).filter (fun i => decide ¬i = s.id)).mapM (fun q => sendPeer s q msg) =
      some ((others r).map (fun q => Out.send q msg)) := by
  simp only [sendPeer, hs]
  rcases r with ⟨_|_|_|_, h⟩
  · rfl
  · rfl
  · rfl
  · omega

theorem stepClientRead_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (rid cid : w32)
    (k : w64) (d : Dep) (hk : k = 0) (hd : slt d.key 0 = true) (hc : sge cid 0 = true)
    (hn : (st r).nReqs < 24) (hu : (cid, rid) ∉ (st r).used) :
    Ok (stepClientRead (st r) rid cid k d) (Post st r) := by
  have hc' : 0 ≤ cid.toInt := by simpa [sge, sle] using hc
  have hmx := budget_lt (hI r) hn
  have hn' : ¬ (24 ≤ (st r).nReqs) := by omega
  tsimp [stepClientRead, hk, hd, hc, hn', hu, beq_self_eq_true, Bool.and_self]
  apply Ok.bind
  have hNs := mx_succ hmx
  have hne : ∀ x : w32, x.toNat ≤ (st r).maxN.toNat → x ≠ (st r).maxN + 1 := by
    intro x hx he; rw [he, hNs] at hx; omega
  refine (Ok.loop _ _ _ (fun _ b => EqE (st r) b ∧ b.nReqs = (st r).nReqs + 1 ∧
      b.used = (cid, rid) :: (st r).used ∧ b.maxN = (st r).maxN + 1 ∧ b.wops = (st r).wops ∧
      b.rops = (st r).rops.put (shiftInts rid cid)
        { requestId := rid, clientId := cid, n := (st r).maxN + 1, maxValTag := none, readValTag := none,
          numRead1Replies := 1, numRead2Replies := 0, readsWithMaxTag := 0, sentRead2Round := false,
          determinedReadVal := false, replicasWithMaxTag := [] } ∧
      OqExt ((st r).maxN + 1) ((st r).ongoingReqs.put ((st r).maxN + 1)
        { requestId := rid, clientId := cid, isRead := true, shortReads := [] }) b.ongoingReqs)
      ?_ ?_).mono ?_
  · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, OqExt.refl _ _⟩
  · intro pre a post b hl hb
    obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hb
    split
    · have ha : a ∈ (st r).wops := by rw [hl]; simp
      obtain ⟨a1, ⟨o, ho, -⟩, -⟩ := (hI r).coord.wops a ha
      have h1 : ((st r).ongoingReqs.put ((st r).maxN + 1)
          { requestId := rid, clientId := cid, isRead := true, shortReads := [] }).get? a.2.n = some o := by
        rw [AMap.get?_put, if_neg (hne _ a1)]; exact ho
      have hs := (hb7 a.2.n).1
      rw [h1] at hs
      obtain ⟨o2, ho2⟩ := Option.isSome_iff_exists.1 hs
      rw [ho2]
      exact Ok.ret ⟨⟨hb1.id, hb1.crtInstance, hb1.committedUpTo, hb1.conf, hb1.inst, hb1.proposeQ⟩,
        hb2, hb3, hb4, hb5, hb6, hb7.put ho2⟩
    · exact Ok.ret ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩
  · intro b hb
    obtain ⟨pre, ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩, -⟩ := hb
    rw [mapM_sendPeer_others (hb1.id.trans (hI r).id)]
    apply Ok.ret
    have hs : SI (Pf st) r b := by
      refine SI.ofCoord (hI r) hb1 (by rw [hb2]; omega)
        (by have := (hI r).budget; rw [hb2, hb4, hNs]; omega)
        (by intro p hp; rw [hb3] at hp; simp at hp; rcases hp with rfl | hp
            · exact hc'
            · exact (hI r).usedPos _ hp) ?_
      rw [hb3, hb4, hb5, hb6]
      exact (hI r).coord.newRead hmx rid cid _ ⟨rfl, rfl, rfl, rfl⟩ rfl hb7
    refine Post.of (Mono.ofCoord hb1 (fun p h => by rw [hb3]; exact List.mem_cons_of_mem _ h)
      (fun _ _ _ h => by rw [hb5]; exact h)) (by simp [RState.crt, hb1.crtInstance]) hs ?_
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨q, -, rfl⟩ := hx
    simp only [OutOk, MInv]
    exact ⟨trivial, trivial, r, by rw [hb1.id, (hI r).id]⟩

end Perennial.gryff.pure.tot
