/-
`bcastStep`: a pending broadcast reads `alive` for its next peer. The message moves from the
broadcast's intended set to the peer's outbox (or is dropped: `msgs` only shrinks), the history
gains a `sent` event of a broadcast message (no conjunct is about those), and the replica's state
changes only in `lb.preAcceptsSent` (no conjunct reads it).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Lose

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace BcastProof

/-- `e` is not the send of a broadcast message. -/
def NotBS (e : Event) : Prop := ∀ to m, e = .sent to m → m.isBcast = false

/-- The history grows by sends of broadcast messages only. -/
def BSExt (S S' : Sys) : Prop :=
  ∃ E : List (Nat × Event), S'.hist = S.hist ++ E ∧
    ∀ x ∈ E, ∃ r to m, x = (r, .sent to m) ∧ m.isBcast = true

theorem notBS_of_mem (E : List (Nat × Event))
    (hE : ∀ x ∈ E, ∃ r to m, x = (r, .sent to m) ∧ m.isBcast = true) (r : Nat) (e : Event)
    (he : NotBS e) : (r, e) ∉ E := by
  intro h
  obtain ⟨r', to, m, hx, hb⟩ := hE _ h
  simp only [Prod.mk.injEq] at hx
  have := he to m hx.2; rw [this] at hb; cases hb

theorem ev_iff {S S' : Sys} (h : BSExt S S') (r : Nat) (e : Event) (he : NotBS e) :
    S'.ev r e ↔ S.ev r e := by
  obtain ⟨E, hh, hE⟩ := h
  simp only [Sys.ev, hh, List.mem_append]
  constructor
  · rintro (h1 | h1)
    · exact h1
    · exact absurd h1 (notBS_of_mem E hE r e he)
  · exact Or.inl

theorem ev_mono {S S' : Sys} (h : BSExt S S') (r : Nat) (e : Event) (h1 : S.ev r e) :
    S'.ev r e := by
  obtain ⟨E, hh, -⟩ := h
  simp only [Sys.ev, hh, List.mem_append]; exact Or.inl h1

theorem evBefore_mono {S S' : Sys} (h : BSExt S S') (r : Nat) (e : Event) (r' : Nat)
    (e' : Event) (h1 : S.evBefore r e r' e') : S'.evBefore r e r' e' := by
  obtain ⟨E, hh, -⟩ := h
  obtain ⟨p, p', hp, h2, h3⟩ := h1
  refine ⟨p, p', hp, ?_, ?_⟩ <;> rw [hh]
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h2).1, h2]
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h3).1, h3]

theorem evBefore_back {S S' : Sys} (h : BSExt S S') (r : Nat) (e : Event) (r' : Nat)
    (e' : Event) (he' : NotBS e') (h1 : S'.evBefore r e r' e') : S.evBefore r e r' e' := by
  obtain ⟨E, hh, hE⟩ := h
  obtain ⟨p, p', hp, h2, h3⟩ := h1
  rw [hh] at h2 h3
  have hp' : p' < S.hist.length := by
    rcases Nat.lt_or_ge p' S.hist.length with hc | hc
    · exact hc
    · rw [List.getElem?_append_right hc] at h3
      exact absurd (List.mem_of_getElem? h3) (notBS_of_mem E hE r' e' he')
  refine ⟨p, p', hp, ?_, ?_⟩
  · rwa [List.getElem?_append_left (by omega)] at h2
  · rwa [List.getElem?_append_left hp'] at h3

theorem count_eq {S S' : Sys} (h : BSExt S S') (r : Nat) (e : Event) (he : NotBS e) :
    (S'.hist.filter (· = (r, e))).length = (S.hist.filter (· = (r, e))).length := by
  obtain ⟨E, hh, hE⟩ := h
  rw [hh, List.filter_append, List.length_append]
  have : E.filter (· = (r, e)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx hxe
    simp only [decide_eq_true_eq] at hxe
    subst hxe; exact notBS_of_mem E hE r e he hx
  rw [this]; rfl

/-- `w'` is `w` up to `lb.preAcceptsSent`. -/
def PasRel (w w' : InstRec) : Prop :=
  w' = w ∨ ∃ lb n, w.lb = some lb ∧ w' = { w with lb := some { lb with preAcceptsSent := n } }

theorem setPAS_inst (σ : RState) (x : InstId) (n : Nat) (x0 : InstId) :
    (∀ w', (setPreAcceptsSent σ x n).inst x0 = some w' → ∃ w, σ.inst x0 = some w ∧ PasRel w w') ∧
    (∀ w, σ.inst x0 = some w → ∃ w', (setPreAcceptsSent σ x n).inst x0 = some w' ∧ PasRel w w') := by
  unfold setPreAcceptsSent
  split
  · rename_i w hw
    split
    · rename_i lb hlb
      simp only [RState.setInst, upd_apply]
      by_cases hx : x0 = x
      · subst hx
        simp only [if_true, hw, Option.some.injEq]
        exact ⟨fun w' h => ⟨w, rfl, Or.inr ⟨lb, _, hlb, h.symm⟩⟩,
          fun w0 h => ⟨_, rfl, Or.inr ⟨lb, _, h ▸ hlb, by rw [h]⟩⟩⟩
      · simp only [hx, if_false]
        exact ⟨fun w' h => ⟨w', h, Or.inl rfl⟩, fun w0 h => ⟨w0, h, Or.inl rfl⟩⟩
    · exact ⟨fun w' h => ⟨w', h, Or.inl rfl⟩, fun w0 h => ⟨w0, h, Or.inl rfl⟩⟩
  · exact ⟨fun w' h => ⟨w', h, Or.inl rfl⟩, fun w0 h => ⟨w0, h, Or.inl rfl⟩⟩

theorem bcastRep_inst (σ : RState) (b : Bcast) (a : Bool) (x0 : InstId) :
    (∀ w', (bcastRep σ b a).inst x0 = some w' → ∃ w, σ.inst x0 = some w ∧ PasRel w w') ∧
    (∀ w, σ.inst x0 = some w → ∃ w', (bcastRep σ b a).inst x0 = some w' ∧ PasRel w w') := by
  unfold bcastRep
  split
  · exact setPAS_inst _ _ _ _
  · exact ⟨fun w' h => ⟨w', h, Or.inl rfl⟩, fun w0 h => ⟨w0, h, Or.inl rfl⟩⟩

/-- `PasRel` keeps every field but `lb.preAcceptsSent`. -/
theorem PasRel.fields {w w' : InstRec} (h : PasRel w w') :
    w'.cmds = w.cmds ∧ w'.bal = w.bal ∧ w'.vbal = w.vbal ∧ w'.status = w.status ∧
    w'.seq = w.seq ∧ w'.deps = w.deps ∧ w'.id = w.id ∧ (w'.lb = none ↔ w.lb = none) ∧
    ∀ lb', w'.lb = some lb' → ∃ lb, w.lb = some lb ∧
      (lb' = lb ∨ ∃ n, lb' = { lb with preAcceptsSent := n }) := by
  rcases h with rfl | ⟨lb, n, hlb, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, Iff.rfl, fun lb' h => ⟨lb', h, Or.inl rfl⟩⟩
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [hlb], fun lb' h => ⟨lb, hlb, Or.inr ⟨n, ?_⟩⟩⟩
    simp only [Option.some.injEq] at h; exact h.symm

theorem bcastRep_eq (σ : RState) (b : Bcast) (a : Bool) :
    (bcastRep σ b a).id = σ.id ∧ (bcastRep σ b a).crtInstance = σ.crtInstance ∧
    (bcastRep σ b a).conflicts = σ.conflicts ∧ (bcastRep σ b a).execedUpTo = σ.execedUpTo ∧
    (bcastRep σ b a).store = σ.store := by
  unfold bcastRep
  split
  · unfold setPreAcceptsSent; split
    · split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The derived views of a replica's state agree under `bcastRep`. -/
theorem views (σ σ' : RState)
    (h1 : ∀ x0 w', σ'.inst x0 = some w' → ∃ w, σ.inst x0 = some w ∧ PasRel w w')
    (h2 : ∀ x0 w, σ.inst x0 = some w → ∃ w', σ'.inst x0 = some w' ∧ PasRel w w') :
    σ'.executed = σ.executed ∧ σ'.ready = σ.ready ∧ σ'.depEdge = σ.depEdge ∧
    sccLe σ' = sccLe σ ∧ Sys.slotsOn σ' = Sys.slotsOn σ ∧
    (∀ x0, (σ'.inst x0).map (·.bal) = (σ.inst x0).map (·.bal)) ∧
    (∀ x0, (σ'.inst x0).map (·.seq) = (σ.inst x0).map (·.seq)) ∧
    (∀ x0, (σ'.inst x0).bind (·.cmds) = (σ.inst x0).bind (·.cmds)) := by
  have hmap : ∀ {β} (f : InstRec → β), (∀ w w', PasRel w w' → f w' = f w) →
      ∀ x0, (σ'.inst x0).map f = (σ.inst x0).map f := by
    intro β f hf x0
    cases hw' : σ'.inst x0 with
    | none =>
      cases hw : σ.inst x0 with
      | none => rfl
      | some w => obtain ⟨w', h, -⟩ := h2 x0 w hw; rw [hw'] at h; cases h
    | some w' => obtain ⟨w, hw, hr⟩ := h1 x0 w' hw'; rw [hw]; simp [hf w w' hr]
  have hbind : ∀ x0, (σ'.inst x0).bind (·.cmds) = (σ.inst x0).bind (·.cmds) := by
    intro x0
    have := hmap (fun w => w.cmds) (fun w w' h => h.fields.1) x0
    cases h3 : σ'.inst x0 <;> cases h4 : σ.inst x0 <;> simp_all
  have hst := hmap (fun w => (w.status, w.cmds, w.deps)) (fun w w' h => by
    obtain ⟨c1, -, -, c4, -, c6, -⟩ := h.fields; simp [c1, c4, c6])
  have hseq := hmap (fun w => w.seq) (fun w w' h => h.fields.2.2.2.2.1)
  refine ⟨?_, ?_, ?_, ?_, ?_, hmap (fun w => w.bal) (fun w w' h => h.fields.2.1), hseq, hbind⟩
  · funext x0; apply propext; simp only [RState.executed]
    have := hst x0
    cases h3 : σ'.inst x0 <;> cases h4 : σ.inst x0 <;> simp_all
  · funext x0; apply propext; simp only [RState.ready]
    have := hst x0
    cases h3 : σ'.inst x0 <;> cases h4 : σ.inst x0 <;> simp_all
  · funext x0 y; apply propext; simp only [RState.depEdge]
    have := hst x0
    cases h3 : σ'.inst x0 <;> cases h4 : σ.inst x0 <;> simp_all
  · funext a0 b0; simp only [sccLe, hseq]
  · funext xs k; simp only [Sys.slotsOn, hbind]

theorem next_some (b b' : Bcast) (a : Bool) (h : b.next a = some b') :
    b'.m = b.m ∧ b'.x = b.x ∧ b'.peers = b.peers.tail ∧ b'.peers ≠ [] ∧ b'.sent < b'.need := by
  unfold Bcast.next at h
  split at h
  · cases h
  · rename_i p ps hps
    split at h <;>
    · unfold Bcast.norm at h
      split at h
      · cases h
      · rename_i hn
        simp only [Option.some.injEq] at h; subst h
        simp only [not_or, Nat.not_le] at hn
        exact ⟨rfl, rfl, by simp [hps], hn.1, hn.2⟩

end BcastProof

open BcastProof LoseProof in
theorem inv0_step_bcast' (S : Sys) (i : Nat) (b : Bcast) (a : Bool) (hS : Inv0 S)
    (hb : S.pending i = some b) (hp : b.peers ≠ []) : Inv0 (S.bcastStep i b a) := by
  have hkind : b.m.isBcast = true := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i b hb
  obtain ⟨p, ps, hpe⟩ : ∃ p ps, b.peers = p :: ps := by
    cases h : b.peers with
    | nil => exact absurd h hp
    | cons p ps => exact ⟨p, ps, rfl⟩
  have hpmem : p ∈ b.peers := by rw [hpe]; exact List.mem_cons_self
  generalize hS' : S.bcastStep i b a = S'
  -- the fields of the new state
  have hrep : S'.rep = upd S.rep i (bcastRep (S.rep i) b a) := by
    subst hS'; simp only [Sys.bcastStep, hpe]; cases a <;> rfl
  have hpend : S'.pending = upd S.pending i (b.next a) := by
    subst hS'; simp only [Sys.bcastStep, hpe]; cases a <;> rfl
  have hsent : S'.sent = S.sent := by subst hS'; simp only [Sys.bcastStep, hpe]; cases a <;> rfl
  have hdel : S'.delivered = S.delivered := by
    subst hS'; simp only [Sys.bcastStep, hpe]; cases a <;> rfl
  have hops : S'.ops = S.ops := by subst hS'; simp only [Sys.bcastStep, hpe]; cases a <;> rfl
  have howner : S'.owner = S.owner := by
    subst hS'; simp only [Sys.bcastStep, hpe]; cases a <;> rfl
  have hlog : S'.execLog = S.execLog := by
    subst hS'; simp only [Sys.bcastStep, hpe]; cases a <;> rfl
  have hcur : S'.execCur = S.execCur := by
    subst hS'; simp only [Sys.bcastStep, hpe]; cases a <;> rfl
  have hidx : S'.execIdx = S.execIdx := by
    subst hS'; simp only [Sys.bcastStep, hpe]; cases a <;> rfl
  have hgexec : S'.gexec = S.gexec := by
    subst hS'; simp only [Sys.bcastStep, hpe]; cases a <;> rfl
  have hfired : S'.fired = S.fired := by
    subst hS'; simp only [Sys.bcastStep, hpe]; cases a <;> rfl
  have hext : BSExt S S' := by
    subst hS'; simp only [Sys.bcastStep, hpe]
    cases a
    · exact ⟨[], by simp, by simp⟩
    · exact ⟨[(i, .sent p b.m)], rfl, by
        intro x hx; simp only [List.mem_singleton] at hx; exact ⟨i, p, b.m, hx, hkind⟩⟩
  have hob : ∀ fr to, S'.outbox fr to =
      S.outbox fr to ++ (if a = true ∧ fr = i ∧ to = p then [b.m] else []) := by
    intro fr to
    subst hS'; simp only [Sys.bcastStep, hpe]
    cases a
    · simp
    · simp only [Sys.emit, upd_apply]
      by_cases h1 : fr = i
      · subst h1; by_cases h2 : to = p
        · subst h2; simp
        · simp [h2]
      · simp [h1]
  have hsub : ∀ fr to m, m ∈ S'.msgs fr to → m ∈ S.msgs fr to := by
    intro fr to m hm
    simp only [Sys.msgs, Sys.intended, List.mem_append, hsent, hob, hpend] at hm ⊢
    rcases hm with (h1 | h1 | h1) | h1
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h1)
    · split at h1
      · rename_i hc
        simp only [List.mem_singleton] at h1; subst h1
        obtain ⟨-, rfl, rfl⟩ := hc
        right; rw [hb]; simp [hpmem]
      · cases h1
    · right
      by_cases h2 : fr = i
      · subst h2; simp only [upd_same] at h1; rw [hb]
        cases hn : b.next a with
        | none => rw [hn] at h1; cases h1
        | some b' =>
          rw [hn] at h1
          obtain ⟨e1, -, e3, -⟩ := next_some b b' a hn
          simp only at h1
          split at h1
          · rename_i hto
            simp only [List.mem_singleton] at h1; subst h1
            rw [e3, hpe] at hto
            simp [e1, hpe]; exact Or.inr hto
          · cases h1
      · simp only [upd_other _ _ _ _ h2] at h1; exact h1
  -- the replicas' states
  have hR1 : ∀ r x0 w', (S'.rep r).inst x0 = some w' → ∃ w, (S.rep r).inst x0 = some w ∧ PasRel w w' := by
    intro r x0 w' h; rw [hrep] at h
    by_cases hr : r = i
    · subst hr; simp only [upd_same] at h; exact (bcastRep_inst _ _ _ _).1 w' h
    · simp only [upd_other _ _ _ _ hr] at h; exact ⟨w', h, Or.inl rfl⟩
  have hR2 : ∀ r x0 w, (S.rep r).inst x0 = some w → ∃ w', (S'.rep r).inst x0 = some w' ∧ PasRel w w' := by
    intro r x0 w h; rw [hrep]
    by_cases hr : r = i
    · subst hr; simp only [upd_same]; exact (bcastRep_inst _ _ _ _).2 w h
    · simp only [upd_other _ _ _ _ hr]; exact ⟨w, h, Or.inl rfl⟩
  have hV : ∀ r, _ := fun r => views (S.rep r) (S'.rep r) (hR1 r) (hR2 r)
  have hF : ∀ r, (S'.rep r).id = (S.rep r).id ∧ (S'.rep r).crtInstance = (S.rep r).crtInstance ∧
      (S'.rep r).conflicts = (S.rep r).conflicts ∧ (S'.rep r).execedUpTo = (S.rep r).execedUpTo ∧
      (S'.rep r).store = (S.rep r).store := by
    intro r; rw [hrep]
    by_cases hr : r = i
    · subst hr; simp only [upd_same]; exact bcastRep_eq _ _ _
    · simp [upd_other _ _ _ _ hr]
  have hexd : ∀ r, (S'.rep r).executed = (S.rep r).executed := fun r => (hV r).1
  have hrdy : ∀ r, (S'.rep r).ready = (S.rep r).ready := fun r => (hV r).2.1
  have hdep : ∀ r, (S'.rep r).depEdge = (S.rep r).depEdge := fun r => (hV r).2.2.1
  have hle : ∀ r, sccLe (S'.rep r) = sccLe (S.rep r) := fun r => (hV r).2.2.2.1
  have hslo : ∀ r, Sys.slotsOn (S'.rep r) = Sys.slotsOn (S.rep r) := fun r => (hV r).2.2.2.2.1
  have hbal : ∀ r x0, ((S'.rep r).inst x0).map (·.bal) = ((S.rep r).inst x0).map (·.bal) :=
    fun r => (hV r).2.2.2.2.2.1
  -- events
  have hcm' : Inv.commitMsgs S' := by
    intro fr to m hm
    obtain ⟨r, b0, he⟩ := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 fr to m (hsub _ _ _ hm)
    exact ⟨r, b0, ev_mono hext _ _ he⟩
  have hcv : S'.committedVal = S.committedVal := by
    funext x v; apply propext
    rw [committedVal_ev S' hcm', committedVal_ev S hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    constructor
    · rintro ⟨r, b0, he⟩; exact ⟨r, b0, (ev_iff hext _ _ (fun to m h => by cases h)).mp he⟩
    · rintro ⟨r, b0, he⟩; exact ⟨r, b0, ev_mono hext _ _ he⟩
  have hevv : ∀ r x b0 st v, S'.ev r (.vote x b0 st v) ↔ S.ev r (.vote x b0 st v) :=
    fun r x b0 st v => ev_iff hext _ _ (fun to m h => by cases h)
  have hsl : S'.slowChosen = S.slowChosen := by
    funext x b0 v; simp only [Sys.slowChosen, hevv]
  have hfr : S'.fastReplies = S.fastReplies := by
    funext x v; simp only [Sys.fastReplies, hevv]
  have hfl : S'.fastLive = S.fastLive := by
    funext x v; simp only [Sys.fastLive, hfr, hbal,
      ev_iff hext _ (.fastCommit x v) (fun to m h => by cases h)]
  have hdE : S'.dEdge = S.dEdge := by funext x y; simp only [Sys.dEdge, hcv]
  have hsO : S'.sccOrd = S.sccOrd := by funext x y; simp only [Sys.sccOrd, hcv]
  have hlx : S'.lexec = S.lexec := by
    funext r k; simp only [Sys.lexec, Sys.curSlots, hslo, hlog, hcur, hidx]
  have hso : S'.slotOp = S.slotOp := by funext s; simp only [Sys.slotOp, howner]
  have hkv : S'.kv = S.kv := by funext k; simp only [Sys.kv, hgexec]
  have hdm : S'.deliveredMsg = S.deliveredMsg := by
    funext a0 r m; simp only [Sys.deliveredMsg, hsent, hdel]
  have hprep : ∀ r m e, S'.prepReport r m e → S.prepReport r m e := by
    rintro r m e ⟨he, h1 | h1⟩
    · obtain ⟨to, hm, rfl⟩ := h1
      exact ⟨(ev_iff hext _ _ (fun to' m' h => by cases h; rfl)).mp he,
        Or.inl ⟨to, hsub _ _ _ hm, rfl⟩⟩
    · subst h1; exact ⟨(ev_iff hext _ _ (fun to' m' h => by cases h)).mp he, Or.inr rfl⟩
  have hprepE : ∀ r m e, S.prepReport r m e → NotBS e := by
    rintro r m e ⟨-, h1 | h1⟩
    · obtain ⟨to, -, rfl⟩ := h1; intro to' m' h; cases h; rfl
    · subst h1; intro to' m' h; cases h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27⟩ := hS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, hcm', ?_, ?_, ?_⟩
  · -- wf
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := h1
    refine ⟨fun r hr => by rw [(hF r).1]; exact w1 r hr, fun r hr x0 w' hw' => ?_,
      fun r hr q hq => by rw [(hF r).2.1]; exact w3 r hr q hq, fun r hr q k p0 hk => ?_,
      fun r hr q hq n hn => ?_, fun fr to hne => ?_, fun fr to n hn => ?_, fun r b' hb' => ?_⟩
    · obtain ⟨w, hw, hrel⟩ := hR1 r x0 w' hw'
      obtain ⟨f1, -, -, f4, -, f6, f7, f8, f9⟩ := hrel.fields
      obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := w2 r hr x0 w hw
      refine ⟨f7 ▸ g1, g2, g3, fun hs => f6 ▸ g4 (f4 ▸ hs), fun lb' hlb' hs => ?_,
        fun hq => fun hn => g6 hq (f8.mp hn), fun lb' ps hlb' hps => ?_⟩
      · obtain ⟨lb, hlb, rfl | ⟨n, rfl⟩⟩ := f9 lb' hlb'
        · exact g5 _ hlb hs
        · exact g5 lb hlb hs
      · rw [howner]
        obtain ⟨lb, hlb, rfl | ⟨n, rfl⟩⟩ := f9 lb' hlb'
        · exact g7 _ ps hlb hps
        · exact g7 lb ps hlb hps
    · rw [(hF r).2.2.1] at hk
      obtain ⟨k1, k2, k3⟩ := w4 r hr q k p0 hk
      refine ⟨k1, fun h => ?_, fun h => ?_⟩
      · have := hbal r ⟨q, toN p0.last⟩; intro hn; rw [hn] at this
        cases h' : (S.rep r).inst ⟨q, toN p0.last⟩ with
        | none => exact k2 h h'
        | some _ => rw [h'] at this; cases this
      · have := hbal r ⟨q, toN p0.lastWrite⟩; intro hn; rw [hn] at this
        cases h' : (S.rep r).inst ⟨q, toN p0.lastWrite⟩ with
        | none => exact k3 h h'
        | some _ => rw [h'] at this; cases this
    · rw [(hF r).2.2.2.1] at hn; rw [hexd]; exact w5 r hr q hq n hn
    · apply w6; intro he
      obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ hne
      have := hsub _ _ _ hm; rw [he] at this; cases this
    · rw [hdel] at hn; rw [hsent]; exact w7 fr to n hn
    · rw [hpend] at hb'
      by_cases hr : r = i
      · subst hr; simp only [upd_same] at hb'
        obtain ⟨d1, d2, d3, d4, d5, d6, w, lb, hw, hlb⟩ := w8 r b hb
        obtain ⟨e1, e2, e3, e4, e5⟩ := next_some b b' a hb'
        obtain ⟨w', hw', hrel⟩ := hR2 r b.x w hw
        obtain ⟨-, -, -, -, -, -, -, f8, -⟩ := hrel.fields
        refine ⟨d1, hcur ▸ d2, e4, e5, ?_, ?_, ?_⟩
        · rw [e3, hpe] at *; simp only [List.tail_cons]; rw [hpe] at d5; exact (List.nodup_cons.mp d5).2
        · intro q hq; rw [e3, hpe] at hq; simp only [List.tail_cons] at hq
          exact d6 q (by rw [hpe]; exact List.mem_cons_of_mem _ hq)
        · rw [e2]
          cases hl : w'.lb with
          | none => exact absurd (f8.mp hl) (by rw [hlb]; simp)
          | some lb' => exact ⟨w', lb', hw', hl⟩
      · simp only [upd_other _ _ _ _ hr] at hb'
        obtain ⟨d1, d2, d3, d4, d5, d6, w, lb, hw, hlb⟩ := w8 r b' hb'
        obtain ⟨w', hw', hrel⟩ := hR2 r b'.x w hw
        obtain ⟨-, -, -, -, -, -, -, f8, -⟩ := hrel.fields
        refine ⟨d1, hcur ▸ d2, d3, d4, d5, d6, ?_⟩
        cases hl : w'.lb with
        | none => exact absurd (f8.mp hl) (by rw [hlb]; simp)
        | some lb' => exact ⟨w', lb', hw', hl⟩
  · intro fr to m hm; exact h2 fr to m (hsub _ _ _ hm)
  · intro fr to m x hm hx hk
    obtain ⟨w, lb, hw, hlb⟩ := h3 fr to m x (hsub _ _ _ hm) hx hk
    obtain ⟨w', hw', hrel⟩ := hR2 to x w hw
    obtain ⟨-, -, -, -, -, -, -, f8, -⟩ := hrel.fields
    cases hl : w'.lb with
    | none => exact absurd (f8.mp hl) (by rw [hlb]; simp)
    | some lb' => exact ⟨w', lb', hw', hl⟩
  · intro fr to m hm; exact h4 fr to m (hsub _ _ _ hm)
  · -- ballots
    refine ⟨fun r hr x0 w' hw' => ?_, fun r hr x0 b0 st v he => ?_⟩
    · obtain ⟨w, hw, hrel⟩ := hR1 r x0 w' hw'
      obtain ⟨-, f2, f3, -⟩ := hrel.fields
      rw [f2, f3]; exact h5.1 r hr x0 w hw
    · obtain ⟨w, hw, hb0⟩ := h5.2 r hr x0 b0 st v ((hevv _ _ _ _ _).mp he)
      obtain ⟨w', hw', hrel⟩ := hR2 r x0 w hw
      exact ⟨w', hw', hrel.fields.2.1 ▸ hb0⟩
  · -- ballotOwner
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := h6
    have hmb : ∀ r x b0, S'.ev r (.makeBallot x b0) ↔ S.ev r (.makeBallot x b0) :=
      fun r x b0 => ev_iff hext _ _ (fun to m h => by cases h)
    refine ⟨fun r x b0 he => ?_, fun r x b0 v he => ?_, fun r x b0 v he => ?_,
      fun r to m hm => ?_, fun r to m hm => ?_, fun r to m hm => ?_⟩
    · rw [hmb] at he; rw [count_eq hext _ _ (fun to m h => by cases h)]; exact o1 r x b0 he
    · have := o2 r x b0 v ((ev_iff hext _ _ (fun to m h => by cases h)).mp he)
      exact evBefore_mono hext _ _ _ _ this
    · rw [hmb]; exact o3 r x b0 v ((ev_iff hext _ _ (fun to m h => by cases h)).mp he)
    · rw [hmb]; exact o4 r to m (hsub _ _ _ hm)
    · obtain ⟨c1, c2⟩ := o5 r to m (hsub _ _ _ hm); exact ⟨c1, ev_mono hext _ _ c2⟩
    · obtain ⟨c1, c2⟩ := o6 r to m (hsub _ _ _ hm); exact ⟨c1, ev_mono hext _ _ c2⟩
  · -- oneProposal
    have hph : ∀ r x b0 v, S'.ev r (.phase1 x b0 v) ↔ S.ev r (.phase1 x b0 v) :=
      fun r x b0 v => ev_iff hext _ _ (fun to m h => by cases h)
    have hac : ∀ r x b0 v, S'.ev r (.accept x b0 v) ↔ S.ev r (.accept x b0 v) :=
      fun r x b0 v => ev_iff hext _ _ (fun to m h => by cases h)
    obtain ⟨p1, p2, p3⟩ := h7
    refine ⟨fun r r' x b0 v v' he he' => ?_, fun r r' x b0 v v' he he' => ?_,
      fun r r' x b0 v v' he he' => ?_⟩
    · rw [hph] at he he'; rw [count_eq hext _ _ (fun to m h => by cases h)]
      exact p1 r r' x b0 v v' he he'
    · rw [hac] at he he'; exact p2 r r' x b0 v v' he he'
    · rw [hph] at he; rw [hac] at he'; exact p3 r r' x b0 v v' he he'
  · -- votesFollowProposals
    refine ⟨fun r x b0 st v he hst => ?_, fun r x b0 v he => ?_⟩
    · obtain ⟨l, v0, h1', h2'⟩ := h8.1 r x b0 st v ((hevv _ _ _ _ _).mp he) hst
      exact ⟨l, v0, ev_mono hext _ _ h1', h2'⟩
    · obtain ⟨l, h1'⟩ := h8.2 r x b0 v ((hevv _ _ _ _ _).mp he)
      exact ⟨l, ev_mono hext _ _ h1'⟩
  · -- repliesReportVotes
    obtain ⟨q1, q2, q3⟩ := h9
    refine ⟨fun r m e hp => ?_, fun a0 r m hm => ?_, fun a0 r m hm => ?_⟩
    · have hp0 := hprep r m e hp
      obtain ⟨c1, c2, c3, c4, c5⟩ := q1 r m e hp0
      have hne := hprepE r m e hp0
      refine ⟨c1, fun hs => evBefore_mono hext _ _ _ _ (c2 hs), by rw [hcv]; exact c3,
        fun hs b0 st v hb' => c4 hs b0 st v (evBefore_back hext _ _ _ _ hne hb'),
        fun b0 st v hb' => c5 b0 st v (evBefore_back hext _ _ _ _ (fun to m h => by cases h) hb')⟩
    · obtain ⟨c1, c2, c3, c4⟩ := q2 a0 r m (hsub _ _ _ hm)
      refine ⟨?_, ?_, ?_, ?_⟩
      · obtain ⟨v, hv⟩ := c1; exact ⟨v, ev_mono hext _ _ hv⟩
      · intro hs; obtain ⟨d1, v, d2, d3⟩ := c2 hs; exact ⟨d1, v, ev_mono hext _ _ d2, d3⟩
      · intro hs; obtain ⟨v, d2, d3⟩ := c3 hs; exact ⟨v, ev_mono hext _ _ d2, d3⟩
      · intro hs; rw [hcv]; exact c4 hs
    · rcases q3 a0 r m (hsub _ _ _ hm) with ⟨v, hv⟩ | ⟨⟨b0, v, hv⟩, c2⟩
      · exact Or.inl ⟨v, evBefore_mono hext _ _ _ _ hv⟩
      · refine Or.inr ⟨⟨b0, v, evBefore_mono hext _ _ _ _ hv⟩, fun m' e' hp' hx hb' => ?_⟩
        exact c2 m' e' (hprep _ _ _ hp') hx
          (evBefore_back hext _ _ _ _ (fun to m0 h => by cases h; rfl) hb')
  · -- prepReplyHighest
    intro r m e hp b0 st v hb'
    have hp0 := hprep r m e hp
    exact h10 r m e hp0 b0 st v (evBefore_back hext _ _ _ _ (hprepE r m e hp0) hb')
  · -- lbInv
    intro r hr x0 w' lb' hw' hlb'
    obtain ⟨w, hw, hrel⟩ := hR1 r x0 w' hw'
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := hrel.fields
    obtain ⟨lb, hlb, hlbe⟩ := f9 lb' hlb'
    obtain ⟨a1, a2, a3, a4, a5, ⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩, a8, a9⟩ :=
      h11 r hr x0 w lb hw hlb
    have key : lb'.lastTriedBallot = lb.lastTriedBallot ∧ lb'.ballot = lb.ballot ∧
        lb'.tryingToPreAccept = lb.tryingToPreAccept ∧ lb'.status = lb.status ∧
        lb'.preAcceptOKs = lb.preAcceptOKs ∧ lb'.preparing = lb.preparing ∧ lb'.cmds = lb.cmds ∧
        lb'.deps = lb.deps ∧ lb'.seq = lb.seq ∧ lb'.allEqual = lb.allEqual ∧
        lb'.acceptOKs = lb.acceptOKs ∧ lb'.prepareReplies = lb.prepareReplies := by
      rcases hlbe with rfl | ⟨n, rfl⟩ <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12⟩ := key
    rw [k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, f2, f4, hdm]
    refine ⟨ev_mono hext _ _ a1, a2, a3, fun b0 v hv => a4 b0 v ?_, fun c1 c2 => by
        obtain ⟨d1, d2, v, d3, d4⟩ := a5 c1 c2; exact ⟨d1, d2, v, ev_mono hext _ _ d3, d4⟩,
      ⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩, fun c1 c2 c3 c4 => ?_, fun hp => ?_⟩
    · rcases hv with hv | hv
      · exact Or.inl ((ev_iff hext _ _ (fun to m h => by cases h)).mp hv)
      · exact Or.inr ((ev_iff hext _ _ (fun to m h => by cases h)).mp hv)
    · obtain ⟨d1, d2⟩ := a8 c1 c2 c3 c4; exact ⟨ev_mono hext _ _ d1, ev_mono hext _ _ d2⟩
    · obtain ⟨c1, c2⟩ := a9 hp
      refine ⟨c1, fun e he => ?_⟩
      obtain ⟨d1, d2, d3⟩ := c2 e he
      refine ⟨d1, d2, ?_⟩
      rcases d3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl ⟨e1, e2⟩
      · exact Or.inr ⟨e1, ev_mono hext _ _ e2⟩
  · -- agreement
    refine ⟨by rw [hcv]; exact h12.1, fun r hr x0 w' hw' hc => ?_⟩
    obtain ⟨w, hw, hrel⟩ := hR1 r x0 w' hw'
    obtain ⟨f1, -, -, f4, f5, f6, -⟩ := hrel.fields
    rw [f4] at hc
    obtain ⟨c1, c2⟩ := h12.2 r hr x0 w hw hc
    refine ⟨f1 ▸ c1, ?_⟩
    rw [hcv]; simp only [instVal, f1, f5, f6]; exact c2
  · intro x v hv; rw [hcv, hsl, hfr] at *
    rw [ev_iff hext _ _ (fun to m h => by cases h)]; exact h13 x v hv
  · intro x b0 v hv b' hb'
    rw [hsl, hfl] at hv
    obtain ⟨c1, c2⟩ := h14 x b0 v hv b' hb'
    exact ⟨fun r v' he => c1 r v' ((ev_iff hext _ _ (fun to m h => by cases h)).mp he),
      fun r v' he => c2 r v' ((ev_iff hext _ _ (fun to m h => by cases h)).mp he)⟩
  · intro x y vx vy hxy hx hy; rw [hcv] at hx hy; exact h15 x y vx vy hxy hx hy
  · intro x v hv hn; rw [hcv] at hv
    obtain ⟨W, w1, w2, w3⟩ := h16 x v hv hn
    exact ⟨W, w1, w2, fun r hr => by
      obtain ⟨c1, d, c2, c3⟩ := w3 r hr; exact ⟨c1, d, ev_mono hext _ _ c2, c3⟩⟩
  · intro r e x cx y cy d hrec hxy hb' hi
    exact h17 r e x cx y cy d hrec hxy (evBefore_back hext _ _ _ _ (fun to m h => by cases h) hb') hi
  · -- execClosed
    intro r hr
    obtain ⟨e1, e2, e3⟩ := h18 r hr
    refine ⟨hlog ▸ e1, fun x0 => by rw [hlog, hexd]; exact e2 x0, fun x0 w' hw' hs => ?_⟩
    obtain ⟨w, hw, hrel⟩ := hR1 r x0 w' hw'
    obtain ⟨f1, -, -, f4, f5, f6, -⟩ := hrel.fields
    rw [f4] at hs
    obtain ⟨c1, c2⟩ := e3 x0 w hw hs
    refine ⟨by rw [hcv]; simp only [instVal, f1, f5, f6]; exact c1, fun y hy => ?_⟩
    rw [hdep] at hy; rw [hexd, hcur]; exact c2 y hy
  · -- execCursor
    intro r hr
    obtain ⟨c1, c2⟩ := h19 r hr
    rw [hcur, hidx]
    refine ⟨c1, fun hne => ?_⟩
    obtain ⟨done, C, d1, d2, d3, d4, d5, d6, d7⟩ := c2 hne
    refine ⟨done, C, by simp only [sccSort, hle]; exact d1, d2, by rw [hexd]; exact d3,
      by rw [hrdy]; exact d4, by rw [hdep, hexd]; exact d5, by rw [hdep]; exact d6,
      fun x0 w' hx hw' => ?_⟩
    obtain ⟨w, hw, hrel⟩ := hR1 r x0 w' hw'
    rw [hrel.fields.1]; exact d7 x0 w hx hw
  · intro r hr i0 j x y hij hx hy ht
    rw [hlog] at hx hy; rw [hdE, hsO] at *; exact h20 r hr i0 j x y hij hx hy ht
  · simp only [Inv.execPrefix, hlx, hgexec, (hF _).2.2.2.2]; exact h21
  · simp only [Inv.slots, hcv, howner, hops]; exact h22
  · simp only [Inv.clientOps, hcv, hso, hgexec, hfired, hops]; exact h23
  · intro r b' hb'
    rw [hpend] at hb'
    by_cases hr : r = i
    · subst hr; simp only [upd_same] at hb'
      rw [(next_some b b' a hb').1]; exact hkind
    · simp only [upd_other _ _ _ _ hr] at hb'; exact h25 r b' hb'
  · exact SafeProof.safe_same S S' (fun r x0 w hw => by
      obtain ⟨w', hw', hrel⟩ := hR2 r x0 w hw
      exact ⟨w', hw', hrel.fields.2.1, fun h => by rw [hrel.fields.2.2.2.1]; exact h⟩)
      (fun r e he => ev_mono hext r e he)
      (fun r e hk he => (ev_iff hext r e (by
        intro to m h; subst h; simp [SafeProof.safeKind] at hk)).mp he) hsub h26
  · exact SafeProof.reports_frame (SafeProof.safeMono_same S S' (fun r x0 w hw => by
      obtain ⟨w', hw', hrel⟩ := hR2 r x0 w hw
      exact ⟨w', hw', hrel.fields.2.1, fun h => by rw [hrel.fields.2.2.2.1]; exact h⟩)
      (fun r e he => ev_mono hext r e he)
      (fun r e hk he => (ev_iff hext r e (by
        intro to m h; subst h; simp [SafeProof.safeKind] at hk)).mp he) hsub)
      hprep (fun r m e x b st u hp h => evBefore_back hext _ _ _ _ (hprepE r m e hp) h)
      (fun r e hk he => (ev_iff hext r e (by
        intro to m h; subst h; simp [SafeProof.safeKind] at hk)).mp he) h27

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
