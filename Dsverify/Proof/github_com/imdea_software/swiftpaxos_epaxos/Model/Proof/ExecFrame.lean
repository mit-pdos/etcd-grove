/-
`InvExec` (p-modelexec) under the steps that do not execute: a general frame lemma
(`invExec_frame`: execution state kept, decided values only added, proposals kept, an instance
that released its proposals keeps them released), the start (`invExec_init`), a client proposal
(`invExec_clientPropose`) and a component's start (`invExec_execSCC`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.ExecCore

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace ExecOrd

theorem blk_congr {σ σ' : RState} {k : w64} {y : InstId} (h : cmdsAt σ' y = cmdsAt σ y) :
    blk σ' k y = blk σ k y := by
  simp only [blk, h]

theorem slotsOn_congr_cmds (σ σ' : RState) (k : w64) :
    ∀ (xs : List InstId), (∀ y ∈ xs, cmdsAt σ' y = cmdsAt σ y) →
      Sys.slotsOn σ' xs k = Sys.slotsOn σ xs k
  | [], _ => rfl
  | y :: ys, h => by
    rw [slotsOn_eq, slotsOn_eq, List.flatMap_cons, List.flatMap_cons, ← slotsOn_eq,
      ← slotsOn_eq, blk_congr (h y (by simp)),
      slotsOn_congr_cmds σ σ' k ys (fun z hz => h z (List.mem_cons_of_mem _ hz))]

/-- `lexec` is kept when the executor's state is and the records of the logged instances and of
the head are. -/
theorem lexec_congr (S S' : Sys) (r : Nat) (hlog : S'.execLog r = S.execLog r)
    (hcur : S'.execCur r = S.execCur r) (hidx : S'.execIdx r = S.execIdx r)
    (hin : ∀ y ∈ S.execLog r ++ (S.execCur r).take 1, cmdsAt (S'.rep r) y = cmdsAt (S.rep r) y)
    (k : w64) : S'.lexec r k = S.lexec r k := by
  unfold Sys.lexec Sys.curSlots
  rw [hlog, hcur, hidx, slotsOn_congr_cmds _ _ k _ (fun y hy => hin y (List.mem_append_left _ hy))]
  cases hc : S.execCur r with
  | nil => rfl
  | cons x rest =>
    dsimp only
    rw [slotsOn_congr_cmds _ _ k [x] (fun y hy => hin y (List.mem_append_right _ (by
      rw [hc]; simpa using hy)))]

section
variable {S S' : Sys} (h0 : Inv0 S) (hX : InvExec S)
include h0 hX

/-- Decided edges out of an execution sequence are kept when decided values are only added. -/
theorem dEdge_keep (hcv : ∀ x v, S.committedVal x v → S'.committedVal x v)
    (huq : ∀ x v v', S'.committedVal x v → S'.committedVal x v' → v = v')
    {r : Nat} (hr : r < nR) {a b : InstId} (ha : a ∈ S.eseq r) : S'.dEdge a b ↔ S.dEdge a b := by
  constructor
  · rintro ⟨v, hv, h1, h2⟩
    obtain ⟨w, -, -, -, hc, -⟩ := eseq_info h0 hr ha
    have := huq a v _ hv (hcv _ _ hc)
    subst this
    exact ⟨_, hc, h1, h2⟩
  · rintro ⟨v, hv, h1, h2⟩
    exact ⟨v, hcv _ _ hv, h1, h2⟩

theorem tg_keep (hcv : ∀ x v, S.committedVal x v → S'.committedVal x v)
    (huq : ∀ x v v', S'.committedVal x v → S'.committedVal x v' → v = v')
    {r : Nat} (hr : r < nR) {a b : InstId} (ha : a ∈ S.eseq r)
    (h : Relation.TransGen S'.dEdge a b) : Relation.TransGen S.dEdge a b := by
  induction h with
  | single h => exact .single ((dEdge_keep h0 hX hcv huq hr ha).mp h)
  | tail h1 h2 ih =>
    exact .tail ih ((dEdge_keep h0 hX hcv huq hr (reach_tg h0 hX hr ha ih)).mp h2)

omit h0 hX in
theorem tg_mono' {R R' : InstId → InstId → Prop} (hR : ∀ a b, R a b → R' a b) {a b : InstId}
    (h : Relation.TransGen R a b) : Relation.TransGen R' a b := by
  induction h with
  | single h => exact .single (hR _ _ h)
  | tail _ h ih => exact .tail ih (hR _ _ h)

omit h0 hX in
theorem tg_mono (hcv : ∀ x v, S.committedVal x v → S'.committedVal x v) {a b : InstId}
    (h : Relation.TransGen S.dEdge a b) : Relation.TransGen S'.dEdge a b := by
  refine tg_mono' (fun c d h => ?_) h
  obtain ⟨v, hv, h1, h2⟩ := h; exact ⟨v, hcv _ _ hv, h1, h2⟩

omit h0 hX in
theorem sccOrd_mono (hcv : ∀ x v, S.committedVal x v → S'.committedVal x v) {a b : InstId}
    (h : S.sccOrd a b) : S'.sccOrd a b := by
  obtain ⟨va, vb, h1, h2, h3⟩ := h; exact ⟨va, vb, hcv _ _ h1, hcv _ _ h2, h3⟩

/-- **Frame.** A step that keeps the executors' state and the global sequences, only adds decided
values, keeps the proposals, and keeps released instances released. -/
theorem invExec_frame (hlog : S'.execLog = S.execLog) (hcur : S'.execCur = S.execCur)
    (hcv : ∀ x v, S.committedVal x v → S'.committedVal x v)
    (huq : ∀ x v v', S'.committedVal x v → S'.committedVal x v' → v = v')
    (hlx : ∀ r < nR, ∀ k, S'.lexec r k = S.lexec r k) (hg : S'.gexec = S.gexec)
    (hown : S'.owner = S.owner) (hchan : S'.proposeChan = S.proposeChan) (hops : S'.ops = S.ops)
    (hdead : ∀ x, S.propDead x → S'.propDead x) : InvExec S' := by
  have hes : ∀ r, S'.eseq r = S.eseq r := by intro r; simp only [Sys.eseq, hlog, hcur]
  have hso : ∀ s, S'.slotOp s = S.slotOp s := by intro s; simp only [Sys.slotOp, hown]
  refine ⟨fun r hr a b ha hab => ?_, fun r hr l1 l2 a b he h1 h2 ht => ?_, fun k e he => ?_,
    fun s s' p p' hne h1 h2 h3 => ?_, fun i p s p' h1 h2 h3 => ?_, fun i j n m p p' h1 h2 h3 => ?_,
    fun i p h => ?_⟩
  · rw [hes] at ha ⊢
    exact hX.reach r hr a b ha ((dEdge_keep h0 hX hcv huq hr ha).mp hab)
  · rw [hes] at he
    have ha : a ∈ S.eseq r := by rw [he]; exact List.mem_append_left _ h1
    obtain ⟨c1, c2⟩ := hX.ord r hr l1 l2 a b he h1 h2 (tg_keep h0 hX hcv huq hr ha ht)
    exact ⟨tg_mono hcv c1, sccOrd_mono hcv c2⟩
  · rw [hg] at he
    obtain ⟨r, hr, h⟩ := hX.gloc k e he
    exact ⟨r, hr, by rw [hlx r hr]; exact h⟩
  · rw [hso] at h1 h2
    exact (hX.tokSlot s s' p p' hne h1 h2 h3).imp (hdead _) (hdead _)
  · rw [hchan] at h1; rw [hso] at h2
    exact hdead _ (hX.tokChan i p s p' h1 h2 h3)
  · rw [hchan] at h1 h2; exact hX.chanOnce i j n m p p' h1 h2 h3
  · rw [hchan] at h; rw [hops]; exact hX.chanOps i p h

end

/-- Released instances stay released when decided values are only added and every bookkeeping
holding proposals had them before. -/
theorem propDead_keep {S S' : Sys} (hcv : ∀ x v, S.committedVal x v → S'.committedVal x v)
    (hcp : ∀ x w' lb', (S'.rep x.q).inst x = some w' → w'.lb = some lb' →
      lb'.clientProposals ≠ none →
      ∃ w lb, (S.rep x.q).inst x = some w ∧ w.lb = some lb ∧ lb.clientProposals ≠ none)
    (x : InstId) (h : S.propDead x) : S'.propDead x := by
  obtain ⟨⟨v, c, h1, h2, h3⟩, h4⟩ := h
  refine ⟨⟨v, c, hcv _ _ h1, h2, h3⟩, fun w' lb' hw' hlb' => ?_⟩
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨w, lb, hw, hlb, hne'⟩ := hcp x w' lb' hw' hlb' hne
  exact hne' (h4 w lb hw hlb)

/-- The start. -/
theorem invExec_init : InvExec Sys.init := by
  refine ⟨fun r _ a b ha _ => by simp [Sys.eseq, Sys.init] at ha,
    fun r _ l1 l2 a b he h1 _ _ => ?_, fun k e he => by simp [Sys.init] at he,
    fun s s' p p' _ h1 _ _ => by simp [Sys.slotOp, Sys.init] at h1,
    fun i p s p' h1 _ _ => by simp [Sys.init] at h1,
    fun i j n m p p' h1 _ _ => by simp [Sys.init] at h1,
    fun i p h => by simp [Sys.init] at h⟩
  simp only [Sys.eseq, Sys.init, List.append_nil] at he
  have := List.append_eq_nil_iff.mp he.symm
  rw [this.1] at h1; cases h1

/-- A client's proposal reaches a channel (fresh connection id). -/
theorem invExec_clientPropose (S : Sys) (i : Nat) (p : Proposal) (h0 : Inv0 S) (hX : InvExec S)
    (hp : p.cid ∉ S.ops.map (·.2.cid)) :
    InvExec { S with ops := S.ops ++ [(i, p)],
                     proposeChan := upd S.proposeChan i (S.proposeChan i ++ [p]) } := by
  have hfresh : ∀ s p', S.slotOp s = some p' → p'.cid ≠ p.cid := by
    intro s p' h e
    unfold Sys.slotOp at h
    cases ho : S.owner s.1 with
    | none => rw [ho] at h; cases h
    | some ps =>
      rw [ho] at h
      have := (I0.slots h0).2 s.1 ps ho p' (List.mem_of_getElem? h)
      exact hp (e ▸ List.mem_map_of_mem (f := (·.2.cid)) this)
  have hchanfresh : ∀ j q, q ∈ S.proposeChan j → q.cid ≠ p.cid := by
    intro j q hq e; exact hp (e ▸ List.mem_map_of_mem (f := (·.2.cid)) (hX.chanOps j q hq))
  refine ⟨hX.reach, hX.ord, hX.gloc, hX.tokSlot, fun j q s p' h1 h2 h3 => ?_,
    fun j1 j2 n m q q' h1 h2 h3 => ?_, fun j q h => ?_⟩
  · simp only [upd_apply] at h1
    split at h1
    · rcases List.mem_append.mp h1 with h1 | h1
      · exact hX.tokChan _ q s p' h1 h2 h3
      · simp only [List.mem_singleton] at h1; subst h1; exact absurd h3 (hfresh s p' h2)
    · exact hX.tokChan j q s p' h1 h2 h3
  · simp only [upd_apply] at h1 h2
    -- positions in the new channels: old ones, or the new last entry of channel `i`
    have hpos : ∀ j n q, ((if j = i then S.proposeChan i ++ [p] else S.proposeChan j))[n]? = some q →
        (S.proposeChan j)[n]? = some q ∨ (j = i ∧ n = (S.proposeChan i).length ∧ q = p) := by
      intro j n q h
      split at h
      · rename_i hj; subst hj
        by_cases hn : n < (S.proposeChan j).length
        · rw [List.getElem?_append_left hn] at h; exact Or.inl h
        · rw [List.getElem?_append_right (by omega)] at h
          have : n - (S.proposeChan j).length = 0 := by
            cases h' : n - (S.proposeChan j).length with
            | zero => rfl
            | succ k => rw [h'] at h; simp at h
          rw [this] at h; simp at h
          exact Or.inr ⟨rfl, by omega, h.symm⟩
      · exact Or.inl h
    rcases hpos j1 n q h1 with g1 | ⟨e1, e2, e3⟩ <;> rcases hpos j2 m q' h2 with g2 | ⟨e1', e2', e3'⟩
    · exact hX.chanOnce j1 j2 n m q q' g1 g2 h3
    · rw [e3'] at h3; exact absurd h3 (hchanfresh _ _ (List.mem_of_getElem? g1))
    · rw [e3] at h3; exact absurd h3.symm (hchanfresh _ _ (List.mem_of_getElem? g2))
    · rw [e1, e1', e2, e2']; exact ⟨rfl, rfl⟩
  · simp only [upd_apply] at h
    simp only [List.mem_append]
    split at h
    · rename_i hj; subst hj
      rcases List.mem_append.mp h with h | h
      · exact Or.inl (hX.chanOps _ q h)
      · simp only [List.mem_singleton] at h; subst h; right; simp
    · exact Or.inl (hX.chanOps j q h)

/-- The executor starts a component. -/
theorem invExec_execSCC (S : Sys) (i : Nat) (C : List InstId) (h0 : Inv0 S) (hX : InvExec S)
    (hi : i < nR) (hidle : S.idle i) (hC : sccReady (S.rep i) C) : InvExec (S.startSCC i C) := by
  obtain ⟨-, hci⟩ := hidle
  obtain ⟨c1, c2, c3, c4, c5⟩ := hC
  have hes : ∀ r, (S.startSCC i C).eseq r =
      if r = i then S.execLog i ++ sccSort (S.rep i) C else S.eseq r := by
    intro r
    simp only [Sys.eseq, Sys.startSCC, upd_apply]
    split
    · rename_i h; subst h; rfl
    · rfl
  have hold : S.eseq i = S.execLog i := by simp [Sys.eseq, hci]
  have hdE : (S.startSCC i C).dEdge = S.dEdge := rfl
  have hord : (S.startSCC i C).sccOrd = S.sccOrd := rfl
  -- a ready instance's edges are its decided edges
  have hready : ∀ a ∈ C, ∃ w, (S.rep i).inst a = some w ∧ w.status = stCOMMITTED ∧
      S.committedVal a (instVal w) := by
    intro a ha
    obtain ⟨w, hw, hs, hcm⟩ := c3 a ha
    exact ⟨w, hw, hs, ((I0.agr h0).2 i hi a w hw (Or.inl hs)).2⟩
  have hdep : ∀ a ∈ C, ∀ b, S.dEdge a b → (S.rep i).depEdge a b := by
    intro a ha b hab
    obtain ⟨w, hw, -, hcv⟩ := hready a ha
    obtain ⟨v, hv, h1, h2⟩ := hab
    have := I0.uniq h0 hv hcv; subst this
    exact ⟨w, hw, h1, h2⟩
  have hdep' : ∀ a ∈ C, ∀ b, (S.rep i).depEdge a b → S.dEdge a b := by
    intro a ha b hab
    obtain ⟨w, hw, -, hcv⟩ := hready a ha
    obtain ⟨w', hw', h1, h2⟩ := hab
    rw [hw] at hw'; cases hw'
    exact ⟨_, hcv, h1, h2⟩
  have hnotlog : ∀ a ∈ C, a ∉ S.execLog i := by
    intro a ha hl
    obtain ⟨w, hw, hs⟩ := ((I0.ecl h0 i hi).2.1 a).mp hl
    obtain ⟨w', hw', hs', -⟩ := c3 a ha
    rw [hw] at hw'; cases hw'
    rw [hs] at hs'; exact stEX_ne_CO hs'
  have hsorted : (sccSort (S.rep i) C).Pairwise (fun a b => sccLe (S.rep i) a b = true) :=
    List.pairwise_mergeSort (sccLe_trans _) (sccLe_total _) C
  have hsn : (sccSort (S.rep i) C).Nodup := (List.mergeSort_perm C _).nodup_iff.mpr c2
  have hmem : ∀ a, a ∈ sccSort (S.rep i) C ↔ a ∈ C := fun a => List.mem_mergeSort
  have hlexec : ∀ r k, (S.startSCC i C).lexec r k = S.lexec r k := by
    intro r k
    by_cases h : r = i
    · subst h
      simp only [Sys.lexec, Sys.curSlots, Sys.startSCC, upd_same, hci]
      cases sccSort (S.rep r) C <;> simp
    · simp only [Sys.lexec, Sys.curSlots, Sys.startSCC, upd_other _ _ _ _ h]
  refine ⟨fun r hr a b ha hab => ?_, fun r hr l1 l2 a b he h1 h2 ht => ?_,
    fun k e he => ?_, hX.tokSlot, hX.tokChan, hX.chanOnce, hX.chanOps⟩
  · rw [hes] at ha ⊢
    split at ha
    · rename_i h; subst h
      simp only [if_true]
      rcases List.mem_append.mp ha with ha | ha
      · have := hX.reach r hr a b (by rw [hold]; exact ha) hab
        rw [hold] at this; exact List.mem_append_left _ this
      · have haC := (hmem a).mp ha
        rcases c4 a haC b (hdep a haC b hab) with h | h
        · exact List.mem_append_left _ (((I0.ecl h0 r hr).2.1 b).mpr h)
        · exact List.mem_append_right _ ((hmem b).mpr h)
    · rename_i h; simp only [h, if_false]; exact hX.reach r hr a b ha hab
  · rw [hes] at he
    split at he
    · rename_i h; subst h
      have hn : (S.execLog r ++ sccSort (S.rep r) C).Nodup := by
        rw [List.nodup_append]
        refine ⟨(I0.ecl h0 r hr).1, hsn, fun a ha b hb e => ?_⟩
        subst e; exact hnotlog a ((hmem a).mp hb) ha
      have hbef : before (S.execLog r ++ sccSort (S.rep r) C) a b := ⟨l1, l2, he, h1, h2⟩
      have ha' := (before_mem hbef).1
      have hb' := (before_mem hbef).2
      rcases List.mem_append.mp hb' with hbl | hbs
      · -- both logged
        have hal : a ∈ S.execLog r := by
          rcases List.mem_append.mp ha' with h | h
          · exact h
          · exact absurd hbef (fun hb => before_asymm hn hb (before_append hbl h))
        obtain ⟨l1', l2', he', h1', h2'⟩ : before (S.execLog r) a b := by
          obtain ⟨m1, m2, hm, hm1, hm2⟩ := hbef
          rcases List.append_eq_append_iff.mp hm with ⟨xs1, e1, e2⟩ | ⟨bs, e1, e2⟩
          · -- `m1 = log ++ as`: `b ∈ m2` is in the sorted part
            subst e1
            exfalso
            have : b ∈ sccSort (S.rep r) C := by rw [e2]; exact List.mem_append_right _ hm2
            exact hnotlog b ((hmem b).mp this) hbl
          · exact ⟨m1, bs, e1, hm1, by
              rw [e2] at hm2
              rcases List.mem_append.mp hm2 with h | h
              · exact h
              · exact absurd hbl (hnotlog b ((hmem b).mp h))⟩
        exact hX.ord r hr l1' l2' a b (by rw [hold]; exact he') h1' h2' ht
      · have hbC := (hmem b).mp hbs
        rcases List.mem_append.mp ha' with hal | has
        · -- from the log into the component: impossible
          exfalso
          have := reach_tg h0 hX hr (by rw [hold]; exact hal) ht
          rw [hold] at this; exact hnotlog b hbC this
        · have haC := (hmem a).mp has
          have hab : a ≠ b := by intro e; subst e; exact before_irrefl hn hbef
          -- strongly connected: `b` reaches `a`
          have hba : Relation.TransGen S.dEdge b a := by
            rcases c5 b hbC a haC with e | h
            · exact absurd e.symm hab
            · exact tg_mono' (fun c d h => hdep' c h.2.1 d h.1) h
          refine ⟨hba, ?_⟩
          -- the sort: `a` before `b` in the sorted part
          have hbs' : before (sccSort (S.rep r) C) a b := by
            rcases before_or hab has hbs with h | h
            · exact h
            · exact absurd (before_append_right (A := S.execLog r) h)
                (fun hb => before_asymm hn hb hbef)
          have hle := before_pairwise hsorted hbs'
          obtain ⟨wa, hwa, -, hca⟩ := hready a haC
          obtain ⟨wb, hwb, -, hcb⟩ := hready b hbC
          refine ⟨_, _, hca, hcb, ?_⟩
          simp only [sccLe, hwa, hwb, Option.map_some, Option.getD_some, Bool.or_eq_true,
            Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hle
          simp only [instVal]
          rcases hle with h | ⟨e, h⟩
          · left; simpa [BitVec.slt, zz, sint.Z] using h
          · right; refine ⟨e, ?_⟩
            rcases h with h | ⟨e2, h⟩
            · exact Or.inl h
            · exact Or.inr ⟨e2, h⟩
    · rename_i h
      exact hX.ord r hr l1 l2 a b he h1 h2 ht
  · obtain ⟨r, hr, h⟩ := hX.gloc k e he
    exact ⟨r, hr, by rw [hlexec]; exact h⟩

/-- Under `commitMsgs`, decided values are only added when the history only grows. -/
theorem cv_mono {S S' : Sys} (h : Inv.commitMsgs S) (hmono : ∀ r e, S.ev r e → S'.ev r e) :
    ∀ x v, S.committedVal x v → S'.committedVal x v := by
  rintro x v (⟨r, b, h1⟩ | ⟨fr, to, m, hm, hx, rfl⟩)
  · exact Or.inl ⟨r, b, hmono _ _ h1⟩
  · obtain ⟨r, b, he⟩ := h fr to m hm
    simp only [Msg.instOf, Option.some.injEq] at hx
    exact Or.inl ⟨r, b, hmono _ _ (hx ▸ he)⟩

/-- **Frame for the protocol steps.** The history only grows, the executors' state, the global
sequences, owners, channels and ops are kept, the records of executed instances (and of every
instance at a replica executing a component) are kept, and every bookkeeping holding proposals
had them before. -/
theorem invExec_step {S S' : Sys} (h0 : Inv0 S) (hX : InvExec S)
    (hmono : ∀ r e, S.ev r e → S'.ev r e) (hagr : Inv.agreement S')
    (hlog : S'.execLog = S.execLog) (hcur : S'.execCur = S.execCur)
    (hidx : S'.execIdx = S.execIdx) (hg : S'.gexec = S.gexec) (hown : S'.owner = S.owner)
    (hchan : S'.proposeChan = S.proposeChan) (hops : S'.ops = S.ops)
    (hin1 : ∀ r < nR, ∀ y, (S.rep r).executed y → cmdsAt (S'.rep r) y = cmdsAt (S.rep r) y)
    (hin2 : ∀ r < nR, S.execCur r ≠ [] → ∀ y, cmdsAt (S'.rep r) y = cmdsAt (S.rep r) y)
    (hcp : ∀ x w' lb', (S'.rep x.q).inst x = some w' → w'.lb = some lb' →
      lb'.clientProposals ≠ none →
      ∃ w lb, (S.rep x.q).inst x = some w ∧ w.lb = some lb ∧ lb.clientProposals ≠ none) :
    InvExec S' := by
  have hcv := cv_mono (S := S) (S' := S') h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hmono
  refine invExec_frame h0 hX hlog hcur hcv hagr.1 (fun r hr k => ?_) hg hown hchan hops
    (propDead_keep hcv hcp)
  refine lexec_congr S S' r (by rw [hlog]) (by rw [hcur]) (by rw [hidx]) (fun y hy => ?_) k
  rcases List.mem_append.mp hy with h | h
  · exact hin1 r hr y (((I0.ecl h0 r hr).2.1 y).mp h)
  · have : S.execCur r ≠ [] := by intro e; rw [e] at h; cases h
    exact hin2 r hr this y

/-- Frame for the steps that keep every record. -/
theorem invExec_same {S S' : Sys} (h0 : Inv0 S) (hX : InvExec S)
    (hinst : ∀ r, (S'.rep r).inst = (S.rep r).inst) (hmono : ∀ r e, S.ev r e → S'.ev r e)
    (hagr : Inv.agreement S') (hlog : S'.execLog = S.execLog) (hcur : S'.execCur = S.execCur)
    (hidx : S'.execIdx = S.execIdx) (hg : S'.gexec = S.gexec) (hown : S'.owner = S.owner)
    (hchan : S'.proposeChan = S.proposeChan) (hops : S'.ops = S.ops) : InvExec S' :=
  invExec_step h0 hX hmono hagr hlog hcur hidx hg hown hchan hops
    (fun r _ y _ => by simp only [cmdsAt, hinst]) (fun r _ _ y => by simp only [cmdsAt, hinst])
    (fun x w' lb' hw' hlb' hne => ⟨w', lb', by rw [← hinst]; exact hw', hlb', hne⟩)

end ExecOrd

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
