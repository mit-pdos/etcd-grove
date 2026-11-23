/-
The execution-consistency argument (p-modelexec).

Two interfering decided instances are executed in the same order at every replica
(`transfer`): from `depsCover` one reaches the other in the decided graph; the execution
sequences are closed under its edges (`InvExec.reach`) and ordered by it (`InvExec.ord`: what
comes later is not reached, unless it reaches back and is later in `(seq, replica, instance)`
order, which is antisymmetric). Hence a slot executed first anywhere sees the global writes of
its key (`exec_first`), and a slot executed again sees the writes that preceded its first
execution (`exec_again`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.ExecList

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace ExecOrd

/-! ## Accessors -/

section
variable {S : Sys}

theorem I0.wf (h : Inv0 S) : Inv.wf S := h.1
theorem I0.agr (h : Inv0 S) : Inv.agreement S := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem I0.dcv (h : Inv0 S) : Inv.depsCover S := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem I0.ecl (h : Inv0 S) : Inv.execClosed S := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem I0.ecu (h : Inv0 S) : Inv.execCursor S := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem I0.eor (h : Inv0 S) : Inv.execOrder S := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem I0.epf (h : Inv0 S) : Inv.execPrefix S := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem I0.slots (h : Inv0 S) : Inv.slots S := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem I0.cops (h : Inv0 S) : Inv.clientOps S := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem I0.uniq (h : Inv0 S) {x : InstId} {v v' : Val} (h1 : S.committedVal x v)
    (h2 : S.committedVal x v') : v = v' := (I0.agr h).1 x v v' h1 h2

end

theorem stEX_ne_CO : stEXECUTED ≠ stCOMMITTED := by decide

/-! ## The execution sequence -/

section
variable {S : Sys} (h0 : Inv0 S)
include h0

/-- A member of an execution sequence is committed at its replica, with the decided value. -/
theorem eseq_info {r : Nat} (hr : r < nR) {a : InstId} (ha : a ∈ S.eseq r) :
    ∃ w, (S.rep r).inst a = some w ∧ isCommitted w.status ∧ w.cmds ≠ none ∧
      S.committedVal a (instVal w) ∧ a.q < nR := by
  have hfin : ∀ w, (S.rep r).inst a = some w → isCommitted w.status →
      ∃ w', (S.rep r).inst a = some w' ∧ isCommitted w'.status ∧ w'.cmds ≠ none ∧
        S.committedVal a (instVal w') ∧ a.q < nR := by
    intro w hw hs
    obtain ⟨c1, c2⟩ := (I0.agr h0).2 r hr a w hw hs
    exact ⟨w, hw, hs, c1, c2, ((I0.wf h0).2.1 r hr a w hw).2.1⟩
  rcases List.mem_append.mp ha with h | h
  · obtain ⟨w, hw, hs⟩ := ((I0.ecl h0 r hr).2.1 a).mp h
    exact hfin w hw (Or.inr hs)
  · have hne : S.execCur r ≠ [] := List.ne_nil_of_mem h
    obtain ⟨-, -, -, -, -, hrd, -⟩ := ((I0.ecu h0) r hr).2 hne
    obtain ⟨w, hw, hs, -⟩ := hrd a h
    exact hfin w hw (Or.inl hs)

theorem eseq_nodup {r : Nat} (hr : r < nR) : (S.eseq r).Nodup := by
  unfold Sys.eseq
  rw [List.nodup_append]
  refine ⟨(I0.ecl h0 r hr).1, ?_, ?_⟩
  · by_cases hne : S.execCur r = []
    · rw [hne]; exact List.nodup_nil
    · obtain ⟨done, C, h1, h2, -⟩ := ((I0.ecu h0) r hr).2 hne
      have : (sccSort (S.rep r) C).Nodup := (List.mergeSort_perm C _).nodup_iff.mpr h2
      rw [h1] at this
      exact (List.nodup_append.mp this).2.1
  · intro a ha b hb e
    subst e
    obtain ⟨w, hw, hs⟩ := ((I0.ecl h0 r hr).2.1 a).mp ha
    have hne : S.execCur r ≠ [] := List.ne_nil_of_mem hb
    obtain ⟨-, -, -, -, -, hrd, -⟩ := ((I0.ecu h0) r hr).2 hne
    obtain ⟨w', hw', hs', -⟩ := hrd a hb
    rw [hw] at hw'; cases hw'
    rw [hs] at hs'; exact stEX_ne_CO hs'

/-- The commands a replica holds for a member of its execution sequence are the decided ones. -/
theorem cmdsAt_eseq {r : Nat} (hr : r < nR) {a : InstId} (ha : a ∈ S.eseq r) {v : Val}
    (hv : S.committedVal a v) : cmdsAt (S.rep r) a = v.cmds := by
  obtain ⟨w, hw, -, -, hc, -⟩ := eseq_info h0 hr ha
  have := I0.uniq h0 hc hv
  subst this
  simp [cmdsAt, hw, instVal]

theorem cmdsAt_eseq2 {r s : Nat} (hr : r < nR) (hs : s < nR) {a : InstId} (ha : a ∈ S.eseq r)
    (ha' : a ∈ S.eseq s) : cmdsAt (S.rep r) a = cmdsAt (S.rep s) a := by
  obtain ⟨w, -, -, -, hc, -⟩ := eseq_info h0 hr ha
  rw [cmdsAt_eseq h0 hr ha hc, cmdsAt_eseq h0 hs ha' hc]

/-- What comes before the head of the component (or a logged instance) is logged. -/
theorem before_head {r : Nat} (hr : r < nR) {u v : InstId}
    (hv : v ∈ S.execLog r ∨ (S.execCur r).head? = some v) (h : before (S.eseq r) u v) :
    u ∈ S.execLog r := by
  have hn := eseq_nodup h0 hr
  have hu := (before_mem h).1
  rcases List.mem_append.mp hu with h1 | h1
  · exact h1
  · exfalso
    rcases hv with hv | hv
    · exact before_asymm hn h (before_append hv h1)
    · cases hc : S.execCur r with
      | nil => rw [hc] at h1; cases h1
      | cons y rest =>
        rw [hc] at hv h1; simp only [List.head?_cons, Option.some.injEq] at hv; subst hv
        rcases List.mem_cons.mp h1 with h2 | h2
        · subst h2; exact before_irrefl hn h
        · refine before_asymm hn h ⟨S.execLog r ++ [y], rest, ?_, by simp, h2⟩
          simp [Sys.eseq, hc]

theorem lexec_eseq {r : Nat} {e : Slot × WCmd} {k : w64} (he : e ∈ S.lexec r k) :
    e.1.1 ∈ S.eseq r := by
  obtain ⟨-, h | ⟨h, -⟩⟩ := (mem_lexec S r k e).mp he
  · exact List.mem_append_left _ h
  · refine List.mem_append_right _ ?_
    cases hc : S.execCur r with
    | nil => rw [hc] at h; cases h
    | cons y rest => rw [hc] at h; simp only [List.head?_cons, Option.some.injEq] at h; simp [h]

theorem lexec_nodup {r : Nat} (hr : r < nR) (k : w64) : (S.lexec r k).Nodup := by
  refine List.Nodup.sublist (lexec_sublist S r k) (slotsOn_nodup _ k _ ?_)
  refine List.Nodup.sublist ?_ (eseq_nodup h0 hr)
  exact List.Sublist.append_left (List.take_sublist _ _) _

theorem before_lexec {r : Nat} {k : w64} {u v : Slot × WCmd} (h : before (S.lexec r k) u v) :
    (u.1.1 = v.1.1 ∧ u.1.2 < v.1.2) ∨ before (S.eseq r) u.1.1 v.1.1 := by
  rcases before_slotsOn _ _ k u v (before_sublist (lexec_sublist S r k) h) with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (before_sublist (List.Sublist.append_left (List.take_sublist _ _) _) h1)

end

/-! ## Order transfer -/

section
variable {S : Sys} (h0 : Inv0 S) (hX : InvExec S)
include h0 hX

theorem reach_tg {r : Nat} (hr : r < nR) {a b : InstId} (ha : a ∈ S.eseq r)
    (h : Relation.TransGen S.dEdge a b) : b ∈ S.eseq r := by
  induction h with
  | single h => exact hX.reach r hr _ _ ha h
  | tail _ h ih => exact hX.reach r hr _ _ ih h

theorem ord_before {r : Nat} (hr : r < nR) {a b : InstId} (h : before (S.eseq r) a b)
    (ht : Relation.TransGen S.dEdge a b) : Relation.TransGen S.dEdge b a ∧ S.sccOrd a b := by
  obtain ⟨l1, l2, he, h1, h2⟩ := h
  exact hX.ord r hr l1 l2 a b he h1 h2 ht

omit hX in
theorem sccOrd_antisymm {a b : InstId} (h1 : S.sccOrd a b) (h2 : S.sccOrd b a) : a = b := by
  obtain ⟨va, vb, ha, hb, h1⟩ := h1
  obtain ⟨vb', va', hb', ha', h2⟩ := h2
  have e1 := I0.uniq h0 ha ha'
  have e2 := I0.uniq h0 hb hb'
  subst e1 e2
  obtain ⟨q1, i1⟩ := a
  obtain ⟨q2, i2⟩ := b
  simp only [InstId.mk.injEq] at *
  rcases h1 with h1 | ⟨e, h1⟩ <;> rcases h2 with h2 | ⟨e', h2⟩
  · omega
  · rw [e'] at h1; omega
  · rw [e] at h2; omega
  · omega

/-- **Order transfer.** Two interfering decided instances: if `a` is in `r`'s execution sequence,
before `b` or without `b`, then wherever `b` is executed, `a` comes before it. -/
theorem transfer {r s : Nat} (hr : r < nR) (hs : s < nR) {a b : InstId} (hab : a ≠ b)
    (hint : ∃ va vb, S.committedVal a va ∧ S.committedVal b vb ∧ interfere va.cmds vb.cmds)
    (ha : a ∈ S.eseq r) (hrb : b ∉ S.eseq r ∨ before (S.eseq r) a b) (hb : b ∈ S.eseq s) :
    before (S.eseq s) a b := by
  obtain ⟨va, vb, hva, hvb, hi⟩ := hint
  have haq := (eseq_info h0 hr ha).choose_spec.2.2.2.2
  have hbq := (eseq_info h0 hs hb).choose_spec.2.2.2.2
  have hns := eseq_nodup h0 hs
  rcases (I0.dcv h0) a b va vb hab hva hvb hi with hc | hc
  · -- `a → b`
    have hE : S.dEdge a b := ⟨va, hva, hbq, hc⟩
    have hbr : b ∈ S.eseq r := hX.reach r hr a b ha hE
    have hbef : before (S.eseq r) a b := hrb.resolve_left (fun h => h hbr)
    obtain ⟨hba, ho⟩ := ord_before h0 hX hr hbef (.single hE)
    have has : a ∈ S.eseq s := reach_tg h0 hX hs hb hba
    rcases before_or hab has hb with h | h
    · exact h
    · exact absurd (sccOrd_antisymm h0 ho (ord_before h0 hX hs h hba).2) hab
  · -- `b → a`
    have hE : S.dEdge b a := ⟨vb, hvb, haq, hc⟩
    have has : a ∈ S.eseq s := hX.reach s hs b a hb hE
    rcases before_or hab has hb with h | h
    · exact h
    · obtain ⟨hab', ho⟩ := ord_before h0 hX hs h (.single hE)
      have hbr : b ∈ S.eseq r := reach_tg h0 hX hr ha hab'
      have hbef : before (S.eseq r) a b := hrb.resolve_left (fun h => h hbr)
      exact absurd (sccOrd_antisymm h0 (ord_before h0 hX hr hbef hab').2 ho) hab

end

/-! ## The executor's slot -/

theorem mem_writes {l : List (Slot × WCmd)} {z : Slot × WCmd} :
    z ∈ Sys.writes l ↔ z ∈ l ∧ z.2.op = opPUT := by
  simp [Sys.writes]

theorem nodup_of_map {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) : l.Nodup := by
  unfold List.Nodup at *; rw [List.pairwise_map] at h; exact h.imp (fun h e => h (congrArg f e))

theorem gexec_nodup {S : Sys} (h0 : Inv0 S) (k : w64) : (S.gexec k).Nodup :=
  nodup_of_map _ ((I0.cops h0).2.2.1 k)

section
variable {S : Sys} (h0 : Inv0 S) (hX : InvExec S) {i : Nat} {x : InstId} {rest : List InstId}
  {w : InstRec} {idx : Nat} {c : WCmd} (hi : i < nR) (hcur : S.execCur i = x :: rest)
  (hw : (S.rep i).inst x = some w) (hidef : S.execIdx i = idx)
  (hcdef : (w.cmds.getD []).getD idx default = c)
  (hidx : idx < (w.cmds.getD []).length) (hc : c.op ≠ opNONE)
include h0 hX hi hcur hw hidef hcdef hidx hc

omit h0 hX hw hidef hcdef hidx hc in
theorem x_eseq : x ∈ S.eseq i := by simp [Sys.eseq, hcur]

omit h0 hX hcur hidef in
/-- The slot being executed, as a slot of the decided commands. -/
theorem e_slotAt (k : w64) (hk : Sys.touches c k) : slotAt (cmdsAt (S.rep i) x) k ((x, idx), c) := by
  simp only [cmdsAt, hw, Option.bind_some]
  exact ⟨hidx, hcdef.symm, hc, hk⟩

omit hX hi hcur hw hidef hcdef hidx hc in
/-- A slot of a member of two execution sequences is a slot at both. -/
theorem slotAt_move {r s : Nat} (hr : r < nR) (hs : s < nR) {y : InstId} (hy : y ∈ S.eseq r)
    (hy' : y ∈ S.eseq s) {k : w64} {z : Slot × WCmd} (h : slotAt (cmdsAt (S.rep r) y) k z) :
    slotAt (cmdsAt (S.rep s) y) k z := by
  rw [← cmdsAt_eseq2 h0 hr hs hy hy']; exact h

omit hX hidef in
/-- The interference of the executed slot with a PUT of a key it touches (stage 2: a SCAN's range
key by `interfere`'s range clause). -/
theorem slot_interfere (k : w64) (hk : Sys.touches c k) (r : Nat) (hr : r < nR) (z : Slot × WCmd)
    (hy : z.1.1 ∈ S.eseq r)
    (hzs : slotAt (cmdsAt (S.rep r) z.1.1) k z) (hput : z.2.op = opPUT) :
    ∃ va vb, S.committedVal z.1.1 va ∧ S.committedVal x vb ∧ interfere va.cmds vb.cmds := by
  have hxi := x_eseq hi hcur
  obtain ⟨wy, -, -, -, hcy, -⟩ := eseq_info h0 hr hy
  obtain ⟨wx, -, -, -, hcx, -⟩ := eseq_info h0 hi hxi
  refine ⟨_, _, hcy, hcx, ?_⟩
  have hcy' := cmdsAt_eseq h0 hr hy hcy
  have hcx' := cmdsAt_eseq h0 hi hxi hcx
  obtain ⟨z1, z2, z3, z4⟩ := hzs
  obtain ⟨f1, f2, f3, -⟩ := e_slotAt hi hw hcdef hidx hc k hk
  rw [hcy'] at z1 z2
  rw [hcx'] at f1 f2
  simp only at f1 f2
  have hzk : z.2.key = k := by
    rcases z4 with h | ⟨h, -⟩
    · exact h
    · rw [hput] at h; exact absurd h (by decide)
  have m1 : z.2 ∈ (instVal wy).cmds := by
    rw [z2, ← List.getElem_eq_getD (h := z1) default]; exact List.getElem_mem _
  have m2 : c ∈ (instVal wx).cmds := by
    rw [f2, ← List.getElem_eq_getD (h := f1) default]; exact List.getElem_mem _
  rcases hk with hk | ⟨hsc, hk⟩
  · exact ⟨z.2, m1, c, m2, Or.inl ⟨hzk.trans hk.symm, Or.inl hput, z3, f3⟩⟩
  · exact ⟨z.2, m1, c, m2, Or.inr (Or.inr ⟨hput, hsc, hzk ▸ hk⟩)⟩

omit hX hidef in
/-- The slot is in the global sequence once some replica executed it: its instance is logged
there, or is the head there with the slot below the index. -/
theorem e_at_gexec {r : Nat} (hr : r < nR)
    (hx : x ∈ S.execLog r ∨ ((S.execCur r).head? = some x ∧ idx < S.execIdx r)) :
    ((x, idx), c) ∈ S.gexec c.key := by
  have hxr : x ∈ S.eseq r := by
    rcases hx with h | ⟨h, -⟩
    · exact List.mem_append_left _ h
    · refine List.mem_append_right _ ?_
      cases hc' : S.execCur r with
      | nil => rw [hc'] at h; cases h
      | cons y rest => rw [hc'] at h; simp only [List.head?_cons, Option.some.injEq] at h; simp [h]
  have hm : ((x, idx), c) ∈ S.lexec r c.key :=
    (mem_lexec S r _ _).mpr ⟨slotAt_move h0 hi hr (x_eseq hi hcur) hxr
      (e_slotAt hi hw hcdef hidx hc c.key (Or.inl rfl)), hx⟩
  obtain ⟨pre, post, hsp⟩ := List.append_of_mem hm
  obtain ⟨gpre, gpost, hg, -⟩ := (I0.epf h0).2.2 r hr _ pre _ post hsp
  rw [hg]; simp

/-- **First execution.** For every key the slot's command touches, the replica's executed writes
of the key are the global ones (stage 2: per touched key; the stage-1 proof, for `c.key`, is
below). -/
theorem exec_first (hnew : ((x, idx), c) ∉ S.gexec c.key) (k : w64) (hk : Sys.touches c k) :
    Sys.writes (S.gexec k) = Sys.writes (S.lexec i k) := by
  have hxi := x_eseq hi hcur
  refine (prefix_eq_of_mem ((I0.epf h0).1 i hi k) (List.prefix_refl _)
    ((gexec_nodup h0 k).filter _) (fun z => ⟨fun hz => ?_, fun hz => ?_⟩)).symm
  · exact ((I0.epf h0).1 i hi k).subset hz
  · obtain ⟨hzg, hput⟩ := mem_writes.mp hz
    refine mem_writes.mpr ⟨?_, hput⟩
    obtain ⟨r, hr, hzr⟩ := hX.gloc _ z hzg
    obtain ⟨hzs, hzw⟩ := (mem_lexec S r _ z).mp hzr
    have hyr := lexec_eseq h0 hzr
    have hnot : ¬ (x ∈ S.execLog r ∨ ((S.execCur r).head? = some x ∧ idx < S.execIdx r)) :=
      fun h => hnew (e_at_gexec h0 hi hcur hw hcdef hidx hc hr h)
    by_cases hyx : z.1.1 = x
    · -- a slot of the same instance
      rw [hyx] at hzs hzw hyr
      rcases hzw with h | ⟨h1, h2⟩
      · exact absurd (Or.inl h) hnot
      · have hlt : z.1.2 < idx := by
          by_cases hh : idx < S.execIdx r
          · exact absurd (Or.inr ⟨h1, hh⟩) hnot
          · omega
        refine (mem_lexec S i _ z).mpr ⟨?_, Or.inr ⟨by rw [hcur, hyx]; rfl, by rw [hidef]; exact hlt⟩⟩
        rw [hyx]; exact slotAt_move h0 hr hi hyr hxi hzs
    · -- another instance: it comes first at `i`
      have hint := slot_interfere h0 hi hcur hw hcdef hidx hc k hk r hr z hyr hzs hput
      have hrb : x ∉ S.eseq r ∨ before (S.eseq r) z.1.1 x := by
        by_cases hxr : x ∈ S.eseq r
        · rcases before_or hyx hyr hxr with h | h
          · exact Or.inr h
          · exact absurd (Or.inl (before_head h0 hr (hzw.imp id (fun h => h.1)) h)) hnot
        · exact Or.inl hxr
      have hb := transfer h0 hX hr hi hyx hint hyr hrb hxi
      have hlog := before_head h0 hi (Or.inr (by rw [hcur]; rfl)) hb
      exact (mem_lexec S i _ z).mpr ⟨slotAt_move h0 hr hi hyr
        (List.mem_append_left _ hlog) hzs, Or.inl hlog⟩

/-- **Later execution.** For every key the command touches, the slot is in its global sequence
and the writes before it there are the replica's executed writes of the key; its op fired with
the output against the sequences before it (stage 2). -/
theorem exec_again (hold : ((x, idx), c) ∈ S.gexec c.key) :
    (∀ k, Sys.touches c k → ∃ pre post, S.gexec k = pre ++ ((x, idx), c) :: post ∧
      Sys.writes pre = Sys.writes (S.lexec i k)) ∧
      ∀ p, S.slotOp (x, idx) = some p →
        S.fired p.cid = some (Sys.outOf (fun k => Sys.before (S.gexec k) ((x, idx), c)) c) := by
  refine ⟨fun k hk => ?_, fun p hp =>
    ((I0.cops h0).2.2.2.2 p.cid _).mpr ⟨((x, idx), c), p, hold, hp, rfl, rfl⟩⟩
  have hint0 := slot_interfere h0 hi hcur hw hcdef hidx hc k hk
  have hxi := x_eseq hi hcur
  have holdk : ((x, idx), c) ∈ S.gexec k := ((I0.cops h0).2.2.2.1 _ _ hold).2.2.1 k hk
  obtain ⟨r, hr, her⟩ := hX.gloc _ _ holdk
  obtain ⟨pr, po, hsp⟩ := List.append_of_mem her
  obtain ⟨gpre, gpost, hg, hwr⟩ := (I0.epf h0).2.2 r hr _ pr _ po hsp
  have hxr := lexec_eseq h0 her
  obtain ⟨-, hew⟩ := (mem_lexec S r _ _).mp her
  have hnr := lexec_nodup h0 hr k
  have hni := eseq_nodup h0 hi
  have hnr' := eseq_nodup h0 hr
  refine ⟨gpre, gpost, hg, ?_⟩
  rw [← hwr]
  have hpre1 : Sys.writes pr <+: Sys.writes (S.gexec k) := by
    rw [hwr, hg]; simp [Sys.writes, List.filter_append]
  refine prefix_eq_of_mem hpre1 ((I0.epf h0).1 i hi k) ((gexec_nodup h0 k).filter _)
    (fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
  · obtain ⟨hzp, hput⟩ := mem_writes.mp hz
    refine mem_writes.mpr ⟨?_, hput⟩
    have hzr : z ∈ S.lexec r k := by rw [hsp]; exact List.mem_append_left _ hzp
    have hbef : before (S.lexec r k) z ((x, idx), c) := by
      rw [hsp]; exact before_append hzp (by simp)
    obtain ⟨hzs, -⟩ := (mem_lexec S r _ z).mp hzr
    have hyr := lexec_eseq h0 hzr
    rcases before_lexec h0 hbef with ⟨h1, h2⟩ | h1
    · simp only at h1 h2
      refine (mem_lexec S i _ z).mpr ⟨?_, Or.inr ⟨by rw [hcur, h1]; rfl, by rw [hidef]; exact h2⟩⟩
      rw [h1] at hzs hyr ⊢; exact slotAt_move h0 hr hi hyr hxi hzs
    · simp only at h1
      have hyx : z.1.1 ≠ x := by intro e; rw [e] at h1; exact before_irrefl hnr' h1
      have hb := transfer h0 hX hr hi hyx (hint0 r hr z hyr hzs hput) hyr (Or.inr h1) hxi
      have hlog := before_head h0 hi (Or.inr (by rw [hcur]; rfl)) hb
      exact (mem_lexec S i _ z).mpr ⟨slotAt_move h0 hr hi hyr
        (List.mem_append_left _ hlog) hzs, Or.inl hlog⟩
  · obtain ⟨hzi, hput⟩ := mem_writes.mp hz
    refine mem_writes.mpr ⟨?_, hput⟩
    obtain ⟨hzs, hzw⟩ := (mem_lexec S i _ z).mp hzi
    have hyi := lexec_eseq h0 hzi
    -- `z` is executed at `r` before the slot
    suffices hsuf : z ∈ S.lexec r k ∧ before (S.lexec r k) z ((x, idx), c) from
      before_pre hnr hsp hsuf.2
    by_cases hyx : z.1.1 = x
    · have hlt : z.1.2 < idx := by
        rcases hzw with h | ⟨-, h⟩
        · exfalso
          rw [hyx] at h
          exact before_irrefl hni (before_append h (by simp [hcur]))
        · rw [← hidef]; exact h
      have hzr : z ∈ S.lexec r k := by
        refine (mem_lexec S r _ z).mpr ⟨?_, ?_⟩
        · rw [hyx] at hzs hyi ⊢; exact slotAt_move h0 hi hr hyi hxr hzs
        · rw [hyx]
          rcases hew with h | ⟨h1, h2⟩
          · exact Or.inl h
          · exact Or.inr ⟨h1, by simp only at h2; omega⟩
      refine ⟨hzr, ?_⟩
      have hne : z ≠ ((x, idx), c) := by
        intro e; rw [e] at hlt; simp at hlt
      rcases before_or hne hzr her with h | h
      · exact h
      · exfalso
        rcases before_lexec h0 h with ⟨-, h2⟩ | h2
        · simp only at h2; omega
        · simp only at h2; rw [hyx] at h2; exact before_irrefl hnr' h2
    · have hlogi : z.1.1 ∈ S.execLog i := by
        rcases hzw with h | ⟨h, -⟩
        · exact h
        · rw [hcur] at h; simp only [List.head?_cons, Option.some.injEq] at h; exact absurd h.symm hyx
      have hbi : before (S.eseq i) z.1.1 x := before_append hlogi (by simp [hcur])
      have hb := transfer h0 hX hi hr hyx (hint0 i hi z hyi hzs hput) hyi (Or.inr hbi) hxr
      have hlog := before_head h0 hr (hew.imp id (fun h => h.1)) hb
      have hzr : z ∈ S.lexec r k :=
        (mem_lexec S r _ z).mpr ⟨slotAt_move h0 hi hr hyi
          (List.mem_append_left _ hlog) hzs, Or.inl hlog⟩
      refine ⟨hzr, ?_⟩
      have hne : z ≠ ((x, idx), c) := by intro e; rw [e] at hyx; exact hyx rfl
      rcases before_or hne hzr her with h | h
      · exact h
      · exfalso
        rcases before_lexec h0 h with ⟨h1, -⟩ | h2
        · exact hyx h1.symm
        · exact before_asymm hnr' hb h2

end

/-! ## `before` and `lastPut` (the laws `before_eq`, `lastPut_eq_of_writes`) -/

theorem takeWhile_split {α : Type} [DecidableEq α] (pre post : List α) (e : α) (hn : e ∉ pre) :
    (pre ++ e :: post).takeWhile (· ≠ e) = pre := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
    have ha : a ≠ e := fun h => hn (h ▸ List.mem_cons_self ..)
    have hn' : e ∉ pre := fun h => hn (List.mem_cons_of_mem _ h)
    have := ih hn'
    simp only [ne_eq, decide_not] at this
    simp [ha, this]

theorem before_split {S : Sys} (h0 : Inv0 S) (k : w64) (pre post : List (Slot × WCmd))
    (e : Slot × WCmd) (h : S.gexec k = pre ++ e :: post) : Sys.before (S.gexec k) e = pre := by
  have hn := gexec_nodup h0 k
  rw [h] at hn ⊢
  exact takeWhile_split pre post e (fun hm => (List.nodup_append.mp hn).2.2 e hm e (by simp) rfl)

theorem lastPut_foldl_filter (l : List (Slot × WCmd)) (v : Option (List w8)) :
    l.foldl (fun v e => if e.2.op = opPUT then some e.2.val else v) v =
      (Sys.writes l).foldl (fun v e => if e.2.op = opPUT then some e.2.val else v) v := by
  induction l generalizing v with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a.2.op = opPUT
    · simp [Sys.writes, ha, ih] at ih ⊢
    · simp [Sys.writes, ha] at ih ⊢
      exact ih _

theorem lastPut_writes (l : List (Slot × WCmd)) : Sys.lastPut l = Sys.lastPut (Sys.writes l) := by
  unfold Sys.lastPut
  rw [lastPut_foldl_filter l none]

/-! ## `clientOps` frame (for the steps that keep the global sequences and the outputs) -/

/-- A step keeping the ops, the global sequences, the outputs, the ops of the executed slots and
the decided values keeps `Inv.clientOps` (stage 2: for the handler steps' old `hco` blocks). -/
theorem clientOps_frame {S S' : Sys} (h : Inv.clientOps S) (hops : S'.ops = S.ops)
    (hg : S'.gexec = S.gexec) (hf : S'.fired = S.fired)
    (hso : ∀ k e, e ∈ S.gexec k → S'.slotOp e.1 = S.slotOp e.1)
    (hcv : ∀ y v, S.committedVal y v → S'.committedVal y v) : Inv.clientOps S' := by
  obtain ⟨o1, o2, o3, o4, o5⟩ := h
  refine ⟨by rw [hops]; exact o1, ?_, ?_, ?_, ?_⟩
  · intro k k' e e' p p' he he' h1 h2 h3
    rw [hg] at he he'
    rw [hso _ _ he] at h1; rw [hso _ _ he'] at h2
    exact o2 k k' e e' p p' he he' h1 h2 h3
  · intro k; rw [hg]; exact o3 k
  · intro k e he
    rw [hg] at he
    obtain ⟨d1, d2, d0, d3, u, d4, d5⟩ := o4 k e he
    exact ⟨d1, d2, by rw [hg]; exact d0, by rw [hso _ _ he]; exact d3, u, hcv _ _ d4, d5⟩
  · intro cid o
    rw [hf, hg, o5 cid o]
    constructor
    · rintro ⟨e, p, h1, h2, h3, h4⟩
      exact ⟨e, p, h1, by rw [hso _ _ h1]; exact h2, h3, h4⟩
    · rintro ⟨e, p, h1, h2, h3, h4⟩
      exact ⟨e, p, h1, by rw [← hso _ _ h1]; exact h2, h3, h4⟩

end ExecOrd

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
