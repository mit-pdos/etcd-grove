/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto2P/Lin.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit I (stage 2 proofs): well-behaved clients across a step (`wb_snoc`), the linearization's ids,
the frontier of a run's real prefix, and replays.
-/
module

public import Dsverify.Proof.gryff.Proto2P.Closure

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.p2

open model kahn pure dsverify_lab.harness

/-! ## Replays -/

theorem replayOk_iff : ∀ (s : w64) (L : List (RegInput w64 × RegOutput w64)) (s' : w64),
    pure.replayOk s L s' ↔ Perennial.gryff.replayOk s L s'
  | s, [], s' => Iff.rfl
  | s, (i, o) :: L, s' => by
    simp only [pure.replayOk, Perennial.gryff.replayOk]
    rw [replayOk_iff _ L s']

theorem replayOk_split : ∀ (s : w64) (A B : List (RegInput w64 × RegOutput w64)) (s1 s2 : w64),
    pure.replayOk s (A ++ B) s2 → pure.replayOk s A s1 → pure.replayOk s1 B s2
  | s, [], B, s1, s2, h, h1 => by
    simp only [pure.replayOk] at h1; subst h1; exact h
  | s, (i, o) :: A, B, s1, s2, h, h1 => by
    simp only [List.cons_append, pure.replayOk] at h h1
    exact replayOk_split _ A B s1 s2 h.2 h1.2

/-- The registered inputs of linearized entries (stage 1's `entries`, over the registrations). -/
def entriesI (info : GMap proto.OpId OpInfo) (L : List (proto.OpId × RegOutput w64)) :
    List (RegInput w64 × RegOutput w64) :=
  L.filterMap (fun x => (info.lookup x.1).map (fun n => (n.input, x.2)))

theorem entriesI_map (info : GMap proto.OpId OpInfo) (l : List Label) :
    ∀ (B : List Op), (∀ o ∈ B, ∃ n, info.lookup o.idZ = some n ∧ n.input = o.inp) →
      entriesI info (B.map fun o => (o.idZ, opOut l o)) = B.map fun o => (o.inp, opOut l o)
  | [], _ => rfl
  | o :: B, h => by
    obtain ⟨n, hn, hi⟩ := h o (List.mem_cons_self ..)
    have ih := entriesI_map info l B (fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))
    unfold entriesI at ih ⊢
    rw [List.map_cons, List.filterMap_cons]
    simp only [hn, Option.map_some, hi, ih, List.map_cons]

/-! ## The frontier of a run's prefix -/

theorem cutSt_append (l l' : List Label) : cutSt (l ++ l') l.length = cutSt l l.length := by
  funext r
  unfold cutSt
  rw [List.take_left, List.take_length]

theorem frontVal_append (l l' : List Label) :
    frontVal (l ++ l') l.length = frontVal l l.length := by
  unfold frontVal front
  rw [cutSt_append]

/-! ## The linearization's ids -/

theorem lin_mem_ops {l : List Label} {k : Nat} {o : Op} (h : o ∈ lin l k) :
    o ∈ ops l ∧ o.g < k := by
  unfold lin at h
  have := (List.mergeSort_perm _ _).mem_iff.1 h
  rw [List.mem_filter] at this
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1, this.2.1⟩

theorem lin_ids_nodup {l1 l2 : List Label} (hwb : WB l1) {k : Nat} (hk : k ≤ l1.length) :
    ((linEntries (l1 ++ l2) k).map Prod.fst).Nodup := by
  unfold linEntries
  rw [List.map_map]
  unfold lin
  have hperm := List.mergeSort_perm ((ops (l1 ++ l2)).filter fun o =>
    decide (o.g < k) && placeLe (l1 ++ l2) o (front (l1 ++ l2) k)) (opLe (l1 ++ l2))
  refine ((hperm.map _).nodup_iff).2 ?_
  have hp := (ops_pairwise (l1 ++ l2)).filter (fun o =>
    decide (o.g < k) && placeLe (l1 ++ l2) o (front (l1 ++ l2) k))
  apply List.pairwise_map.2
  refine List.Pairwise.imp_of_mem ?_ hp
  intro a b ha hb hab heq
  rw [List.mem_filter] at ha hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ha hb
  have ha' := ops_of_append ha.1 (by omega)
  have hb' := ops_of_append hb.1 (by omega)
  simp only [Function.comp, Op.idZ, Prod.mk.injEq] at heq
  have := hwb.1 a ha' b hb' (sintZ_inj heq.1) (sintZ_inj heq.2)
  omega

/-! ## Well-behaved clients across a step -/

theorem idZ_eq {o : Op} {cid rid : w32} (h1 : o.cid = cid) (h2 : o.rid = rid) :
    o.idZ = (sint.Z cid, sint.Z rid) := by
  unfold Op.idZ; rw [h1, h2]

theorem keyZ_eq {x : Ext} {o : Op} (h : (o.cid, o.rid) = x.key) : x.keyZ = o.idZ := by
  unfold Ext.keyZ Op.idZ; rw [← h]

/-- A reply within the real history is to an operation handled in it. -/
theorem reply_handled {S : Inv2St} (hf : Inv2Facts S) {l2 : List Label} {c : Cfg gNet}
    (h2 : GRun (Cfg.init gNet) (S.l1 ++ l2) c) {n : Nat} {id : proto.OpId}
    (hr : replyAt S.l1 n id) :
    ∃ o ∈ ops S.l1, o.idZ = id ∧ o.g < n ∧ (S.l1[n]?).map Prod.fst = some o.r ∧
      ∃ x ∈ extsAt S.l1 n, x.key = (o.cid, o.rid) := by
  obtain ⟨hn, x, hx, hk⟩ := hr
  have hx' : x ∈ extsAt (S.l1 ++ l2) n := by rw [extsAt_append _ _ hn]; exact hx
  obtain ⟨o, ho, hg, hr, hkey, -⟩ := lin_reply h2 hf.wb hn hx'
  refine ⟨o, ops_of_append ho (by omega), ?_, hg, ?_, x, hx, hkey.symm⟩
  · rw [← keyZ_eq hkey]; exact hk
  · rw [List.getElem?_append_left hn] at hr; exact hr

/-- **Well-behaved clients across a step**: a client request's key is fresh (its token), and an
earlier request of the same client id is at the same replica and replied to before (the
bindings, the order of registrations). -/
theorem wb_snoc {S : Inv2St} (hf : Inv2Facts S) {l2 : List Label} {c : Cfg gNet}
    (h2 : GRun (Cfg.init gNet) (S.l1 ++ l2) c) {k : Fin 3} {e : Ev}
    (htok : ∀ cid rid i, e.clientReq = some (cid, rid, i) →
      S.reqs.lookup (sint.Z cid, sint.Z rid) = some (k.val, i)) :
    WB (S.l1 ++ [(k, e)]) := by
  -- the new operation, if any, is fresh
  have hnew : ∀ o', newOp S.l1 k e = some o' →
      S.reqs.lookup o'.idZ = some (k.val, o'.inp) ∧ ∀ o ∈ ops S.l1, o.idZ ≠ o'.idZ := by
    intro o' h'
    obtain ⟨-, -, hc⟩ := newOp_spec h'
    have ht := htok _ _ _ hc
    refine ⟨ht, fun o ho => hf.reqFresh _ _ ht o ho⟩
  refine ⟨?_, ?_⟩
  · intro o ho o' ho' hc hr
    rcases mem_ops_snoc.1 ho with ho | ho <;> rcases mem_ops_snoc.1 ho' with ho' | ho'
    · exact hf.wb.1 o ho o' ho' hc hr
    · exact absurd (by unfold Op.idZ; rw [hc, hr]) ((hnew o' ho').2 o ho)
    · exact absurd (by unfold Op.idZ; rw [hc, hr]) ((hnew o ho).2 o' ho')
    · rw [ho] at ho'; cases ho'; rfl
  · intro o ho o' ho' hc hlt
    rcases mem_ops_snoc.1 ho' with ho' | ho'
    · -- both old
      rcases mem_ops_snoc.1 ho with ho | ho
      · obtain ⟨hr, n, hn, hrep⟩ := hf.wb.2 o ho o' ho' hc hlt
        exact ⟨hr, n, hn, RepliesTo_append _ hrep⟩
      · have := (newOp_spec ho).1; have := ops_g_lt ho'; omega
    · obtain ⟨hg', hr', hc'⟩ := newOp_spec ho'
      rcases mem_ops_snoc.1 ho with ho | ho
      rotate_left
      · have := (newOp_spec ho).1; omega
      obtain ⟨htk, hfr⟩ := hnew o' ho'
      -- same replica: one connection per client id, one replica per connection
      have hrk : o.r = k := by
        obtain ⟨hs, conn, n, h1, h2, -, -, h4⟩ := hf.binding o'.idZ k.val (Or.inl ⟨_, htk⟩)
        obtain ⟨hs', conn', n', h1', h2', -, -, h4'⟩ :=
          hf.binding o.idZ o.r.val (Or.inr ⟨o, ho, rfl, rfl⟩)
        have hh : hs = hs' := by
          apply sintZ_inj
          rw [← h1, ← h1']; unfold Op.idZ; rw [hc]
        subst hh
        rw [h2] at h2'; cases h2'
        rw [h4] at h4'
        exact Fin.ext (Option.some.inj h4').symm
      refine ⟨by rw [hrk, hr'], ?_⟩
      have hreg : (S.info.lookup o.idZ).isSome := by
        obtain ⟨n, hn, -⟩ := hf.reg o ho; rw [hn]; rfl
      have hreg' : (S.info.lookup o'.idZ).isSome := by
        obtain ⟨-, n, hn, -⟩ := hf.reqReg _ _ _ htk; rw [hn]; rfl
      rcases Int.lt_trichotomy (sint.Z o.rid) (sint.Z o'.rid) with hlt' | heq | hgt
      · obtain ⟨n, hrep, -⟩ := hf.order (sint.Z o.cid) _ _ hlt' hreg
          (by unfold Op.idZ at hreg'; rw [hc]; exact hreg')
        obtain ⟨o'', ho'', hid, hg, hr, x, hx, hk⟩ := reply_handled hf h2 hrep
        have hcr : o''.cid = o.cid ∧ o''.rid = o.rid := by
          unfold Op.idZ at hid; simp only [Prod.mk.injEq] at hid
          exact ⟨sintZ_inj hid.1, sintZ_inj hid.2⟩
        have hgg := hf.wb.1 o'' ho'' o ho hcr.1 hcr.2
        have heo := ops_g_inj ho'' ho hgg
        subst heo
        refine ⟨n, by rw [hg']; exact hrep.1, hg, ?_, x, ?_, hk⟩
        · rw [List.getElem?_append_left hrep.1]; exact hr
        · rw [extsAt_append _ _ hrep.1]; exact hx
      · exact absurd (by unfold Op.idZ; rw [hc, heq]) (hfr o ho)
      · obtain ⟨n, hrep, -⟩ := hf.order (sint.Z o.cid) _ _ hgt
          (by unfold Op.idZ at hreg'; rw [hc]; exact hreg') hreg
        obtain ⟨o'', ho'', hid, -⟩ := reply_handled hf h2 hrep
        exact absurd (by rw [hid]; unfold Op.idZ; rw [hc]) (hfr o'' ho'')

end Perennial.gryff.p2
