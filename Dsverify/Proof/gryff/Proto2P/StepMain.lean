/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto2P/StepMain.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit I (stage 2 proofs): `replica_step`'s pure part, assembled (`step_pure`).
-/
module

public import Dsverify.Proof.gryff.Proto2P.Step

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.p2

open model kahn pure dsverify_lab.harness

/-- What `replica_step`'s Iris proof needs of the new state. -/
structure StepOut (S : Inv2St) (k : Fin 3) (e : Ev) (outs : List Out) (S' : Inv2St) : Prop where
  facts : Inv2Facts S'
  grow : ∃ new, S'.linL = S.linL ++ new ∧
    Perennial.gryff.replayOk S.σ (entriesI S.info new) S'.σ ∧
    (∀ x ∈ new, (S.info.lookup x.1).isSome)
  replies : ∀ x ∈ extsIn outs, (x.keyZ, x.out) ∈ S'.linL ∧ repliedIn S'.l1 x.keyZ
  streams : ∀ q, streamOf k q (S'.T k) = streamOf k q (S.T k) ++ sentToR q outs

theorem linEntries_congr {l l' : List Label} {k : Nat} (hl : lin l k = lin l' k)
    (ho : ∀ o, opOut l o = opOut l' o) : linEntries l k = linEntries l' k := by
  unfold linEntries; rw [hl]
  exact List.map_congr_left (fun o _ => by rw [ho o])


/-- The invariant's facts after the step (given the closure's and the clients' parts). -/
theorem step_facts {S : Inv2St} (hf : Inv2Facts S) {ws : Fin 3 → List w64}
    (hP : ∀ i : Fin 3, S.P.lookup i.val = some (some (ws i))) {k : Fin 3} {e : Ev}
    {rest : List w64} (hws : ((S.T k).map evCodec.enc).flatten ++ evCodec.enc e ++ rest = ws k)
    {outs : List Out}
    (hstr : ∀ q, streamOf k q (S.T k ++ [e]) = streamOf k q (S.T k) ++ sentToR q outs)
    {rx' reqs'} (htok : tokStep S k e rx' reqs') {c1 : Cfg gNet}
    (hrun1 : GRun (Cfg.init gNet) (S.l1 ++ [(k, e)]) c1)
    (hreach' : Reach (N := gNet) (decodeT ws) (fun r => (traceSnoc S.T k e r).length))
    {l2' : List Label} {c2' : Cfg gNet} (hR' : GRun (Cfg.init gNet) ((S.l1 ++ [(k, e)]) ++ l2') c2')
    (hproj' : ∀ r : Fin 3, projR ((S.l1 ++ [(k, e)]) ++ l2') r =
      (decodeT ws r).take (close (N := gNet) (decodeT ws) r))
    (hwb' : WB (S.l1 ++ [(k, e)]))
    (hreg' : ∀ o ∈ ops (S.l1 ++ [(k, e)]), ∃ n, S.info.lookup o.idZ = some n ∧ n.input = o.inp) :
    Inv2Facts (stepSt S k e rx' reqs'
      (frontVal (S.l1 ++ [(k, e)]) (S.l1 ++ [(k, e)]).length)
      (linEntries ((S.l1 ++ [(k, e)]) ++ l2') (S.l1 ++ [(k, e)]).length)) := by
  have hreqtok := tokStep_req htok
  have hsub := tokStep_reqs_sub htok
  have hpre : ∀ k0 q : Fin 3, streamOf k0 q (S.T k0) <+: streamOf k0 q (traceSnoc S.T k e k0) := by
    intro k0 q
    by_cases h : k0 = k
    · subst h; rw [traceSnoc_self, hstr q]; exact List.prefix_append _ _
    · rw [traceSnoc_ne _ _ h]; exact List.prefix_refl _
  have hfresh' : ∀ id ki, reqs'.lookup id = some ki →
      ∀ o ∈ ops (S.l1 ++ [(k, e)]), o.idZ ≠ id := by
    intro id ki h o ho
    rcases mem_ops_snoc.1 ho with ho | ho
    · exact hf.reqFresh id ki (hsub id ki h) o ho
    · obtain ⟨-, -, hcr⟩ := newOp_spec ho
      obtain ⟨-, hdel, -⟩ := hreqtok _ _ _ hcr
      rw [hdel, GMap.lookup_delete_iff] at h
      intro hid
      unfold Op.idZ at hid
      rw [hid] at h
      simp at h
  have hws' : ∀ ws0 : Fin 3 → List w64, (∀ i : Fin 3, S.P.lookup i.val = some (some (ws0 i))) →
      ws0 = ws := by
    intro ws0 h0; funext i
    have := h0 i; rw [hP i] at this
    exact (Option.some.inj (Option.some.inj this)).symm
  exact {
    run := ⟨c1, hrun1⟩
    proj := fun r => proj_traceSnoc hf.proj k e r
    predKeys := hf.predKeys
    predPrefix := by
      intro i ws0 h
      have h' : S.P.lookup i.val = some (some ws0) := h
      rw [hP i] at h'; cases h'
      show ∃ rest, ((traceSnoc S.T k e i).map evCodec.enc).flatten ++ rest = ws i
      by_cases hi : i = k
      · subst hi
        refine ⟨rest, ?_⟩
        rw [traceSnoc_self, ← hws]; simp
      · rw [traceSnoc_ne _ _ hi]; exact hf.predPrefix i (ws i) (hP i)
    predNode := hf.predNode
    unset := by
      rintro ⟨i, hi⟩
      have hi' : S.P.lookup i.val = some none := hi
      rw [hP i] at hi'; cases hi'
    closure := by
      intro ws0 h0
      have := hws' ws0 h0; subst this
      exact ⟨hreach', l2', c2', hR', hproj', rfl⟩
    val := rfl
    wb := hwb'
    linNodup := lin_ids_nodup hwb' (Nat.le_refl _)
    reg := hreg'
    reqReg := fun id k0 i h => hf.reqReg id k0 i (hsub _ _ h)
    reqFresh := hfresh'
    binding := by
      intro id k0 hor
      rcases hor with ⟨i, h⟩ | ⟨o, ho, hid, hr⟩
      · exact hf.binding id k0 (Or.inl ⟨i, hsub _ _ h⟩)
      · rcases mem_ops_snoc.1 ho with ho | ho
        · exact hf.binding id k0 (Or.inr ⟨o, ho, hid, hr⟩)
        · obtain ⟨-, hrk, hcr⟩ := newOp_spec ho
          obtain ⟨htk, -⟩ := hreqtok _ _ _ hcr
          refine hf.binding id k0 (Or.inl ⟨o.inp, ?_⟩)
          rw [← hid, ← hr, hrk]; exact htk
    repSet := hf.repSet
    turnsReg := hf.turnsReg
    turnsIdle := fun cid n h r hr =>
      repliedIn_prefix (List.prefix_append _ _) (hf.turnsIdle cid n h r hr)
    turnsBusy := fun cid n h r hne hr =>
      repliedIn_prefix (List.prefix_append _ _) (hf.turnsBusy cid n h r hne hr)
    order := by
      intro cid r1 r2 hlt h1 h2
      obtain ⟨n, hrep, hall⟩ := hf.order cid r1 r2 hlt h1 h2
      refine ⟨n, replyAt_append _ hrep, fun o ho hid => ?_⟩
      rcases mem_ops_snoc.1 ho with ho | ho
      · exact hall o ho hid
      · rw [(newOp_spec ho).1]; exact hrep.1
    budgetKeys := hf.budgetKeys
    budgetSpent := hf.budgetSpent
    reqBudget := by
      intro id k0 i h
      have hr := (grun_init_acc hrun1).1 k0
      have hT : (stepSt S k e rx' reqs' (frontVal (S.l1 ++ [(k, e)]) (S.l1 ++ [(k, e)]).length)
          (linEntries ((S.l1 ++ [(k, e)]) ++ l2') (S.l1 ++ [(k, e)]).length)).T k0 =
          projR (S.l1 ++ [(k, e)]) k0 := (proj_traceSnoc hf.proj k e k0).symm
      rw [hT, stOf_of_runP hr]
      obtain ⟨unit, hu1, hu2⟩ := hf.budgetSpent
      obtain ⟨-, n, hn, -⟩ := hf.reqReg _ _ _ (hsub _ _ h)
      exact reqBudget_of hr hwb'
        (fun o ho => by obtain ⟨n, hn, -⟩ := hreg' o ho; rw [hn]; rfl)
        (by rw [hn]; rfl) (fun o ho => hfresh' id _ h o ho)
        ⟨unit, fun id h => (hu1 id h).1, hu2⟩
    curOk := by
      intro k0 q
      obtain ⟨c, h, hle⟩ := hf.curOk k0 q
      exact ⟨c, h, Nat.le_trans hle (hpre k0 q).length_le⟩
    rxOk := by
      intro k0 q n m h
      obtain ⟨k', q', hk, hq, hn, hm⟩ := hf.rxOk k0 q n m (tokStep_rx_sub htok _ _ h)
      refine ⟨k', q', hk, hq, hn, ?_⟩
      show (streamOf k' q' (traceSnoc S.T k e k'))[n]? = some m
      have hlt : n < (streamOf k' q' (S.T k')).length :=
        (List.getElem?_eq_some_iff.1 hm).1
      rw [prefix_getElem? (hpre k' q') hlt]; exact hm
    recvdOk := by
      intro q
      apply (List.perm_iff_count (α := Msg)).2
      intro m
      show List.count (α := Msg) m (recvdR (traceSnoc S.T k e q)) =
        List.count (α := Msg) m (consumedTo (traceSnoc S.T k e) S.cur rx' q)
      rw [consumed_step hf htok _ hpre q m]
      have hold : List.count (α := Msg) m (recvdR (S.T q)) =
          List.count (α := Msg) m (consumedTo S.T S.cur S.rx q) :=
        (List.perm_iff_count (α := Msg)).1 (hf.recvdOk q) m
      by_cases hq : q = k
      · subst hq
        rw [traceSnoc_self, recvdR_append, List.count_append, hold, if_pos rfl]
      · rw [traceSnoc_ne _ _ hq, hold, if_neg hq, Nat.add_zero] }

/-- **`replica_step`'s pure part.** -/
theorem step_pure {S : Inv2St} (hf : Inv2Facts S) {ws : Fin 3 → List w64}
    (hP : ∀ i : Fin 3, S.P.lookup i.val = some (some (ws i))) {k : Fin 3} {e : Ev}
    {rest : List w64} (hws : ((S.T k).map evCodec.enc).flatten ++ evCodec.enc e ++ rest = ws k)
    {s' : RState} {outs : List Out} (hstep : stepR k (stOf k (S.T k)) e = .ok (s', outs))
    {rx' reqs'} (htok : tokStep S k e rx' reqs') :
    ∃ l2' : List Label, StepOut S k e outs (stepSt S k e rx' reqs'
      (frontVal (S.l1 ++ [(k, e)]) (S.l1 ++ [(k, e)]).length)
      (linEntries ((S.l1 ++ [(k, e)]) ++ l2') (S.l1 ++ [(k, e)]).length)) := by
  obtain ⟨c, hc⟩ := hf.run
  have hrk := real_runP hf hc k
  obtain ⟨-, -, -, hstr⟩ := step_snoc hrk hstep
  -- the consumed message is in flight
  have hrecv : ∀ m, e.recv = some m →
      (recvdR (S.T k)).count m < sum3 (fun r => (streamOf r k (S.T r)).count m) := by
    intro m hm
    rcases htok with ⟨m0, k', n, rfl, hrx, -⟩ | ⟨cid, rid, i, hcr, -⟩ | ⟨hr, -⟩
    · cases hm; exact token_count_lt' hf hrx
    · rw [recv_of_clientReq hcr] at hm; cases hm
    · rw [hr] at hm; cases hm
  obtain ⟨⟨c1, hrun1⟩, hreach', l2', c2', hR', hproj'⟩ := step_closure hf hP hws hstep hrecv
  obtain ⟨-, l2, c', hR, hprojR, hlinL⟩ := hf.closure ws hP
  have hreqtok := tokStep_req htok
  have hwb' : WB (S.l1 ++ [(k, e)]) :=
    wb_snoc hf hR (fun cid rid i h => (hreqtok cid rid i h).1)
  refine ⟨l2', ?_⟩
  -- notation
  have hlen : (S.l1 ++ [(k, e)]).length = S.l1.length + 1 := by simp
  have hL' : (S.l1 ++ [(k, e)]) ++ l2' = S.l1 ++ ([(k, e)] ++ l2') := List.append_assoc ..
  -- registrations of the new history's operations
  have hreg' : ∀ o ∈ ops (S.l1 ++ [(k, e)]), ∃ n, S.info.lookup o.idZ = some n ∧ n.input = o.inp := by
    intro o ho
    rcases mem_ops_snoc.1 ho with ho | ho
    · exact hf.reg o ho
    · obtain ⟨-, -, hcr⟩ := newOp_spec ho
      obtain ⟨-, n, hn, hi⟩ := hf.reqReg _ _ _ (hreqtok _ _ _ hcr).1
      exact ⟨n, hn, hi⟩
  -- the old linearization, in the new run
  have hcong := lin_congr_proj (l := S.l1 ++ l2) (l' := (S.l1 ++ [(k, e)]) ++ l2')
    (k := S.l1.length) (by rw [hL', List.take_left, List.take_left])
    (fun r => by rw [hprojR r, hproj' r])
  have hlin0 : S.linL = linEntries ((S.l1 ++ [(k, e)]) ++ l2') S.l1.length := by
    rw [hlinL]; exact linEntries_congr hcong.1 hcong.2.2.2
  obtain ⟨B, hB⟩ := lin_prefix hR' hwb' (Nat.le_succ S.l1.length) (by rw [hlen]; exact Nat.le_refl _)
  -- the new entries and their replay
  have hrep1 := lin_replay hR' hwb' (k := S.l1.length) (by rw [hlen]; exact Nat.le_succ _)
  have hrep2 := lin_replay hR' hwb' (k := S.l1.length + 1) (by rw [hlen]; exact Nat.le_refl _)
  rw [← hB, List.map_append] at hrep2
  have hrep := replayOk_split _ _ _ _ _ hrep2 hrep1
  have hf1 : frontVal ((S.l1 ++ [(k, e)]) ++ l2') S.l1.length = S.σ := by
    rw [hL', frontVal_append, ← hf.val]
  have hf2 : frontVal ((S.l1 ++ [(k, e)]) ++ l2') (S.l1.length + 1) =
      frontVal (S.l1 ++ [(k, e)]) (S.l1 ++ [(k, e)]).length := by
    rw [← hlen, frontVal_append]
  rw [hf1, hf2] at hrep
  have hBreg : ∀ o ∈ B, ∃ n, S.info.lookup o.idZ = some n ∧ n.input = o.inp := by
    intro o ho
    have hmem : o ∈ lin ((S.l1 ++ [(k, e)]) ++ l2') (S.l1.length + 1) := by
      rw [← hB]; exact List.mem_append_right _ ho
    obtain ⟨ho1, ho2⟩ := lin_mem_ops hmem
    exact hreg' o (ops_of_append ho1 (by rw [hlen]; exact ho2))
  -- the replies
  have houts : extsAt (S.l1 ++ [(k, e)]) S.l1.length = extsIn outs := by
    unfold extsAt
    rw [outsAt_last, hf.proj k, hstep]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left
  · -- the linearization grows
    refine ⟨B.map fun o => (o.idZ, opOut ((S.l1 ++ [(k, e)]) ++ l2') o), ?_, ?_, ?_⟩
    · show linEntries _ _ = _
      rw [hlin0, hlen]; unfold linEntries; rw [← hB, List.map_append]
    · show Perennial.gryff.replayOk S.σ _ (frontVal (S.l1 ++ [(k, e)]) (S.l1 ++ [(k, e)]).length)
      rw [entriesI_map _ _ B hBreg, ← replayOk_iff]; exact hrep
    · intro x hx
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx
      obtain ⟨n, hn, -⟩ := hBreg o ho
      show (S.info.lookup o.idZ).isSome
      rw [hn]; rfl
  · -- the replies are linearized, and in the history
    intro x hx
    have hx' : x ∈ extsAt ((S.l1 ++ [(k, e)]) ++ l2') S.l1.length := by
      rw [extsAt_append _ _ (by rw [hlen]; exact Nat.lt_succ_self _), houts]; exact hx
    obtain ⟨o, -, -, -, hkey, -, hol, hout⟩ := lin_reply hR' hwb' (by rw [hlen]; exact Nat.lt_succ_self _) hx'
    refine ⟨?_, ⟨S.l1.length, ?_, x, ?_, rfl⟩⟩
    rotate_left
    · show S.l1.length < (S.l1 ++ [(k, e)]).length
      rw [hlen]; exact Nat.lt_succ_self _
    · show x ∈ extsAt (S.l1 ++ [(k, e)]) S.l1.length
      rw [houts]; exact hx
    show (x.keyZ, x.out) ∈ linEntries _ _
    rw [hlen]
    unfold linEntries
    refine List.mem_map.2 ⟨o, hol, ?_⟩
    rw [keyZ_eq hkey, hout]
  · -- the streams
    intro q
    show streamOf k q (traceSnoc S.T k e k) = _
    rw [traceSnoc_self]; exact hstr q
  · exact step_facts hf hP hws hstr htok hrun1 hreach' hR' hproj' hwb' hreg'

end Perennial.gryff.p2
