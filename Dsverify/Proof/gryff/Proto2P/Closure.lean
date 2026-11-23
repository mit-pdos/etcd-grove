/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto2P/Closure.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit I (stage 2 proofs): `replica_step`'s closure (`notes/stage2-interface-I.md` §4.7): the
step's event is the next predicted one and enabled, so the new history is a run whose positions
are reachable in the (fixed) predicted traces, and it extends to their closure.
-/
module

public import Dsverify.Proof.gryff.Proto2P.Model

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.p2

open model kahn pure

/-- The messages consumed in `t` (Kahn's `recvd` at the model, typed over `Msg`). -/
def recvdR (t : List Ev) : List Msg := t.filterMap Ev.recv

theorem recvdR_append (t t' : List Ev) : recvdR (t ++ t') = recvdR t ++ recvdR t' := by
  unfold recvdR; exact List.filterMap_append

theorem recvdR_single (e : Ev) : recvdR [e] = (e.recv.map (fun x => [x])).getD [] := by
  unfold recvdR; rw [List.filterMap_cons, List.filterMap_nil]; cases e.recv <;> rfl

theorem token_count_lt' {S : Inv2St} (hf : Inv2Facts S) {k' q : Fin 3} {n : Nat} {m : Msg}
    (hrx : S.rx.lookup (k'.val, q.val, n) = some m) :
    (recvdR (S.T q)).count m < sum3 (fun k => (streamOf k q (S.T k)).count m) :=
  token_count_lt hf hrx

/-- The traces after replica `k`'s step on `e`. -/
def traceSnoc (T : Fin 3 → List Ev) (k : Fin 3) (e : Ev) : Fin 3 → List Ev :=
  fun r => if r = k then T k ++ [e] else T r

theorem traceSnoc_self (T : Fin 3 → List Ev) (k : Fin 3) (e : Ev) :
    traceSnoc T k e k = T k ++ [e] := by simp [traceSnoc]

theorem traceSnoc_ne (T : Fin 3 → List Ev) {k r : Fin 3} (e : Ev) (h : r ≠ k) :
    traceSnoc T k e r = T r := by simp [traceSnoc, h]

theorem proj_traceSnoc {l : List Label} {T : Fin 3 → List Ev} (hp : ∀ r, projR l r = T r)
    (k : Fin 3) (e : Ev) (r : Fin 3) : projR (l ++ [(k, e)]) r = traceSnoc T k e r := by
  rw [proj_snoc, hp]
  by_cases h : r = k
  · subst h; simp [traceSnoc]
  · simp [traceSnoc, h]

/-- The predicted traces extend the real ones. -/
theorem decodeT_prefix {S : Inv2St} (hf : Inv2Facts S) {ws : Fin 3 → List w64}
    (hP : ∀ i : Fin 3, S.P.lookup i.val = some (some (ws i))) (i : Fin 3) :
    decodeT ws i = S.T i ++ evCodec.decodeAll ((hf.predPrefix i (ws i) (hP i)).choose) := by
  have h := (hf.predPrefix i (ws i) (hP i)).choose_spec
  unfold decodeT
  conv => lhs; rw [← h]
  exact evCodec.decodeAll_enc (S.T i) _

theorem decodeT_snoc {ws : Fin 3 → List w64} {t : List Ev} {k : Fin 3} {e : Ev} {rest : List w64}
    (h : (t.map evCodec.enc).flatten ++ evCodec.enc e ++ rest = ws k) :
    decodeT ws k = t ++ [e] ++ evCodec.decodeAll rest := by
  unfold decodeT
  rw [← h]
  have : (t.map evCodec.enc).flatten ++ evCodec.enc e ++ rest =
      ((t ++ [e]).map evCodec.enc).flatten ++ rest := by simp
  rw [this]
  exact evCodec.decodeAll_enc (t ++ [e]) rest

/-- The real configuration's states run the traces. -/
theorem real_runP {S : Inv2St} (hf : Inv2Facts S) {c : Cfg gNet}
    (hc : GRun (Cfg.init gNet) S.l1 c) (k : Fin 3) :
    runP gNet k (S.T k) = some (c.st k, outsP k (S.T k)) := by
  have := (grun_init_acc hc).1 k
  rw [hf.proj k] at this; exact this

theorem real_stOf {S : Inv2St} (hf : Inv2Facts S) {c : Cfg gNet}
    (hc : GRun (Cfg.init gNet) S.l1 c) (k : Fin 3) : stOf k (S.T k) = c.st k :=
  stOf_of_runP (real_runP hf hc k)

/-- A message the replica consumes is in flight in the real configuration. -/
theorem real_inflight {S : Inv2St} (hf : Inv2Facts S) {c : Cfg gNet}
    (hc : GRun (Cfg.init gNet) S.l1 c) {q : Fin 3} {m : Msg}
    (hlt : (recvdR (S.T q)).count m < sum3 (fun k => (streamOf k q (S.T k)).count m)) :
    m ∈ c.inflight q := by
  apply inflight_of_count hc
  erw [hf.proj q, sumN_gNet]
  have : ∀ k, (streamOf k q (projR S.l1 k)).count m = (streamOf k q (S.T k)).count m := by
    intro k; rw [hf.proj k]
  erw [sum3_congr this]; exact hlt

/-- **The closure across a step**: the new history is a run, its positions are reachable in the
predicted traces, and it extends to their closure. -/
theorem step_closure {S : Inv2St} (hf : Inv2Facts S) {ws : Fin 3 → List w64}
    (hP : ∀ i : Fin 3, S.P.lookup i.val = some (some (ws i))) {k : Fin 3} {e : Ev}
    {rest : List w64} (hws : ((S.T k).map evCodec.enc).flatten ++ evCodec.enc e ++ rest = ws k)
    {s' : RState} {outs : List Out} (hstep : stepR k (stOf k (S.T k)) e = .ok (s', outs))
    (hrecv : ∀ m, e.recv = some m →
      (recvdR (S.T k)).count m < sum3 (fun r => (streamOf r k (S.T r)).count m)) :
    (∃ c1, GRun (Cfg.init gNet) (S.l1 ++ [(k, e)]) c1) ∧
      Reach (N := gNet) (decodeT ws) (fun r => (traceSnoc S.T k e r).length) ∧
      ∃ (l2 : List Label) (c : Cfg gNet), GRun (Cfg.init gNet) ((S.l1 ++ [(k, e)]) ++ l2) c ∧
        ∀ r : Fin 3, projR ((S.l1 ++ [(k, e)]) ++ l2) r =
          (decodeT ws r).take (close (N := gNet) (decodeT ws) r) := by
  obtain ⟨c, hc⟩ := hf.run
  obtain ⟨hreach, -⟩ := hf.closure ws hP
  have hstep' : stepR k (c.st k) e = .ok (s', outs) := by rw [← real_stOf hf hc k]; exact hstep
  -- the new global step
  let c1 : Cfg gNet := ⟨fun (j : Fin 3) => if j = k then s' else c.st j,
    fun (j : Fin 3) => (if j = k then consume (gNet.recv e) (c.inflight j) else c.inflight j) ++
      sentTo gNet j outs⟩
  have hgs : ∃ x, GStep c k e c1 x := by
    refine ⟨_, s', outs, gStep_ok hstep', fun m hm => ?_, rfl, (by rfl), (by rfl)⟩
    exact real_inflight hf hc (hrecv m hm)
  obtain ⟨x, hgs⟩ := hgs
  have hrun1 : GRun (Cfg.init gNet) (S.l1 ++ [(k, e)]) c1 := grun_snoc hc hgs
  -- the event is the next predicted one, and enabled
  have hdk := decodeT_snoc hws
  have hpre : ∀ r, traceSnoc S.T k e r <+: decodeT ws r := by
    intro r
    by_cases h : r = k
    · subst h; rw [traceSnoc_self, hdk]; exact List.prefix_append _ _
    · rw [traceSnoc_ne _ _ h, decodeT_prefix hf hP r]; exact List.prefix_append _ _
  have htake : ∀ r, (decodeT ws r).take (S.T r).length = S.T r := by
    intro r
    by_cases h : r = k
    · subst h; rw [hdk, List.append_assoc]; exact List.take_left
    · rw [decodeT_prefix hf hP r]; exact List.take_left
  have hen : Enabled (N := gNet) (decodeT ws) (fun r => (S.T r).length) k := by
    refine ⟨e, ?_, c.st k, outsP k (S.T k), ?_, ?_, ?_⟩
    · show (decodeT ws k)[(S.T k).length]? = some e
      rw [hdk, List.append_assoc]; simp
    · show runP gNet k ((decodeT ws k).take (S.T k).length) = _
      erw [htake k]; exact real_runP hf hc k
    · rw [gStep_ok hstep']; rfl
    · intro (m : Msg) hm
      have hm' : e.recv = some m := hm
      have h1 : (decodeT ws k).take ((S.T k).length + 1) = S.T k ++ [e] := by
        rw [hdk, List.take_left' (by simp)]
      have hcore : (recvdR (S.T k ++ [e])).count m ≤
          sum3 (fun r => (streamOf r k (S.T r)).count m) := by
        have h2 := hrecv m hm'
        rw [recvdR_append, List.count_append, recvdR_single, hm']
        simp only [Option.map_some, Option.getD_some, List.count_singleton_self]
        omega
      have hout : ∀ r : Fin 3, kahn.outsAt (N := gNet) (decodeT ws) r (S.T r).length =
          outsP r (S.T r) := by
        intro r
        have := congrArg (fun t => ((runP gNet r t).map Prod.snd).getD []) (htake r)
        exact this
      have hb : sentCount (N := gNet) (decodeT ws) (fun r => (S.T r).length) k m =
          sum3 (fun r => (streamOf r k (S.T r)).count m) := by
        refine (sentCount_eq _ _ _ _).trans ?_; apply sum3_congr; intro r
        rw [hout r]; exact rfl
      have ha : (recvd gNet ((decodeT ws k).take ((S.T k).length + 1))).count m =
          (recvdR (S.T k ++ [e])).count m :=
        congrArg (fun t => (recvdR t).count m) h1
      calc _ = _ := ha
        _ ≤ _ := hcore
        _ = _ := hb.symm
  have hreach' : Reach (N := gNet) (decodeT ws) (fun r => (traceSnoc S.T k e r).length) := by
    have hfun : bump (N := gNet) (fun r => (S.T r).length) k =
        (fun (r : Fin 3) => (traceSnoc S.T k e r).length) := by
      funext r
      unfold bump traceSnoc
      by_cases h : r = k
      · erw [ite_cond_eq_true _ _ (eq_true h), ite_cond_eq_true _ _ (eq_true h)]; subst h; simp
      · erw [ite_cond_eq_false _ _ (eq_false h), ite_cond_eq_false _ _ (eq_false h)]
    exact hfun ▸ Reach.step hreach hen
  refine ⟨⟨c1, hrun1⟩, hreach', ?_⟩
  obtain ⟨l2, c2, h2, hp2⟩ := reach_extend (T := decodeT ws) hrun1
    (p := fun r => (traceSnoc S.T k e r).length)
    (fun r => by
      have h := proj_traceSnoc hf.proj k e r
      obtain ⟨u, hu⟩ := hpre r
      have h' : traceSnoc S.T k e r = (decodeT ws r).take (traceSnoc S.T k e r).length := by
        rw [← hu]; exact List.take_left.symm
      exact h.trans h')
    (close_reach _) (close_ge hreach')
  exact ⟨l2, c2, grun_append.2 ⟨c1, hrun1, h2⟩, hp2⟩

end Perennial.gryff.p2
