/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto2P/Step.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit I (stage 2 proofs): **`replica_step`'s pure part**: the invariant's facts hold of the state
after replica `k`'s step on `e` (the trace and the history extended, the event's token consumed,
the register at the new frontier's value, the linearization at the new cut), and the data the
Iris proof needs (the linearization grows by entries whose replay goes from the old register to
the new one; the step's replies are linearized and in the history; the streams grow by the step's
messages).
-/
module

public import Dsverify.Proof.gryff.Proto2P.Lin

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.p2

open model kahn pure dsverify_lab.harness

/-- The invariant's state after replica `k`'s step on `e`. -/
def stepSt (S : Inv2St) (k : Fin 3) (e : Ev) (rx' : GMap (Nat × Nat × Nat) Msg)
    (reqs' : GMap proto.OpId (Nat × RegInput w64)) (σ' : w64)
    (linL' : List (proto.OpId × RegOutput w64)) : Inv2St :=
  ⟨traceSnoc S.T k e, S.l1 ++ [(k, e)], S.P, S.NP, S.idNode, S.B, σ', linL', S.info, S.turns,
    S.conns, S.placers, S.connRep, S.cur, rx', reqs'⟩

/-- The event's token consumed: a message's receive token, a client request's token, or none. -/
def tokStep (S : Inv2St) (k : Fin 3) (e : Ev) (rx' : GMap (Nat × Nat × Nat) Msg)
    (reqs' : GMap proto.OpId (Nat × RegInput w64)) : Prop :=
  (∃ (m : Msg) (k' : Fin 3) (n : Nat), e = .msg m ∧ S.rx.lookup (k'.val, k.val, n) = some m ∧
    rx' = S.rx.delete (k'.val, k.val, n) ∧ reqs' = S.reqs) ∨
  (∃ cid rid i, e.clientReq = some (cid, rid, i) ∧
    S.reqs.lookup (sint.Z cid, sint.Z rid) = some (k.val, i) ∧
    reqs' = S.reqs.delete (sint.Z cid, sint.Z rid) ∧ rx' = S.rx) ∨
  (e.recv = none ∧ e.clientReq = none ∧ rx' = S.rx ∧ reqs' = S.reqs)

theorem clientReq_msg (m : Msg) : (Ev.msg m).clientReq = none := rfl

theorem recv_of_clientReq {e : Ev} {x : w32 × w32 × RegInput w64} (h : e.clientReq = some x) :
    e.recv = none := by
  cases e <;> first | rfl | (simp [Ev.clientReq] at h)

theorem tokStep_req {S : Inv2St} {k : Fin 3} {e : Ev} {rx' reqs'}
    (h : tokStep S k e rx' reqs') :
    ∀ cid rid i, e.clientReq = some (cid, rid, i) →
      S.reqs.lookup (sint.Z cid, sint.Z rid) = some (k.val, i) ∧
      reqs' = S.reqs.delete (sint.Z cid, sint.Z rid) ∧ rx' = S.rx := by
  intro cid rid i hc
  rcases h with ⟨m, k', n, rfl, -⟩ | ⟨cid', rid', i', hc', h1, h2, h3⟩ | ⟨-, hc', -⟩
  · rw [clientReq_msg] at hc; cases hc
  · rw [hc] at hc'; cases hc'; exact ⟨h1, h2, h3⟩
  · rw [hc] at hc'; cases hc'

theorem tokStep_reqs_sub {S : Inv2St} {k : Fin 3} {e : Ev} {rx' reqs'}
    (h : tokStep S k e rx' reqs') : ∀ id ki, reqs'.lookup id = some ki → S.reqs.lookup id = some ki := by
  intro id ki hl
  rcases h with ⟨-, -, -, -, -, -, rfl⟩ | ⟨cid, rid, i, -, -, rfl, -⟩ | ⟨-, -, -, rfl⟩
  · exact hl
  · rw [GMap.lookup_delete_iff] at hl
    by_cases h : (sint.Z cid, sint.Z rid) = id
    · rw [ite_cond_eq_true _ _ (eq_true h)] at hl; cases hl
    · rw [ite_cond_eq_false _ _ (eq_false h)] at hl; exact hl
  · exact hl

theorem tokStep_rx_sub {S : Inv2St} {k : Fin 3} {e : Ev} {rx' reqs'}
    (h : tokStep S k e rx' reqs') : ∀ x m, rx'.lookup x = some m → S.rx.lookup x = some m := by
  intro x m hl
  rcases h with ⟨-, k', n, -, -, rfl, -⟩ | ⟨-, -, -, -, -, -, rfl⟩ | ⟨-, -, rfl, -⟩
  · rw [GMap.lookup_delete_iff] at hl
    by_cases h : (k'.val, k.val, n) = x
    · rw [ite_cond_eq_true _ _ (eq_true h)] at hl; cases hl
    · rw [ite_cond_eq_false _ _ (eq_false h)] at hl; exact hl
  · exact hl
  · exact hl

theorem prefix_getElem? {α : Type} {l l' : List α} (h : l <+: l') {n : Nat} (hn : n < l.length) :
    l'[n]? = l[n]? := by
  obtain ⟨u, rfl⟩ := h; exact List.getElem?_append_left hn

/-! ## The receive tokens across a step -/

/-- The consumed messages after a step: the streams grow (indices below the cursors keep their
messages), and the consumed token (if any) is added. -/
theorem consumed_step {S : Inv2St} (hf : Inv2Facts S) {k : Fin 3} {e : Ev} {rx' reqs'}
    (htok : tokStep S k e rx' reqs') (T'' : Fin 3 → List Ev)
    (hpre : ∀ k0 q : Fin 3, streamOf k0 q (S.T k0) <+: streamOf k0 q (T'' k0)) (q : Fin 3)
    (m : Msg) :
    (consumedTo T'' S.cur rx' q).count m =
      (consumedTo S.T S.cur S.rx q).count m +
        (if q = k then (recvdR [e]).count m else 0) := by
  rw [consumedTo_count, consumedTo_count]
  -- the streams below the cursors are unchanged
  have hc : ∀ k0 : Fin 3, ∀ n, n < (S.cur.lookup (k0.val, q.val)).getD 0 →
      (streamOf k0 q (T'' k0))[n]? = (streamOf k0 q (S.T k0))[n]? := by
    intro k0 n hn
    obtain ⟨c, hcl, hcle⟩ := hf.curOk k0 q
    rw [hcl] at hn; simp only [Option.getD_some] at hn
    exact prefix_getElem? (hpre k0 q) (by omega)
  rcases htok with ⟨m0, k', n0, rfl, hrx, rfl, -⟩ | ⟨cid, rid, i, hcr, -, -, rfl⟩ | ⟨hr, -, rfl, -⟩
  · -- a message: its token's index is consumed
    obtain ⟨k'', q'', hk, hq, hn0, hm0⟩ := hf.rxOk _ _ _ _ hrx
    have hk2 : k'' = k' := Fin.ext hk
    have hq2 : q'' = k := Fin.ext hq
    subst hk2 hq2
    have hr1 : (recvdR [Ev.msg m0]).count m = ([m0] : List Msg).count m := rfl
    rw [hr1]
    by_cases hqk : q = q''
    · subst hqk
      simp only [↓reduceIte]
      have key : ∀ k0 : Fin 3,
          (pickL (streamOf k0 q (T'' k0)) ((S.cur.lookup (k0.val, q.val)).getD 0)
            (fun n => ((S.rx.delete (k''.val, q.val, n0)).lookup (k0.val, q.val, n)).isNone)).count m =
          (pickL (streamOf k0 q (S.T k0)) ((S.cur.lookup (k0.val, q.val)).getD 0)
            (fun n => (S.rx.lookup (k0.val, q.val, n)).isNone)).count m +
            (if k0 = k'' then ([m0] : List Msg).count m else 0) := by
        intro k0
        by_cases hk0 : k0 = k''
        · subst hk0
          simp only [↓reduceIte]
          have hP : pickL (streamOf k0 q (T'' k0)) ((S.cur.lookup (k0.val, q.val)).getD 0)
              (fun n => ((S.rx.delete (k0.val, q.val, n0)).lookup (k0.val, q.val, n)).isNone) =
              pickL (streamOf k0 q (S.T k0)) ((S.cur.lookup (k0.val, q.val)).getD 0)
              (fun n => (S.rx.lookup (k0.val, q.val, n)).isNone || n == n0) := by
            apply pickL_congr
            intro n hn
            refine ⟨?_, fun _ => hc k0 n hn⟩
            simp only [GMap.lookup_delete_iff, Prod.mk.injEq, true_and]
            by_cases h : n0 = n
            · subst h; simp [hrx]
            · have : (n == n0) = false := by simp [Ne.symm h]
              simp [h, this]
          rw [hP]
          have hd : ∀ j, (S.rx.lookup (k0.val, q.val, j)).isNone = true → (j == n0) = true → False := by
            intro j h1 h2
            simp only [beq_iff_eq] at h2; subst h2
            rw [hrx] at h1; cases h1
          rw [pickL_or_count _ _ _ _ hd m, pickL_single _ _ _ hn0, hm0]
          rfl
        · simp only [hk0, ↓reduceIte, Nat.add_zero]
          congr 1
          apply pickL_congr
          intro n hn
          refine ⟨?_, fun _ => hc k0 n hn⟩
          have : (k''.val, q.val, n0) ≠ (k0.val, q.val, n) := by
            intro h; simp only [Prod.mk.injEq] at h; exact hk0 (Fin.ext h.1.symm)
          simp only [GMap.lookup_delete_iff, this, ↓reduceIte]
      rw [sum3_congr key, sum3_add, sum3_ite]
    · simp only [hqk, ↓reduceIte, Nat.add_zero]
      apply sum3_congr
      intro k0
      congr 1
      apply pickL_congr
      intro n hn
      refine ⟨?_, fun _ => hc k0 n hn⟩
      have : (k''.val, q''.val, n0) ≠ (k0.val, q.val, n) := by
        intro h; simp only [Prod.mk.injEq] at h; exact hqk (Fin.ext h.2.1.symm)
      simp only [GMap.lookup_delete_iff, this, ↓reduceIte]
  · have hr : e.recv = none := recv_of_clientReq hcr
    have hr0 : ∀ m, (recvdR [e]).count m = 0 := by
      intro m; rw [recvdR_single, hr]; rfl
    simp only [hr0, ite_self, Nat.add_zero]
    apply sum3_congr
    intro k0
    congr 1
    exact pickL_congr (fun n hn => ⟨rfl, fun _ => hc k0 n hn⟩)
  · have hr0 : ∀ m, (recvdR [e]).count m = 0 := by
      intro m; rw [recvdR_single, hr]; rfl
    simp only [hr0, ite_self, Nat.add_zero]
    apply sum3_congr
    intro k0
    congr 1
    exact pickL_congr (fun n hn => ⟨rfl, fun _ => hc k0 n hn⟩)

end Perennial.gryff.p2
