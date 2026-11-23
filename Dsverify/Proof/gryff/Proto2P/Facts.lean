/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto2P/Facts.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit I (stage 2 proofs): the invariant's facts across the laws other than the step: a
prediction's registration and record (`pred_register`, `pred_set`), a receive token
(`recv_msg`), a request token (`req_mint`), a registration and its claim (`op_begin`, `op_end`),
a connection's binding and counter (`clientConnAt_intro`, `placeRight_intro`), and the facts the
read-only laws need (`step_ok_msg`, `step_ok_free`).
-/
module

public import Dsverify.Proof.gryff.Proto2P.Lin

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.p2

open model kahn pure dsverify_lab.harness

/-! ## Facts derived from the invariant's -/

theorem lin_nil (l : List Label) : lin l 0 = [] := by
  unfold lin
  have : (ops l).filter (fun o => decide (o.g < 0) && placeLe l o (front l 0)) = [] := by
    apply List.filter_eq_nil_iff.2
    intro o _; simp
  rw [this, List.mergeSort_nil]

/-- The linearized entries are registered operations. -/
theorem linL_registered {S : Inv2St} (hf : Inv2Facts S) :
    ∀ x ∈ S.linL, (S.info.lookup x.1).isSome := by
  intro x hx
  by_cases hu : ∃ k : Fin 3, S.P.lookup k.val = some none
  · rw [(hf.unset hu).2] at hx; exact absurd hx List.not_mem_nil
  · have hset : ∀ k : Fin 3, ∃ ws, S.P.lookup k.val = some (some ws) := by
      intro k
      have h := hf.predKeys k
      rcases hk : S.P.lookup k.val with _ | (_ | ws)
      · rw [hk] at h; cases h
      · exact absurd ⟨k, hk⟩ hu
      · exact ⟨ws, rfl⟩
    let ws : Fin 3 → List w64 := fun k => (hset k).choose
    obtain ⟨-, l2, c, hR, -, hlin⟩ := hf.closure ws (fun k => (hset k).choose_spec)
    rw [hlin] at hx
    unfold linEntries at hx
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx
    obtain ⟨ho1, ho2⟩ := lin_mem_ops ho
    obtain ⟨n, hn, -⟩ := hf.reg o (ops_of_append ho1 ho2)
    show (S.info.lookup o.idZ).isSome
    rw [hn]; rfl

/-- The registered ids number at most 24 (and a fortiori a registration needs a free unit). -/
theorem real_run {S : Inv2St} (hf : Inv2Facts S) :
    ∃ c, GRun (Cfg.init gNet) S.l1 c ∧ ∀ k : Fin 3, runP gNet k (S.T k) = some (c.st k, outsP k (S.T k)) := by
  obtain ⟨c, hc⟩ := hf.run
  exact ⟨c, hc, real_runP hf hc⟩

/-! ## A prediction's registration -/

theorem facts_pred_register {S : Inv2St} (hf : Inv2Facts S) {i n : Nat} {ws : List w64}
    (hi : i < 3) (hP : S.P.lookup i = some none) (hNP : S.NP.lookup n = some (some ws)) :
    Inv2Facts { S with P := S.P.insert i (some ws), idNode := S.idNode.insert i n } := by
  have hu := hf.unset ⟨⟨i, hi⟩, hP⟩
  have hT : ∀ k : Fin 3, S.T k = [] := by
    intro k; rw [← hf.proj k, hu.1]; rfl
  exact {
    run := hf.run
    proj := hf.proj
    predKeys := by
      intro k
      show ((S.P.insert i (some ws)).lookup k.val).isSome
      rw [GMap.lookup_insert_eq_iff]; split
      · rfl
      · exact hf.predKeys k
    predPrefix := by
      intro k ws0 h
      have h' : (S.P.insert i (some ws)).lookup k.val = some (some ws0) := h
      rw [GMap.lookup_insert_eq_iff] at h'
      split at h'
      · cases h'; exact ⟨_, by rw [hT k]; rfl⟩
      · exact hf.predPrefix k ws0 h'
    predNode := by
      intro j ws0 h
      have h' : (S.P.insert i (some ws)).lookup j = some (some ws0) := h
      show ∃ n', (S.idNode.insert i n).lookup j = some n' ∧ S.NP.lookup n' = some (some ws0)
      rw [GMap.lookup_insert_eq_iff] at h' ⊢
      split at h'
      · cases h'; rw [if_pos (by assumption)]; exact ⟨n, rfl, hNP⟩
      · rw [if_neg (by assumption)]; exact hf.predNode j ws0 h'
    unset := fun _ => hu
    closure := by
      intro ws0 _
      have hz : (fun r : Fin 3 => (S.T r).length) = (fun _ => 0) := by
        funext r; rw [hT r]; rfl
      refine ⟨by show Reach (N := gNet) (decodeT ws0) (fun r : Fin 3 => (S.T r).length)
                 rw [hz]; exact Reach.zero, ?_⟩
      have h0 : GRun (Cfg.init gNet) ([] : List Label) (Cfg.init gNet) := .nil _
      obtain ⟨l2, c2, h2, hp2⟩ := reach_extend (T := decodeT ws0) (p := fun _ => 0) h0
        (fun _ => rfl) (close_reach _) (fun _ => Nat.zero_le _)
      obtain ⟨l2, rfl⟩ : ∃ l2' : List Label, l2' = l2 := ⟨l2, rfl⟩
      refine ⟨l2, c2, ?_, ?_, ?_⟩
      · show GRun (Cfg.init gNet) (S.l1 ++ l2) c2
        rw [hu.1]; exact h2
      · intro r
        show projR (S.l1 ++ l2) r = _
        rw [hu.1]; exact hp2 r
      · show S.linL = linEntries (S.l1 ++ l2) S.l1.length
        rw [hu.1, hu.2]; unfold linEntries; rw [List.length_nil, lin_nil]; rfl
    val := hf.val
    wb := hf.wb
    linNodup := hf.linNodup
    reg := hf.reg
    reqReg := hf.reqReg
    reqFresh := hf.reqFresh
    binding := hf.binding
    repSet := hf.repSet
    turnsReg := hf.turnsReg
    turnsIdle := hf.turnsIdle
    turnsBusy := hf.turnsBusy
    order := hf.order
    budgetKeys := hf.budgetKeys
    budgetSpent := hf.budgetSpent
    reqBudget := hf.reqBudget
    curOk := hf.curOk
    rxOk := hf.rxOk
    recvdOk := hf.recvdOk }

/-- A node's prediction recorded. -/
theorem facts_pred_set {S : Inv2St} (hf : Inv2Facts S) {n : Nat} {ws : List w64}
    (hNP : S.NP.lookup n = some none) :
    Inv2Facts { S with NP := S.NP.insert n (some ws) } := by
  exact { hf with
    predNode := by
      intro j ws0 h
      obtain ⟨n', h1, h2⟩ := hf.predNode j ws0 h
      refine ⟨n', h1, ?_⟩
      show (S.NP.insert n (some ws)).lookup n' = some (some ws0)
      rw [GMap.lookup_insert_eq_iff, if_neg]; exact h2
      intro e; subst e; rw [hNP] at h2; cases h2 }

end Perennial.gryff.p2

namespace Perennial.gryff.p2

open model kahn pure dsverify_lab.harness

/-! ## A receive token -/

theorem consumedTo_recv (T : Fin 3 → List Ev) (cur : GMap (Nat × Nat) Nat)
    (rx : GMap (Nat × Nat × Nat) Msg) {k q : Fin 3} {n : Nat} {m : Msg}
    (hcur : cur.lookup (k.val, q.val) = some n) (q0 : Fin 3) :
    consumedTo T (cur.insert (k.val, q.val) (n + 1)) (rx.insert (k.val, q.val, n) m) q0 =
      consumedTo T cur rx q0 := by
  rw [consumedTo_eq, consumedTo_eq]
  congr 1; funext k0
  by_cases h : (k0.val, q0.val) = (k.val, q.val)
  · simp only [Prod.mk.injEq] at h
    have hk : k0 = k := Fin.ext h.1
    have hq : q0 = q := Fin.ext h.2
    subst hk hq
    rw [GMap.lookup_insert_eq_iff, if_pos rfl, hcur]
    simp only [Option.getD_some]
    rw [pickL_succ_false _ _ _ (by simp)]
    apply pickL_congr
    intro j hj
    refine ⟨?_, fun _ => rfl⟩
    have : (k0.val, q0.val, n) ≠ (k0.val, q0.val, j) := by
      intro e; simp only [Prod.mk.injEq] at e; omega
    rw [GMap.lookup_insert_eq_iff, if_neg this]
  · have h1 : (k.val, q.val) ≠ (k0.val, q0.val) := fun e => h e.symm
    rw [GMap.lookup_insert_eq_iff, if_neg h1]
    apply pickL_congr
    intro j _
    refine ⟨?_, fun _ => rfl⟩
    have : (k.val, q.val, n) ≠ (k0.val, q0.val, j) := by
      intro e; simp only [Prod.mk.injEq] at e; exact h1 (by rw [e.1, e.2.1])
    rw [GMap.lookup_insert_eq_iff, if_neg this]

theorem facts_recv {S : Inv2St} (hf : Inv2Facts S) {k q : Fin 3} {n : Nat} {m : Msg}
    (hcur : S.cur.lookup (k.val, q.val) = some n)
    (hm : (streamOf k q (S.T k))[n]? = some m) :
    S.rx.lookup (k.val, q.val, n) = none ∧
      Inv2Facts { S with cur := S.cur.insert (k.val, q.val) (n + 1), rx := S.rx.insert (k.val, q.val, n) m } := by
  have hlt : n < (streamOf k q (S.T k)).length := (List.getElem?_eq_some_iff.1 hm).1
  have hnone : S.rx.lookup (k.val, q.val, n) = none := by
    rcases h : S.rx.lookup (k.val, q.val, n) with _ | m'
    · rfl
    · obtain ⟨-, -, -, -, hn, -⟩ := hf.rxOk _ _ _ _ h
      rw [hcur] at hn; simp at hn
  refine ⟨hnone, { hf with
    curOk := ?_
    rxOk := ?_
    recvdOk := ?_ }⟩
  · intro k0 q0
    show ∃ c, (S.cur.insert (k.val, q.val) (n + 1)).lookup (k0.val, q0.val) = some c ∧ _
    rw [GMap.lookup_insert_eq_iff]
    by_cases h : (k.val, q.val) = (k0.val, q0.val)
    · rw [if_pos h]
      simp only [Prod.mk.injEq] at h
      have hk : k0 = k := Fin.ext h.1.symm
      have hq : q0 = q := Fin.ext h.2.symm
      subst hk hq
      exact ⟨n + 1, rfl, hlt⟩
    · rw [if_neg h]; exact hf.curOk k0 q0
  · intro k1 q1 n1 m1 h
    have h' : (S.rx.insert (k.val, q.val, n) m).lookup (k1, q1, n1) = some m1 := h
    show ∃ (k' q' : Fin 3), k'.val = k1 ∧ q'.val = q1 ∧
      n1 < ((S.cur.insert (k.val, q.val) (n + 1)).lookup (k1, q1)).getD 0 ∧
      (streamOf k' q' (S.T k'))[n1]? = some m1
    rw [GMap.lookup_insert_eq_iff] at h'
    by_cases he : (k.val, q.val, n) = (k1, q1, n1)
    · rw [if_pos he] at h'
      cases h'
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨k, q, rfl, rfl, ?_, hm⟩
      rw [GMap.lookup_insert_eq_iff, if_pos rfl]; simp
    · rw [if_neg he] at h'
      obtain ⟨k', q', hk, hq, hn1, hm1⟩ := hf.rxOk _ _ _ _ h'
      refine ⟨k', q', hk, hq, ?_, hm1⟩
      rw [GMap.lookup_insert_eq_iff]
      by_cases hkq : (k.val, q.val) = (k1, q1)
      · rw [if_pos hkq]
        simp only [Prod.mk.injEq] at hkq
        rw [← hkq.1, ← hkq.2, hcur] at hn1
        simp only [Option.getD_some] at hn1 ⊢
        omega
      · rw [if_neg hkq]; exact hn1
  · intro q0
    show (recvd gNet (S.T q0)).Perm
      (consumedTo S.T (S.cur.insert (k.val, q.val) (n + 1)) (S.rx.insert (k.val, q.val, n) m) q0)
    rw [consumedTo_recv S.T S.cur S.rx hcur q0]
    exact hf.recvdOk q0

/-! ## A request token -/

theorem facts_req_mint {S : Inv2St} (hf : Inv2Facts S) {k : Fin 3} {hs : w32} {conn : Nat}
    {last req : Int} {i : RegInput w64} {nI : OpInfo}
    (hconn : S.conns.lookup hs = some (some conn)) (hpl : S.placers.lookup conn = some last)
    (hlt : last < req) (h0 : 0 ≤ req) (hrep : last < 0 ∨ S.connRep.lookup conn = some k.val)
    (hinfo : S.info.lookup (sint.Z hs, req) = some nI) (hin : nI.input = i) :
    S.reqs.lookup (sint.Z hs, req) = none ∧ (last < 0 → S.connRep.lookup conn = none) ∧
      Inv2Facts { S with placers := S.placers.insert conn req, connRep := S.connRep.insert conn k.val, reqs := S.reqs.insert (sint.Z hs, req) (k.val, i) } := by
  -- the id is above the connection's counter, so neither a token nor handled
  have habove : ∀ k0, ¬ ((∃ i0, S.reqs.lookup (sint.Z hs, req) = some (k0, i0)) ∨
      (∃ o ∈ ops S.l1, o.idZ = (sint.Z hs, req) ∧ o.r.val = k0)) := by
    intro k0 h
    obtain ⟨hs', conn', n', h1, h2, h3, h4, -⟩ := hf.binding _ k0 h
    have : hs' = hs := sintZ_inj h1.symm
    subst this
    rw [hconn] at h2; cases h2
    rw [hpl] at h3; cases h3
    exact absurd h4 (by simp; omega)
  have hnone : S.reqs.lookup (sint.Z hs, req) = none := by
    rcases h : S.reqs.lookup (sint.Z hs, req) with _ | ⟨k0, i0⟩
    · rfl
    · exact absurd (Or.inl ⟨i0, h⟩) (habove k0)
  have hfresh : ∀ o ∈ ops S.l1, o.idZ ≠ (sint.Z hs, req) :=
    fun o ho he => habove o.r.val (Or.inr ⟨o, ho, he, rfl⟩)
  have hrnone : last < 0 → S.connRep.lookup conn = none := by
    intro hl
    rcases h : S.connRep.lookup conn with _ | k0
    · rfl
    · obtain ⟨n, hn, hn0⟩ := hf.repSet conn k0 h
      rw [hpl] at hn; cases hn; omega
  -- the connection's replica id, after
  have hrep' : ∀ k0, S.connRep.lookup conn = some k0 → k0 = k.val := by
    intro k0 h
    rcases hrep with hl | hr
    · rw [hrnone hl] at h; cases h
    · rw [hr] at h; cases h; rfl
  refine ⟨hnone, hrnone, { hf with
    reqReg := ?_
    reqFresh := ?_
    binding := ?_
    repSet := ?_
    reqBudget := ?_ }⟩
  · intro id k0 i0 h
    have h' : (S.reqs.insert (sint.Z hs, req) (k.val, i)).lookup id = some (k0, i0) := h
    rw [GMap.lookup_insert_eq_iff] at h'
    split at h'
    · rename_i hid
      simp only [Option.some.injEq, Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      rw [← hid]; exact ⟨k.isLt, nI, hinfo, hin⟩
    · exact hf.reqReg id k0 i0 h'
  · intro id ki h
    have h' : (S.reqs.insert (sint.Z hs, req) (k.val, i)).lookup id = some ki := h
    rw [GMap.lookup_insert_eq_iff] at h'
    split at h'
    · subst_vars; exact hfresh
    · exact hf.reqFresh id ki h'
  · intro id k0 hor
    show ∃ (hs1 : w32) (conn1 : Nat) (n1 : Int), id.1 = sint.Z hs1 ∧
      S.conns.lookup hs1 = some (some conn1) ∧
      (S.placers.insert conn req).lookup conn1 = some n1 ∧ id.2 ≤ n1 ∧
      (S.connRep.insert conn k.val).lookup conn1 = some k0
    by_cases hid : (sint.Z hs, req) = id
    · subst hid
      rcases hor with ⟨i0, h⟩ | ⟨o, ho, he, -⟩
      · have h' : (S.reqs.insert (sint.Z hs, req) (k.val, i)).lookup (sint.Z hs, req) =
            some (k0, i0) := h
        rw [GMap.lookup_insert_eq_iff, if_pos rfl] at h'
        cases h'
        refine ⟨hs, conn, req, rfl, hconn, ?_, Int.le_refl _, ?_⟩
        · rw [GMap.lookup_insert_eq_iff, if_pos rfl]
        · rw [GMap.lookup_insert_eq_iff, if_pos rfl]
      · exact absurd he (hfresh o ho)
    · have hor' : (∃ i0, S.reqs.lookup id = some (k0, i0)) ∨
          (∃ o ∈ ops S.l1, o.idZ = id ∧ o.r.val = k0) := by
        rcases hor with ⟨i0, h⟩ | h
        · left; refine ⟨i0, ?_⟩
          have h' : (S.reqs.insert (sint.Z hs, req) (k.val, i)).lookup id = some (k0, i0) := h
          rw [GMap.lookup_insert_eq_iff, if_neg hid] at h'; exact h'
        · right; exact h
      obtain ⟨hs1, conn1, n1, h1, h2, h3, h4, h5⟩ := hf.binding id k0 hor'
      by_cases hc : conn = conn1
      · subst hc
        rw [hpl] at h3; cases h3
        refine ⟨hs1, conn, req, h1, h2, by rw [GMap.lookup_insert_eq_iff, if_pos rfl],
          by omega, ?_⟩
        rw [GMap.lookup_insert_eq_iff, if_pos rfl, hrep' k0 h5]
      · refine ⟨hs1, conn1, n1, h1, h2, by rw [GMap.lookup_insert_eq_iff, if_neg hc]; exact h3,
          h4, ?_⟩
        rw [GMap.lookup_insert_eq_iff, if_neg hc]; exact h5
  · intro conn1 k1 h
    show ∃ n, (S.placers.insert conn req).lookup conn1 = some n ∧ 0 ≤ n
    by_cases hc : conn = conn1
    · subst hc; exact ⟨req, by rw [GMap.lookup_insert_eq_iff, if_pos rfl], h0⟩
    · have h' : (S.connRep.insert conn k.val).lookup conn1 = some k1 := h
      rw [GMap.lookup_insert_eq_iff, if_neg hc] at h'
      obtain ⟨n, hn, hn0⟩ := hf.repSet conn1 k1 h'
      exact ⟨n, by rw [GMap.lookup_insert_eq_iff, if_neg hc]; exact hn, hn0⟩
  · intro id k0 i0 h
    have h' : (S.reqs.insert (sint.Z hs, req) (k.val, i)).lookup id = some (k0.val, i0) := h
    rw [GMap.lookup_insert_eq_iff] at h'
    split at h'
    · rename_i hid
      simp only [Option.some.injEq, Prod.mk.injEq] at h'
      have hk0 : k0 = k := Fin.ext h'.1.symm
      subst hk0 hid
      obtain ⟨c, hc⟩ := hf.run
      have hr := (grun_init_acc hc).1 k0
      rw [hf.proj k0] at hr
      show (stOf k0 (S.T k0)).nReqs < 24
      rw [stOf_of_runP hr]
      rw [← hf.proj k0] at hr
      obtain ⟨unit, hu1, hu2⟩ := hf.budgetSpent
      exact reqBudget_of hr hf.wb
        (fun o ho => by obtain ⟨n, hn, -⟩ := hf.reg o ho; rw [hn]; rfl)
        (by rw [hinfo]; rfl) hfresh ⟨unit, fun id h => (hu1 id h).1, hu2⟩
    · exact hf.reqBudget id k0 i0 h'

end Perennial.gryff.p2

namespace Perennial.gryff.p2

open model kahn pure dsverify_lab.harness

/-! ## A registration (`op_begin`) and its claim (`op_end`) -/

theorem facts_op_begin {S : Inv2St} (hf : Inv2Facts S) {cid r req : Int} (hr : r ≤ req)
    (ht : S.turns.lookup cid = some (r, false)) {u : Nat} (hu : S.B.lookup u = some ())
    (n : OpInfo) :
    S.info.lookup (cid, req) = none ∧ (∀ o, ((cid, req), o) ∉ S.linL) ∧
      Inv2Facts { S with info := S.info.insert (cid, req) n, turns := S.turns.insert cid (req + 1, true), B := S.B.delete u } := by
  have hnone : S.info.lookup (cid, req) = none := by
    rcases h : S.info.lookup (cid, req) with _ | n0
    · rfl
    · obtain ⟨n1, b1, h1, h2⟩ := hf.turnsReg (cid, req) (by rw [h]; rfl)
      rw [ht] at h1; cases h1
      simp at h2; omega
  have hnl : ∀ o, ((cid, req), o) ∉ S.linL := by
    intro o ho
    have := linL_registered hf _ ho
    rw [hnone] at this; cases this
  -- lookups of the new registrations
  have hI : ∀ id, (S.info.insert (cid, req) n).lookup id =
      if (cid, req) = id then some n else S.info.lookup id := fun id => rfl
  have hold : ∀ id, (S.info.lookup id).isSome → ((S.info.insert (cid, req) n).lookup id).isSome := by
    intro id h; rw [hI]; split <;> simp_all
  refine ⟨hnone, hnl, { hf with
    reg := ?_
    reqReg := ?_
    turnsReg := ?_
    turnsIdle := ?_
    turnsBusy := ?_
    order := ?_
    budgetKeys := ?_
    budgetSpent := ?_ }⟩
  · intro o ho
    obtain ⟨n0, h1, h2⟩ := hf.reg o ho
    refine ⟨n0, ?_, h2⟩
    show (S.info.insert (cid, req) n).lookup o.idZ = some n0
    rw [hI, if_neg]; exact h1
    intro e; rw [← e, hnone] at h1; cases h1
  · intro id k i h
    obtain ⟨hk, n0, h1, h2⟩ := hf.reqReg id k i h
    refine ⟨hk, n0, ?_, h2⟩
    show (S.info.insert (cid, req) n).lookup id = some n0
    rw [hI, if_neg]; exact h1
    intro e; rw [← e, hnone] at h1; cases h1
  · intro id h
    have h' : ((S.info.insert (cid, req) n).lookup id).isSome := h
    show ∃ n1 b, (S.turns.insert cid (req + 1, true)).lookup id.1 = some (n1, b) ∧ id.2 < n1
    rw [GMap.lookup_insert_eq_iff]
    rw [hI] at h'
    by_cases hid : (cid, req) = id
    · subst hid; exact ⟨req + 1, true, if_pos rfl, by simp only; omega⟩
    · rw [if_neg hid] at h'
      obtain ⟨n1, b1, h1, h2⟩ := hf.turnsReg id h'
      by_cases hc : cid = id.1
      · rw [if_pos hc]
        rw [← hc, ht] at h1; cases h1
        exact ⟨req + 1, true, rfl, by omega⟩
      · rw [if_neg hc]; exact ⟨n1, b1, h1, h2⟩
  · intro c n1 h r1 hr1
    have h' : (S.turns.insert cid (req + 1, true)).lookup c = some (n1, false) := h
    rw [GMap.lookup_insert_eq_iff] at h'
    by_cases hc : cid = c
    · rw [if_pos hc] at h'; cases h'
    · rw [if_neg hc] at h'
      have hr1' : ((S.info.insert (cid, req) n).lookup (c, r1)).isSome := hr1
      rw [hI, if_neg (by intro e; simp only [Prod.mk.injEq] at e; exact hc e.1)] at hr1'
      exact hf.turnsIdle c n1 h' r1 hr1'
  · intro c n1 h r1 hne hr1
    have h' : (S.turns.insert cid (req + 1, true)).lookup c = some (n1, true) := h
    have hr1' : ((S.info.insert (cid, req) n).lookup (c, r1)).isSome := hr1
    rw [GMap.lookup_insert_eq_iff] at h'
    by_cases hc : cid = c
    · rw [if_pos hc] at h'
      simp only [Option.some.injEq, Prod.mk.injEq] at h'
      subst hc
      rw [hI, if_neg (by intro e; simp only [Prod.mk.injEq] at e; omega)] at hr1'
      exact hf.turnsIdle cid r ht r1 hr1'
    · rw [if_neg hc] at h'
      rw [hI, if_neg (by intro e; simp only [Prod.mk.injEq] at e; exact hc e.1)] at hr1'
      exact hf.turnsBusy c n1 h' r1 hne hr1'
  · intro c r1 r2 hlt h1 h2
    have h1' : ((S.info.insert (cid, req) n).lookup (c, r1)).isSome := h1
    have h2' : ((S.info.insert (cid, req) n).lookup (c, r2)).isSome := h2
    rw [hI] at h1' h2'
    by_cases e2 : (cid, req) = (c, r2)
    · simp only [Prod.mk.injEq] at e2
      obtain ⟨rfl, rfl⟩ := e2
      have e1 : (cid, req) ≠ (cid, r1) := by intro e; simp only [Prod.mk.injEq] at e; omega
      rw [if_neg e1] at h1'
      obtain ⟨m, hm⟩ := hf.turnsIdle cid r ht r1 h1'
      refine ⟨m, hm, fun o ho hid => ?_⟩
      obtain ⟨n0, hn0, -⟩ := hf.reg o ho
      rw [hid, hnone] at hn0; cases hn0
    · rw [if_neg e2] at h2'
      by_cases e1 : (cid, req) = (c, r1)
      · simp only [Prod.mk.injEq] at e1
        obtain ⟨rfl, rfl⟩ := e1
        obtain ⟨n1, b1, h3, h4⟩ := hf.turnsReg _ h2'
        rw [ht] at h3; cases h3
        simp at h4; omega
      · rw [if_neg e1] at h1'
        exact hf.order c r1 r2 hlt h1' h2'
  · intro u' h
    have h' : (S.B.delete u).lookup u' = some () ∨ (S.B.delete u).lookup u' = none := by
      cases (S.B.delete u).lookup u' <;> simp
    have h'' : ((S.B.delete u).lookup u').isSome := h
    rw [GMap.lookup_delete_iff] at h''
    split at h''
    · cases h''
    · exact hf.budgetKeys u' h''
  · obtain ⟨unit, hu1, hu2⟩ := hf.budgetSpent
    refine ⟨fun id => if (cid, req) = id then u else unit id, ?_, ?_⟩
    · intro id h
      have h' : ((S.info.insert (cid, req) n).lookup id).isSome := h
      rw [hI] at h'
      show (if (cid, req) = id then u else unit id) < 24 ∧
        (S.B.delete u).lookup (if (cid, req) = id then u else unit id) = none
      split
      · exact ⟨hf.budgetKeys u (by rw [hu]; rfl), by rw [GMap.lookup_delete_iff, if_pos rfl]⟩
      · rename_i hid
        rw [if_neg hid] at h'
        obtain ⟨h1, h2⟩ := hu1 id h'
        refine ⟨h1, ?_⟩
        rw [GMap.lookup_delete_iff]; split
        · rfl
        · exact h2
    · intro id1 id2 h1 h2 he
      have h1' : ((S.info.insert (cid, req) n).lookup id1).isSome := h1
      have h2' : ((S.info.insert (cid, req) n).lookup id2).isSome := h2
      rw [hI] at h1' h2'
      simp only at he
      by_cases e1 : (cid, req) = id1 <;> by_cases e2 : (cid, req) = id2
      · rw [← e1, ← e2]
      · rw [if_pos e1, if_neg e2] at he
        rw [if_neg e2] at h2'
        have := (hu1 id2 h2').2; rw [← he, hu] at this; cases this
      · rw [if_neg e1, if_pos e2] at he
        rw [if_neg e1] at h1'
        have := (hu1 id1 h1').2; rw [he, hu] at this; cases this
      · rw [if_neg e1, if_neg e2] at he
        rw [if_neg e1] at h1'; rw [if_neg e2] at h2'
        exact hu2 id1 id2 h1' h2' he

theorem facts_op_end {S : Inv2St} (hf : Inv2Facts S) {cid req : Int}
    (ht : S.turns.lookup cid = some (req + 1, true)) (hrep : repliedIn S.l1 (cid, req)) :
    Inv2Facts { S with turns := S.turns.insert cid (req + 1, false) } := by
  refine { hf with
    turnsReg := ?_
    turnsIdle := ?_
    turnsBusy := ?_ }
  · intro id h
    obtain ⟨n1, b1, h1, h2⟩ := hf.turnsReg id h
    show ∃ n b, (S.turns.insert cid (req + 1, false)).lookup id.1 = some (n, b) ∧ id.2 < n
    rw [GMap.lookup_insert_eq_iff]
    by_cases hc : cid = id.1
    · rw [if_pos hc]; rw [← hc, ht] at h1; cases h1; exact ⟨_, _, rfl, h2⟩
    · rw [if_neg hc]; exact ⟨n1, b1, h1, h2⟩
  · intro c n1 h r1 hr1
    have h' : (S.turns.insert cid (req + 1, false)).lookup c = some (n1, false) := h
    rw [GMap.lookup_insert_eq_iff] at h'
    by_cases hc : cid = c
    · subst hc
      by_cases hr : r1 = req
      · subst hr; exact hrep
      · exact hf.turnsBusy cid (req + 1) ht r1 (by omega) hr1
    · rw [if_neg hc] at h'; exact hf.turnsIdle c n1 h' r1 hr1
  · intro c n1 h r1 hne hr1
    have h' : (S.turns.insert cid (req + 1, false)).lookup c = some (n1, true) := h
    rw [GMap.lookup_insert_eq_iff] at h'
    by_cases hc : cid = c
    · rw [if_pos hc] at h'; cases h'
    · rw [if_neg hc] at h'; exact hf.turnsBusy c n1 h' r1 hne hr1

/-! ## A connection's binding and counter -/

theorem facts_conn {S : Inv2St} (hf : Inv2Facts S) {hs : w32} {c : Nat}
    (hn : S.conns.lookup hs = some none) :
    Inv2Facts { S with conns := S.conns.insert hs (some c) } := by
  refine { hf with binding := ?_ }
  intro id k h
  obtain ⟨hs1, conn1, n1, h1, h2, h3⟩ := hf.binding id k h
  refine ⟨hs1, conn1, n1, h1, ?_, h3⟩
  show (S.conns.insert hs (some c)).lookup hs1 = some (some conn1)
  rw [GMap.lookup_insert_eq_iff, if_neg]; exact h2
  intro e; subst e; rw [hn] at h2; cases h2

theorem facts_placer {S : Inv2St} (hf : Inv2Facts S) {c : Nat}
    (hn : S.placers.lookup c = none) :
    Inv2Facts { S with placers := S.placers.insert c (-1) } := by
  refine { hf with binding := ?_, repSet := ?_ }
  · intro id k h
    obtain ⟨hs1, conn1, n1, h1, h2, h3, h4, h5⟩ := hf.binding id k h
    refine ⟨hs1, conn1, n1, h1, h2, ?_, h4, h5⟩
    show (S.placers.insert c (-1)).lookup conn1 = some n1
    rw [GMap.lookup_insert_eq_iff, if_neg]; exact h3
    intro e; subst e; rw [hn] at h3; cases h3
  · intro conn1 k h
    obtain ⟨n1, h1, h2⟩ := hf.repSet conn1 k h
    refine ⟨n1, ?_, h2⟩
    show (S.placers.insert c (-1)).lookup conn1 = some n1
    rw [GMap.lookup_insert_eq_iff, if_neg]; exact h1
    intro e; subst e; rw [hn] at h1; cases h1

end Perennial.gryff.p2
