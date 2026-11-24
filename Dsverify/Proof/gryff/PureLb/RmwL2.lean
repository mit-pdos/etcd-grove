/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/RmwL2.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b (RMW side): **an RMW's replies** (`rmw_once`, `rmw_l2'`). A reply to RMW `o` (label `n`)
is the leader's `handleExecuted` on `o`'s instance `rmwInst l o` (`rmw_repX`: the reply's
proposal is the head of the instance's bookkeeping, owned by the RMW that created the instance:
`HOwn`); such replies are not repeated (`rep_new`), and at one two distinct replicas executed the
instance with a result at most their stores (`rep_two`), all executions agreeing (A1's
`exec_same`).
-/
module

public import Dsverify.Proof.gryff.PureLb.ExInv
public import Dsverify.Proof.gryff.PureLb.Once

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

theorem rmwInst_append {l : List Label} {o : Op} (ho : o ∈ ops l) (l2 : List Label) :
    rmwInst (l ++ l2) o = rmwInst l o := by
  unfold rmwInst
  rw [proj_append, List.take_append_of_le_length (op_j_le ho)]

theorem headIn_ow {s : RState} {v : w64} {t : model.Tag} {q i : w32} {p : Proposal}
    (h : HeadIn (s.overwrite v t) q i p) : HeadIn s q i p := by
  obtain ⟨c, lb, hc, h2, h3⟩ := h
  rw [tot.ow_inst] at hc
  exact ⟨c, lb, hc, h2, h3⟩

theorem handleExecuted_head {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) {cid rid : w32} {f : w8}
    (hx : Out.ext (.rmwReply cid rid f) ∈ o) :
    ∃ p, HeadIn s m.replica m.inst p ∧ p.client = cid ∧ p.cmdId = rid := by
  rcases handleExecuted_spec h with ⟨-, rfl⟩ | ⟨c, lb, b, hc, hlb, -, ⟨rfl, -⟩ | ⟨-, -, -, p, hp, rfl⟩⟩
  · cases hx
  · cases hx
  · simp only [List.mem_singleton, Out.ext.injEq, Ext.rmwReply.injEq] at hx
    obtain ⟨rfl, rfl, -⟩ := hx
    exact ⟨p, ⟨c, lb, hc, hlb, hp⟩, rfl, rfl⟩

/-- An RMW reply is the leader's `handleExecuted` on an instance of its row, from the head of the
instance's bookkeeping. -/
theorem rmwReply_hx {l : List Label} {cn : Cfg gNet} {R : Fin 3} {e : Ev} {s' : RState}
    {outs : List Out} (hc : ReplyCtx l cn R e s' outs) {cid rid : w32} {f : w8}
    (hx : Out.ext (.rmwReply cid rid f) ∈ outs) :
    ∃ y p, HX e y ∧ y.1 = rid32 R ∧ HeadIn (stR cn R) y.1 y.2 p ∧ p.client = cid ∧
      p.cmdId = rid := by
  have hAF := af_of hc.run
  have hstep := hc.ok
  cases hm : Ev.mspecial e with
  | false => exact absurd (step_noM hstep hm _ hx) (by simp [isMOut])
  | true =>
    cases e with
    | msg m =>
      cases m with
      | executed m =>
        obtain ⟨p, hp, h1, h2⟩ := handleExecuted_head hstep hx
        exact ⟨(m.replica, m.inst), p, Or.inl ⟨m, rfl, rfl⟩, hAF.ex R m (hc.recv _ rfl), hp, h1, h2⟩
      | executeOverwrite m =>
        rcases stepEO_spec hstep with ⟨hself, hh⟩ | ⟨-, -, d, -, rfl⟩
        · obtain ⟨p, hp, h1, h2⟩ := handleExecuted_head hh hx
          refine ⟨(m.leader, m.slot), p, Or.inr ⟨m, rfl, rfl⟩, ?_, headIn_ow hp, h1, h2⟩
          rw [hself, hAF.id R]
        · simp at hx
      | _ => cases hm
    | _ => cases hm

/-- **A reply to an RMW is its instance's reply** (`RepX`). -/
theorem rmw_repX {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {a b : w64} (hi : o.inp = .cas a b) {n : Nat} (hr : RepliesTo l n o) :
    RepX l n (rmwInst l o) := by
  obtain ⟨e, cn, s', outs, x, hn, hc, houts, -, -, -, ho', hxo, hxk, hfit⟩ := reply_is_own h ho hr
  cases x with
  | readReply => rw [hi] at hfit; exact hfit.elim
  | writeReply => rw [hi] at hfit; exact hfit.elim
  | rmwReply cid rid f =>
  simp only [Ext.key, Prod.mk.injEq] at hxk
  obtain ⟨rfl, rfl⟩ := hxk
  obtain ⟨y, p, hy, hy1, hp, h1, h2⟩ := rmwReply_hx hc hxo
  obtain ⟨o', ho'', hor, -, hoc, hoq, hinst⟩ := hown hc.run o.r y.1 y.2 p hp
  have e' : o' = o := (rinv hc.run).2.1.uniq o' ho'' o ho' hor (hoc.trans h1) (hoq.trans h2)
  subst e'
  have hl : l = l.take n ++ l.drop n := (List.take_append_drop n l).symm
  have hri : rmwInst l o' = y := by
    rw [hl, rmwInst_append ho', hinst]
  rw [hri]
  refine ⟨o'.r, e, hn, hy1, hy, o'.cid, o'.rid, f, ?_⟩
  unfold extsAt extsIn; rw [houts]
  exact List.mem_filterMap.2 ⟨_, hxo, rfl⟩

/-- The configuration before label `n` and the step at `n`. -/
theorem label_step {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {n : Nat}
    {R : Fin 3} {e : Ev} (hn : l[n]? = some (R, e)) :
    ∃ cn c1 xx, GRun (Cfg.init gNet) (l.take n) cn ∧ GStep cn R e c1 xx ∧
      l.take (n + 1) = l.take n ++ [(R, e)] ∧ (l.take n).length = n := by
  obtain ⟨cn, h1, h2, -⟩ := grun_cut h n
  have hlt : n < l.length := (List.getElem?_eq_some_iff.1 hn).1
  have hd : l.drop n = (R, e) :: l.drop (n + 1) := by
    obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 hn
    rw [List.drop_eq_getElem_cons hlt, he]
  obtain ⟨c1, xx, hs, -⟩ := grun_cons_inv (grun_of_eq hd h2)
  refine ⟨cn, c1, xx, h1, hs, ?_, by simp; omega⟩
  rw [List.take_add_one, hn]; rfl

theorem repX_take {l : List Label} {n k : Nat} {x : w32 × w32} (h : RepX l n x) (hk : n < k) :
    RepX (l.take k) n x := by
  have hl : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  have hlt : n < (l.take k).length := by
    have := repX_lt h; simp; omega
  rw [hl] at h
  exact (repX_appL hlt).1 h

/-- **An RMW is replied to at most once.** -/
theorem rmw_once {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {a b : w64} (hi : o.inp = .cas a b) {n n' : Nat}
    (r1 : RepliesTo l n o) (r2 : RepliesTo l n' o) : n = n' := by
  have h1 := rmw_repX h ho hi r1
  have h2 := rmw_repX h ho hi r2
  have key : ∀ {n n' : Nat}, RepX l n (rmwInst l o) → RepX l n' (rmwInst l o) → n < n' → False := by
    intro n n' h1 h2 hlt
    obtain ⟨L, e, hn', -⟩ := id h2
    obtain ⟨cn, c1, xx, hrun, hst, htake, hlen⟩ := label_step h hn'
    have hy : RepX (l.take n' ++ [(L, e)]) (l.take n').length (rmwInst l o) := by
      rw [← htake, hlen]; exact repX_take h2 (Nat.lt_succ_self _)
    exact rep_new hrun hst hy ⟨n, repX_take h1 hlt⟩
  rcases Nat.lt_trichotomy n n' with hlt | heq | hlt
  · exact (key h1 h2 hlt).elim
  · exact heq
  · exact (key h2 h1 hlt).elim

/-- The first execution's tag of an executed instance. -/
theorem execTag_of_mem {r : Fin 3} {es : List Ev} {x : w32 × w32} {vt : ValTag}
    (h : (x, vt) ∈ execSeq r es) :
    ∃ t, execTag r es x = some t ∧ ∃ vt', (x, vt') ∈ execSeq r es ∧ t = vt'.t := by
  obtain ⟨j, hj, hv⟩ := (mem_execSeq' r).1 h
  cases hf : execTag r es x with
  | none =>
    exfalso
    unfold execTag at hf
    have := List.findSome?_eq_none_iff.1 hf j
      (List.mem_range.2 (List.getElem?_eq_some_iff.1 hj).1)
    rw [hj] at this; simp [hv] at this
  | some t =>
    refine ⟨t, rfl, ?_⟩
    unfold execTag at hf
    obtain ⟨j', -, hj'⟩ := List.exists_of_findSome?_eq_some hf
    split at hj'
    · rename_i q i he
      split at hj'
      · rename_i hx
        obtain ⟨vt', hv', rfl⟩ := Option.map_eq_some_iff.1 hj'
        exact ⟨vt', (mem_execSeq' r).2 ⟨j', by rw [he, ← hx], hv'⟩, rfl⟩
      · cases hj'
    · cases hj'

/-- **L2 for RMWs**: a replied RMW is placed, at most the frontier after its reply. -/
theorem rmw_l2' {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {a b : w64} (hi : o.inp = .cas a b) {n : Nat} (hr : RepliesTo l n o) :
    ∃ t, place l o = some t ∧ tagLe t.toP (front l (n + 1)) := by
  have hx := rmw_repX h ho hi hr
  obtain ⟨L, e, hn', hx1, -⟩ := id hx
  generalize hX : rmwInst l o = X at hx hx1
  obtain ⟨q, i⟩ := X
  simp only at hx1; subst hx1
  obtain ⟨c1, h1, h2, h3⟩ := grun_cut h (n + 1)
  have hlt : n < l.length := (List.getElem?_eq_some_iff.1 hn').1
  obtain ⟨r1, r2, vt1, vt2, hne, m1, m2, t1, t2⟩ := rep_two h1 ⟨n, repX_take hx (Nat.lt_succ_self n)⟩
  have hst : ∀ r, stR c1 r = cutSt l (n + 1) r := fun r => by
    obtain ⟨o', h'⟩ := h3 r; exact (stOf_of_runP h').symm
  have hl : ∀ r, projR l r = projR (l.take (n + 1)) r ++ projR (l.drop (n + 1)) r := fun r => by
    rw [← proj_append, List.take_append_drop]
  have f1 : ((rid32 L, i), vt1) ∈ execSeq r1 (projR l r1) := by
    rw [hl]; exact execSeq_append_mem r1 _ m1
  have f2 : ((rid32 L, i), vt2) ∈ execSeq r2 (projR l r2) := by
    rw [hl]; exact execSeq_append_mem r2 _ m2
  have e12 := exec_same h r1 r2 f1 f2
  subst e12
  -- the place
  obtain ⟨t1', ht1, -⟩ := execTag_of_mem f1
  have hpl : ∃ t, rmwPlace l o = some t ∧ t = vt1.t := by
    unfold rmwPlace
    rw [hX]
    cases hf : (List.finRange 3).findSome? (fun r => execTag r (projR l r) (rid32 L, i)) with
    | none =>
      exfalso
      have := List.findSome?_eq_none_iff.1 hf r1 (List.mem_finRange r1)
      rw [ht1] at this; cases this
    | some t =>
      refine ⟨t, rfl, ?_⟩
      obtain ⟨r', -, hr'⟩ := List.exists_of_findSome?_eq_some hf
      obtain ⟨vt', hm', -⟩ : ∃ vt', ((rid32 L, i), vt') ∈ execSeq r' (projR l r') ∧ True := by
        unfold execTag at hr'
        obtain ⟨j', -, hj'⟩ := List.exists_of_findSome?_eq_some hr'
        split at hj'
        · rename_i q0 i0 he
          split at hj'
          · rename_i hx'
            obtain ⟨vt', hv', -⟩ := Option.map_eq_some_iff.1 hj'
            exact ⟨vt', (mem_execSeq' r').2 ⟨j', by rw [he, ← hx'], hv'⟩, trivial⟩
          · cases hj'
        · cases hj'
      obtain ⟨t', ht', vt'', hm'', rfl⟩ := execTag_of_mem hm'
      rw [hr'] at ht'; cases ht'
      rw [exec_same h r' r1 hm'' f1]
  obtain ⟨t, hpt, rfl⟩ := hpl
  refine ⟨vt1.t, by unfold place; rw [hi]; exact hpt, ?_⟩
  rw [hst] at t1 t2
  exact le_front_of_pair hne t1 t2

end Perennial.gryff.pure
